/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`muonclip-adamw-sr-bounds`)

Pure-`Init` (zero Mathlib) exact rational definitions for:
1. MuonClip Frobenius weight-distortion objective, quartic stationarity polynomial,
   RTN overshoot and RTZ undershoot factors, and linearized asymmetric quadratic objective.
2. `m`-bit IEEE-754 binary floating-point Round-to-Nearest-Even (`RNE`) decoupled
   weight-decay freeze/decay predicates and exact critical radii.
3. 2-state Stochastic Rounding EMA (`SR-EMA`) Markov chain transition probabilities,
   stationary distribution, mean, variance, second eigenvalue, and autocorrelation
   variance inflation factor.
4. Low-bit second-moment preconditioner Jensen bias factors for unbiased stochastic
   rounding of `1/√v`, `√v`, and `v`.
-/

namespace MuonclipAdamwSr

/-! ### 0. Exact Dyadic Powers of Two -/

/-- Exact rational power of two `2^k`. -/
def pow2Rat (k : Nat) : Rat := ((2 ^ k : Nat) : Rat)

/-- Exact rational inverse power of two `2^{-k}`. -/
def invPow2Rat (k : Nat) : Rat := 1 / pow2Rat k

/-! ### 1. MuonClip Objective, Pitchfork Quartic, and Scale-Quantization Bounds -/

/-- MuonClip total squared Frobenius weight perturbation
    `L(A, B, γ, x) = A(1 - x)^2 + B(1 - γ/x)^2`, where `x = γ^α ∈ [γ, 1]`. -/
def muonclipObj (A B γ x : Rat) : Rat :=
  A * (1 - x) * (1 - x) + B * (1 - γ / x) * (1 - γ / x)

/-- Exact stationarity quartic `r x^4 - r x^3 + γ x - γ^2` (with `r = A / B`),
    satisfying `L'(x) = (2 B / x^3) * muonclipQuartic (A / B) γ x`. -/
def muonclipQuartic (r γ x : Rat) : Rat :=
  r * (x * x * x * x) - r * (x * x * x) + γ * x - γ * γ

/-- Second derivative of the symmetric MuonClip objective (`A = B`) evaluated at
    the symmetric split `x = s = √γ`: `L''(s) = 4 A (2 - 1 / s)`. -/
def muonclipSecondDerivSym (A s : Rat) : Rat :=
  4 * A * (2 - 1 / s)

/-- Small-clipping (`γ = 1 - ε → 1⁻`) leading-order quadratic objective
    `L_quad(A, B, α) = A α^2 + B (1 - α)^2`. -/
def muonclipQuadApprox (A B α : Rat) : Rat :=
  A * α * α + B * (1 - α) * (1 - α)

/-- Worst-case multiplicative logit-cap overshoot factor `(1 + 2^{-(m+1)})^2` under
    `m`-bit IEEE-754 RTN quantization of `(s_Q, s_K)`. -/
def rtnOvershootFactor (m : Nat) : Rat :=
  (1 + invPow2Rat (m + 1)) * (1 + invPow2Rat (m + 1))

/-- Worst-case multiplicative logit-cap undershoot factor `(1 - 2^{-m})^2` under
    `m`-bit RTZ (round-toward-zero) quantization of `(s_Q, s_K)`. -/
def rtzUndershootFactor (m : Nat) : Rat :=
  (1 - invPow2Rat m) * (1 - invPow2Rat m)

/-! ### 2. `m`-Bit IEEE-754 RNE AdamW Weight-Decay Freeze Radii -/

/-- Normal binary floating-point value `(2^m + f) / 2^m ∈ [1, 2)` in binade `e = 0`
    (scale-invariant across all normal binades `2^e`). -/
def binadeFloat (m f : Nat) : Rat :=
  ((2 ^ m + f : Nat) : Rat) / pow2Rat m

/-- Exact downward midpoint between `binadeFloat m f` and its immediate lower
    floating-point neighbor in `m`-bit binary floating point. -/
def wdLowerMidpoint (m f : Nat) : Rat :=
  if f = 0 then
    1 - invPow2Rat (m + 2)
  else
    ((2 * (2 ^ m + f) - 1 : Nat) : Rat) / pow2Rat (m + 1)

/-- IEEE-754 Round-to-Nearest-Even (`RNE`) weight-decay freeze predicate:
    `binadeFloat m f * (1 - ρ)` rounds back to `binadeFloat m f` (tie-to-even). -/
def wdFrozenRNE (m f : Nat) (ρ : Rat) : Prop :=
  let y := binadeFloat m f * (1 - ρ)
  if f % 2 = 0 then wdLowerMidpoint m f ≤ y else wdLowerMidpoint m f < y

/-- IEEE-754 `RNE` strict weight-decay predicate: `binadeFloat m f * (1 - ρ)`
    strictly rounds down below `binadeFloat m f`. -/
def wdDecaysRNE (m f : Nat) (ρ : Rat) : Prop :=
  ¬ wdFrozenRNE m f ρ

/-- Exact total weight-decay freeze radius `2^{-(m+2)}`. -/
def wdTotalFreezeRadius (m : Nat) : Rat :=
  invPow2Rat (m + 2)

/-- Exact supremum of the power-of-2-only decay gap `1 / (2^{m+2} - 2)`. -/
def wdInteriorFreezeSup (m : Nat) : Rat :=
  1 / ((2 ^ (m + 2) - 2 : Nat) : Rat)

/-- Exact universal decay threshold `1 / (2^{m+1} + 2)`. -/
def wdUniversalDecayThreshold (m : Nat) : Rat :=
  1 / ((2 ^ (m + 1) + 2 : Nat) : Rat)

/-! ### 3. 2-State SR-EMA Markov Chain -/

/-- Upward transition probability `p_{0 → 1} = (1 - β) r / Δ`. -/
def srEmaP01 (β r Δ : Rat) : Rat := (1 - β) * r / Δ

/-- Downward transition probability `p_{1 → 0} = (1 - β) (Δ - r) / Δ`. -/
def srEmaP10 (β r Δ : Rat) : Rat := (1 - β) * (Δ - r) / Δ

/-- Stationary probability of lower state `l`: `π_0 = 1 - r / Δ`. -/
def srEmaPi0 (r Δ : Rat) : Rat := 1 - r / Δ

/-- Stationary probability of upper state `l + Δ`: `π_1 = r / Δ`. -/
def srEmaPi1 (r Δ : Rat) : Rat := r / Δ

/-- Stationary expectation `E_π[q_∞] = π_0 l + π_1 (l + Δ)`. -/
def srEmaMean (l Δ r : Rat) : Rat :=
  srEmaPi0 r Δ * l + srEmaPi1 r Δ * (l + Δ)

/-- Stationary variance `Var_π(q_∞) = π_0 (l - (l + r))^2 + π_1 ((l + Δ) - (l + r))^2`. -/
def srEmaVar (l Δ r : Rat) : Rat :=
  srEmaPi0 r Δ * (l - (l + r)) * (l - (l + r)) +
  srEmaPi1 r Δ * ((l + Δ) - (l + r)) * ((l + Δ) - (l + r))

/-- Second eigenvalue `λ_2 = trace(P) - 1 = (1 - p_{0→1}) + (1 - p_{1→0}) - 1`. -/
def srEmaLambda2 (β r Δ : Rat) : Rat :=
  (1 - srEmaP01 β r Δ) + (1 - srEmaP10 β r Δ) - 1

/-- Asymptotic time-average variance inflation factor `(1 + β) / (1 - β)`. -/
def srEmaVarInflation (β : Rat) : Rat :=
  (1 + β) / (1 - β)

/-! ### 4. Preconditioner Jensen Bias Factors -/

/-- Exact expectation of unbiased stochastic rounding of `s ∈ [a, b]` onto `{a, b}`. -/
def srDirectExpect (a b s : Rat) : Rat :=
  ((b - s) / (b - a)) * a + ((s - a) / (b - a)) * b

/-- Preconditioner Jensen bias factor when unbiased SR is applied to `p = √v ∈ [1, r_p]`
    at relative position `t ∈ [0, 1]`: `J_sqrt(r_p, t) = (1 + t(r_p - 1))(1 - t + t/r_p)`. -/
def jensenSqrtFactor (r_p t : Rat) : Rat :=
  (1 + t * (r_p - 1)) * (1 - t + t / r_p)

/-- Exact worst-case Jensen bias factor `(r_p + 1)^2 / (4 r_p)` for SR of `√v` on `[1, r_p]`. -/
def jensenSqrtMax (r_p : Rat) : Rat :=
  (r_p + 1) * (r_p + 1) / (4 * r_p)

/-- Squared preconditioner Jensen bias factor when unbiased SR is applied to `v ∈ [1, r^2]`
    at relative position `t ∈ [0, 1]`: `J_v(r, t)^2 = (1 + t(r^2 - 1))(1 - t + t/r)^2`. -/
def jensenVSq (r t : Rat) : Rat :=
  (1 + t * (r * r - 1)) * (1 - t + t / r) * (1 - t + t / r)

/-- Exact worst-case relative position `t*(r) = (r + 2) / (3 (r + 1))` maximizing `J_v(r, t)`. -/
def jensenVOptT (r : Rat) : Rat :=
  (r + 2) / (3 * (r + 1))

/-- Exact closed-form squared worst-case Jensen bias factor
    `J_max(r)^2 = 4 (r^2 + r + 1)^3 / (27 r^2 (r + 1)^2)` for SR of `v` on `[1, r^2]`. -/
def jensenVMaxSq (r : Rat) : Rat :=
  4 * (r * r + r + 1) * (r * r + r + 1) * (r * r + r + 1) /
    (27 * r * r * (r + 1) * (r + 1))

end MuonclipAdamwSr
