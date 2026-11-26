/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`specdec-wiener-temp-bounds`)

Pure-`Init` (zero Mathlib) definitions over `Rat`, `Int`, and `Nat` for:
- Exact rational absolute value, min/max, integer powers, and `Fin n` sums.
- Logit-MSE under independent additive quantization noise and Wiener-MMSE temperature `T_MMSE`.
- Finite probability distributions, total variation distance, speculative acceptance rate `α(p, q)`,
  and Rényi-2 collision probability `‖p‖_2^2`.
- Speculative decoding expected accepted-token yield, net speedup, discrete marginal benefit,
  and bandwidth-proportional draft cost `c(b) = c_0 · b / 16`.
- Exact rational-base softmax normalization for binary and multi-class rescue witnesses.
-/

namespace SpecDecWienerTemp

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if 0 ≤ x then x else -x

/-- Exact rational minimum. -/
def ratMin (x y : Rat) : Rat :=
  if x ≤ y then x else y

/-- Exact rational maximum. -/
def ratMax (x y : Rat) : Rat :=
  if x ≤ y then y else x

/-- Exact natural-number power of a rational number. -/
def ratPow (x : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => ratPow x n * x

/-- Exact integer power of a positive rational base `r`. -/
def ratZPow (r : Rat) (k : Int) : Rat :=
  if 0 ≤ k then ratPow r k.toNat else (1 : Rat) / ratPow r (-k).toNat

/-- Auxiliary sum over `Fin k`. -/
def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f => finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Sum of `f : Fin n → Rat`. -/
def finSum {n : Nat} (f : Fin n → Rat) : Rat :=
  finSumAux n f

/-! ### Logit MSE and Wiener-MMSE Temperature -/

/-- Exact logit MSE `E[(z̃ / T - z)^2] = (1 - 1/T)^2 σ_z^2 + σ_q^2 / T^2`
    under independent additive quantization noise (`Cov(z, e) = 0`). -/
def logitMSE (sz2 sq2 T : Rat) : Rat :=
  (1 - 1 / T) * (1 - 1 / T) * sz2 + sq2 / (T * T)

/-- Wiener-MMSE optimal draft temperature `T_MMSE^* = 1 + σ_q^2 / σ_z^2`. -/
def wienerTemp (sz2 sq2 : Rat) : Rat :=
  1 + sq2 / sz2

/-- Exact optimal logit MSE achieved at `T_MMSE^*`: `σ_z^2 σ_q^2 / (σ_z^2 + σ_q^2)`. -/
def wienerOptMSE (sz2 sq2 : Rat) : Rat :=
  (sz2 * sq2) / (sz2 + sq2)

/-- General affine logit projection MSE `E[(β z̃ - z)^2] = β^2 s_zt^2 - 2 β c_zzt + s_z^2`
    for arbitrary (possibly attenuating) quantizers such as absmean `Ternary 1.58b`. -/
def generalProjMSE (sz2 szt2 cov beta : Rat) : Rat :=
  beta * beta * szt2 - 2 * beta * cov + sz2

/-- Optimal Wiener-MMSE projection gain `β^* = Cov(z, z̃) / Var(z̃)`. -/
def wienerProjGain (szt2 cov : Rat) : Rat :=
  cov / szt2

/-- Residual MSE of the general Wiener projection: `s_z^2 - Cov(z, z̃)^2 / Var(z̃)`. -/
def wienerProjOptMSE (sz2 szt2 cov : Rat) : Rat :=
  sz2 - (cov * cov) / szt2

/-! ### Probability Distributions, TV Distance, and Speculative Acceptance -/

/-- Predicate asserting `p : Fin n → Rat` is a finite probability distribution. -/
def isProbDist {n : Nat} (p : Fin n → Rat) : Prop :=
  (∀ i : Fin n, 0 ≤ p i) ∧ finSum p = 1

/-- Total variation distance `TV(p, q) = (1/2) ∑_v |p_v - q_v|`. -/
def tvDist {n : Nat} (p q : Fin n → Rat) : Rat :=
  finSum (fun i => ratAbs (p i - q i)) / 2

/-- Speculative decoding token acceptance probability `α(p, q) = ∑_v min(p_v, q_v)`. -/
def acceptRate {n : Nat} (p q : Fin n → Rat) : Rat :=
  finSum (fun i => ratMin (p i) (q i))

/-- Rényi-2 collision probability `‖p‖_2^2 = ∑_v p_v^2`. -/
def renyi2Collision {n : Nat} (p : Fin n → Rat) : Rat :=
  finSum (fun i => p i * p i)

/-- Normalization of non-negative unnormalized weights `w` into a probability vector. -/
def normProb {n : Nat} (w : Fin n → Rat) : Fin n → Rat :=
  fun i => w i / finSum w

/-! ### Speculative Decoding Yield, Speedup, and Bandwidth Cost -/

/-- Exact expected accepted tokens per speculative cycle `Y(α, γ) = ∑_{k=0}^{γ} α^k`. -/
def specYieldSum (α : Rat) (γ : Nat) : Rat :=
  finSum (fun k : Fin (γ + 1) => ratPow α k.val)

/-- Closed-form geometric yield `(1 - α^{γ+1}) / (1 - α)` (valid for `α ≠ 1`). -/
def specYieldClosed (α : Rat) (γ : Nat) : Rat :=
  (1 - ratPow α (γ + 1)) / (1 - α)

/-- Exact net speculative decoding speedup `S(α, γ, c) = Y(α, γ) / (1 + γ c)`. -/
def specSpeedup (α : Rat) (γ : Nat) (c : Rat) : Rat :=
  specYieldSum α γ / (1 + (γ : Rat) * c)

/-- Closed-form net speedup `(1 - α^{γ+1}) / ((1 - α)(1 + γ c))`. -/
def specSpeedupClosed (α : Rat) (γ : Nat) (c : Rat) : Rat :=
  (1 - ratPow α (γ + 1)) / ((1 - α) * (1 + (γ : Rat) * c))

/-- Discrete marginal-benefit numerator `M(α, γ, c) = α^{γ+1}(1 + γ c) - c · Y(α, γ)`. -/
def specMargin (α : Rat) (γ : Nat) (c : Rat) : Rat :=
  ratPow α (γ + 1) * (1 + (γ : Rat) * c) - c * specYieldSum α γ

/-- Bandwidth-proportional draft cost `c(b) = c_0 · b / 16` relative to a `BF16` (`b = 16`) target. -/
def draftCost (c0 b : Rat) : Rat :=
  c0 * b / 16

/-! ### Exact Rational-Base Softmax for Temperature Rescue Witnesses -/

/-- Exact rational-base softmax `softmax_r(z)_i = r^{z_i} / ∑_j r^{z_j}` for integer logits `z`. -/
def ratSoftmax {n : Nat} (r : Rat) (z : Fin n → Int) : Fin n → Rat :=
  normProb (fun i => ratZPow r (z i))

/-- Binary rational-base softmax `(r^z / (r^z + 1), 1 / (r^z + 1))` for integer logit margin `z`. -/
def binRatSoftmax (r : Rat) (z : Int) : Fin 2 → Rat :=
  ratSoftmax r (fun i => if i.val = 0 then z else 0)

/-- Three-class rational-base softmax for integer logit triple `(z0, z1, z2)`. -/
def triRatSoftmax (r : Rat) (z0 z1 z2 : Int) : Fin 3 → Rat :=
  ratSoftmax r (fun i => if i.val = 0 then z0 else if i.val = 1 then z1 else z2)

/-- Signal distribution for exact rescue witness: `z ∈ {-4, +4}` with weights `(1/2, 1/2)`. -/
def sigVal : Fin 2 → Int
  | ⟨0, _⟩ => -4
  | ⟨1, _⟩ => 4

def sigProb : Fin 2 → Rat
  | ⟨0, _⟩ => 1 / 2
  | ⟨1, _⟩ => 1 / 2

/-- Independent noise distribution: `e ∈ {-8, 0, +8}` with weights `(3/8, 1/4, 3/8)`. -/
def noiseVal : Fin 3 → Int
  | ⟨0, _⟩ => -8
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 8

def noiseProb : Fin 3 → Rat
  | ⟨0, _⟩ => 3 / 8
  | ⟨1, _⟩ => 1 / 4
  | ⟨2, _⟩ => 3 / 8

/-- Expected binary rational-base softmax acceptance over the 6-state `(z, e)` ensemble
    at integer temperature divisor `T_div ∈ {1, 2, 4}`. -/
def expectedBinAccept (r : Rat) (T_div : Int) : Rat :=
  finSum (fun i : Fin 2 =>
    sigProb i * finSum (fun j : Fin 3 =>
      noiseProb j * acceptRate
        (binRatSoftmax r (sigVal i))
        (binRatSoftmax r ((sigVal i + noiseVal j) / T_div))))

/-- Expected 3-class rational-base softmax acceptance over the 6-state `(z, e)` ensemble
    with zero-mean logits `(z, -z, 0)` and noise `(e, -e, 0)` at divisor `T_div ∈ {1, 2, 4}`. -/
def expectedTriAccept (r : Rat) (T_div : Int) : Rat :=
  finSum (fun i : Fin 2 =>
    sigProb i * finSum (fun j : Fin 3 =>
      noiseProb j * acceptRate
        (triRatSoftmax r (sigVal i) (-sigVal i) 0)
        (triRatSoftmax r ((sigVal i + noiseVal j) / T_div)
                         ((-(sigVal i + noiseVal j)) / T_div) 0)))

end SpecDecWienerTemp
