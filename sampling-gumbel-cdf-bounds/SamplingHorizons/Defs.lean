/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Pure-`Init` Definitions for `sampling-gumbel-cdf-bounds`

Zero Mathlib, zero `native_decide`, zero floating-point approximations.
All objects are exact over `Nat`, `Int`, and `Rat`.
-/

namespace SamplingHorizons

/-! ### Exact Dyadic Powers, Absolute Value, Min/Max, and Finite Sums -/

/-- Exact dyadic power `2^k` in `Rat`. -/
def pow2Rat (k : Nat) : Rat :=
  ((2 ^ k : Nat) : Rat)

/-- Exact inverse dyadic power `2^{-k} = 1 / 2^k` in `Rat`. -/
def invPow2Rat (k : Nat) : Rat :=
  (1 : Rat) / pow2Rat k

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then x else -x

/-- Exact rational minimum. -/
def ratMin (a b : Rat) : Rat :=
  if a ≤ b then a else b

/-- Exact rational maximum. -/
def ratMax (a b : Rat) : Rat :=
  if a ≤ b then b else a

/-- Exact integer minimum. -/
def intMin (a b : Int) : Int :=
  if a ≤ b then a else b

/-- Exact integer maximum. -/
def intMax (a b : Int) : Int :=
  if a ≤ b then b else a

/-- Recursive sum over `Fin k → Rat`. -/
def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f => finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum `∑_{j : Fin n} f j` over `Rat`. -/
def finSum {n : Nat} (f : Fin n → Rat) : Rat :=
  finSumAux n f

/-- Recursive sum over `Fin k → Int`. -/
def finSumIntAux : (k : Nat) → (Fin k → Int) → Int
  | 0, _ => 0
  | k + 1, f => finSumIntAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum `∑_{j : Fin n} f j` over `Int`. -/
def finSumInt {n : Nat} (f : Fin n → Int) : Int :=
  finSumIntAux n f

/-- Recursive sum over `Fin k → Nat`. -/
def finSumNatAux : (k : Nat) → (Fin k → Nat) → Nat
  | 0, _ => 0
  | k + 1, f => finSumNatAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum `∑_{j : Fin n} f j` over `Nat`. -/
def finSumNat {n : Nat} (f : Fin n → Nat) : Nat :=
  finSumNatAux n f

/-- Exact total variation distance `(1/2) * ∑_i |p_i - q_i|` over `Rat`. -/
def tvDist {n : Nat} (p q : Fin n → Rat) : Rat :=
  (1 / 2 : Rat) * finSum (fun i => ratAbs (p i - q i))

/-! ### Exact IEEE-754 Round-to-Nearest-Even (RNE) Grid Predicate -/

/-- Exact IEEE-754 Round-to-Nearest-Even (RNE) condition on a uniform dyadic grid
    with spacing `u = ulp`: `x` rounds to grid point `k * u` iff `|x - k * u| < u / 2`,
    or `|x - k * u| = u / 2` and `k` is even (tie-to-even). -/
def rneRoundsToGrid (u : Rat) (k : Nat) (x : Rat) : Prop :=
  ratAbs (x - (k : Rat) * u) < u / 2 ∨ (ratAbs (x - (k : Rat) * u) = u / 2 ∧ k % 2 = 0)

/-! ### Pillar 1: Gumbel-Max Finite-Bit RNG Horizon Definitions -/

/-- The `b`-bit uniform RNG grid value `u(r) ∈ {2^{-b}, ..., 1 - 2^{-b}}` for `r : Fin (2^b)`,
    clamping `r = 0` to `2^{-b}` (preventing `log(0)` as in production samplers). -/
def uniformGridVal (b : Nat) (r : Fin (2 ^ b)) : Rat :=
  (if r.val = 0 then (1 : Rat) else (r.val : Rat)) * invPow2Rat b

/-- Predicate (as `Bool`) that token 2 wins or ties token 1 in Gumbel-Max argmax. -/
def gumbelToken2Wins (G : Rat → Rat) (z1 z2 u1 u2 : Rat) : Bool :=
  decide (z1 + G u1 ≤ z2 + G u2)

/-- Exact count of RNG pairs `(r1, r2) ∈ Fin (2^b) × Fin (2^b)` where token 2 wins or ties. -/
def gumbelWinCount2 (b : Nat) (G : Rat → Rat) (z1 z2 : Rat) : Nat :=
  finSumNat (fun r1 : Fin (2 ^ b) =>
    finSumNat (fun r2 : Fin (2 ^ b) =>
      if gumbelToken2Wins G z1 z2 (uniformGridVal b r1) (uniformGridVal b r2) then 1 else 0))

/-- Exact rational win probability of token 2 over all `2^(2b)` uniform RNG pairs. -/
def gumbelWinProb2 (b : Nat) (G : Rat → Rat) (z1 z2 : Rat) : Rat :=
  (gumbelWinCount2 b G z1 z2 : Rat) / (pow2Rat b * pow2Rat b)

/-- Factorial on `Nat`. -/
def natFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * natFact n

/-- Natural power on `Rat`. -/
def ratPow (x : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => ratPow x n * x

/-- Truncated exponential Taylor sum `∑_{k=0}^{N} x^k / k!`, an exact rational strict
    lower bound on `exp(x)` for all `x > 0`. -/
def expLower : Nat → Rat → Rat
  | 0, _ => 1
  | n + 1, x => expLower n x + ratPow x (n + 1) / ((natFact (n + 1) : Nat) : Rat)

/-! ### Pillar 2: Speculative Decoding Definitions -/

/-- Exact positive residual `max(0, p_v - q_v)`. -/
def specDecRes {n : Nat} (p q : Fin n → Rat) (v : Fin n) : Rat :=
  ratMax 0 (p v - q v)

/-- Exact total residual mass `Z = ∑_v max(0, p_v - q_v)`. -/
def specDecZ {n : Nat} (p q : Fin n → Rat) : Rat :=
  finSum (specDecRes p q)

/-- Exact acceptance probability `β = ∑_v min(p_v, q_v)`. -/
def specDecAcceptProb {n : Nat} (p q : Fin n → Rat) : Rat :=
  finSum (fun v => ratMin (p v) (q v))

/-- Exact rational speculative decoding output probability for token `v`. -/
def specDecOut {n : Nat} (p q : Fin n → Rat) (v : Fin n) : Rat :=
  let Z := specDecZ p q
  if Z = 0 then
    ratMin (p v) (q v)
  else
    ratMin (p v) (q v) + (1 - specDecAcceptProb p q) * (specDecRes p q v / Z)

/-- Finite-precision residual sum `Z_fl = ∑_v max(0, fl(p_v) - fl(q_v))`. -/
def specDecFlZ {n : Nat} (fl : Rat → Rat) (p q : Fin n → Rat) : Rat :=
  finSum (fun v => ratMax 0 (fl (p v) - fl (q v)))

/-- Unnormalized accepted-only mass when residual normalization crashes (`Z_fl = 0`). -/
def specDecCrashedUnnorm {n : Nat} (p q : Fin n → Rat) (v : Fin n) : Rat :=
  ratMin (p v) (q v)

/-- Fallback speculative decoding distribution putting all rejected mass `1 - β` onto
    a single fallback token `v0` when `Z_fl = 0` prevents residual normalization. -/
def specDecFallbackDist {n : Nat} (p q : Fin n → Rat) (v0 : Fin n) (v : Fin n) : Rat :=
  ratMin (p v) (q v) + if v = v0 then (1 - specDecAcceptProb p q) else 0

/-- Exact `Q_B` fixed-point denominator `D = 2^B` in `Int`. -/
def qDenom (B : Nat) : Int :=
  ((2 ^ B : Nat) : Int)

/-- Exact integer residual `max(0, P_v - Q_v)`. -/
def specDecIntRes {n : Nat} (P Q : Fin n → Int) (v : Fin n) : Int :=
  intMax 0 (P v - Q v)

/-- Exact integer total residual mass `Z_int = ∑_v max(0, P_v - Q_v)`. -/
def specDecIntZ {n : Nat} (P Q : Fin n → Int) : Int :=
  finSumInt (specDecIntRes P Q)

/-- Exact integer total acceptance mass `β_int = ∑_v min(P_v, Q_v)`. -/
def specDecIntAccept {n : Nat} (P Q : Fin n → Int) : Int :=
  finSumInt (fun v => intMin (P v) (Q v))

/-- Exact rational probability induced by a `Q_B` integer table `P`. -/
def qToRat (B : Nat) {n : Nat} (P : Fin n → Int) (v : Fin n) : Rat :=
  (P v : Rat) / pow2Rat B

/-- Exact division-free `Q_B` integer cross-multiplication acceptance test:
    `u * Q_v < P_v * 2^B`. -/
def qAcceptTest (B : Nat) (u Pv Qv : Int) : Prop :=
  u * Qv < Pv * qDenom B

/-! ### Pillar 3: Descending Inverse-CDF Swamping & Fenwick Binary Tree Definitions -/

/-- Exact IEEE-754 RNE swamping cutoff at prefix sum `S ∈ [1/2, 1)` (`e = -1`):
    `half-ulp(S) = 2^{-(m+2)}`. -/
def swampCutoffHalf (m : Nat) : Rat :=
  invPow2Rat (m + 2)

/-- Exact IEEE-754 RNE swamping cutoff at prefix sum `S ∈ [1/4, 1/2)` (`e = -2`):
    `half-ulp(S) = 2^{-(m+3)}`. -/
def swampCutoffQuarter (m : Nat) : Rat :=
  invPow2Rat (m + 3)

/-- Sequential left-to-right CDF accumulation with an addition operator `add`,
    starting from initial prefix `S0`. -/
def seqCdfAux (add : Rat → Rat → Rat) (S0 : Rat) : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => S0
  | k + 1, p => add (seqCdfAux add S0 k (fun j => p ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
                    (p ⟨k, Nat.lt_succ_self k⟩)

/-- Final sequential CDF value after accumulating all `n` probabilities from `S0`. -/
def seqCdf (add : Rat → Rat → Rat) (S0 : Rat) {n : Nat} (p : Fin n → Rat) : Rat :=
  seqCdfAux add S0 n p

/-- Predicate that a rational number is an exact dyadic power of two `2^a * 2^{-b}`. -/
def isDyadicPow2 (x : Rat) : Prop :=
  ∃ (a b : Nat), x = pow2Rat a * invPow2Rat b

/-- Balanced binary-tree / Fenwick pairwise sum of `2^k` equal terms `t`
    using addition operator `add`. -/
def pairwiseTreeSum (add : Rat → Rat → Rat) : Nat → Rat → Rat
  | 0, t => t
  | k + 1, t => add (pairwiseTreeSum add k t) (pairwiseTreeSum add k t)

end SamplingHorizons
