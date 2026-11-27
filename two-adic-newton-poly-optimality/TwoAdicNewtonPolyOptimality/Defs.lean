/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`two-adic-newton-poly-optimality`)

2-adic valuation algebra, affine contraction certificates, Newton reciprocal and inverse-square-root iterations, polynomial and circuit optimality.
-/

namespace AdicNewtonOptimality


-- ============================================================================
-- SECTION 1: Pure-Silicon 2-Adic Valuation Algebra, Popcount & Legendre's Law
-- ============================================================================

def OddInt (z : Int) : Prop := z % 2 ≠ 0

def DivPow2 (z : Int) (m : Nat) : Prop := ((2 : Int) ^ m) ∣ z

def ExactVal2 (z : Int) (m : Nat) : Prop :=
  ∃ u : Int, OddInt u ∧ z = u * (2 : Int) ^ m

-- Binary popcount s_2(n)
def popcount : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)
termination_by n => n

-- Factorial & Legendre's exact 2-adic valuation formula: v_2(n!) = n - popcount(n)
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

-- ============================================================================
-- SECTION 2: Reusable Infinite Proof Mechanism — AffineContractionEngine
-- ============================================================================

def iterateStep (step : Int → Int → Int) (a x0 : Int) : Nat → Int
  | 0 => x0
  | k + 1 => step a (iterateStep step a x0 k)

def orbitVal (d s m0 : Nat) : Nat → Nat
  | 0 => m0
  | k + 1 => d * orbitVal d s m0 k - s

/--
  Finite single-step algebraic certificate for a 2-adic valuation-affine lift operator.
  Once a lift operator `step` with residual `res` proves ONE finite single-step valuation
  contraction `v_2(res a (step a x)) = d * m - s`, the engine automatically discharges:
    (1) Exact error-bit-count formula valid ∀ k ≥ 0
    (2) Closed-form integer affine valuation law ∀ k ≥ 0
    (3) Sharp minimal-step optimality (necessary & sufficient step count) ∀ k ≥ 0, ∀ N ≥ 1
-/
structure AffineContractionCert where
  step : Int → Int → Int
  res : Int → Int → Int
  valid : Int → Prop
  d : Nat
  s : Nat
  mCrit : Nat
  hd : 2 ≤ d
  hsuper : s < (d - 1) * mCrit
  step_exact : ∀ a x m, valid a → mCrit ≤ m → ExactVal2 (res a x) m →
    ExactVal2 (res a (step a x)) (d * m - s)
  step_div : ∀ a x m, valid a → mCrit ≤ m → DivPow2 (res a x) m →
    DivPow2 (res a (step a x)) (d * m - s)

-- ============================================================================
-- SECTION 3: Pillar 2A — Parametric Order-d Reciprocal Engine (d ≥ 2),
--            Dumas Bitwise XOR Seed, and Hardware Bit-Masked mod 2^(2^k) Lifts
-- ============================================================================

def geomSum (e : Int) : Nat → Int
  | 0 => 0
  | d + 1 => 1 + e * geomSum e d

/-- Pure-integer order-d Newton-Hensel reciprocal lift (d=2 quadratic, d=3 cubic, d=4 quartic, ...). -/
def recipStep (d : Nat) (a x : Int) : Int :=
  x * geomSum (1 - a * x) d

/-- Dumas silicon bitwise XOR seed: (3*a) ^^^ 2 achieves 5 exact bits for all odd a : Nat. -/
def dumasSeedNat (a : Nat) : Nat := (3 * a) ^^^ 2

-- ============================================================================
-- SECTION 4: Pillar 2B — Ramified 2-Adic Inverse Square Root Lifts (S2, S3, S4),
--            Cubic Popcount Super-Gain, m0=3 Resonance Bonus, S4 = S2^2 Val,
--            and m0=2 Boundary Stalling Falsification
-- ============================================================================

def invSqrtS2 (a x : Int) : Int :=
  (x * (3 - a * x * x)) / 2

def invSqrtS3 (a x : Int) : Int :=
  let e := 1 - a * x * x
  (x * (8 + 4 * e + 3 * e * e)) / 8

def invSqrtS4 (a x : Int) : Int :=
  let e := 1 - a * x * x
  (x * (16 + 8 * e + 6 * e * e + 5 * e * e * e)) / 16

-- ============================================================================
-- Polynomial Evaluation, Alternating Forward Differences & Vanishing Theorem
-- ============================================================================

def evalPoly : List Int → Int → Int
  | [], _ => 0
  | c :: cs, a => c + a * evalPoly cs a

-- ============================================================================
-- Universal Arithmetic-Circuit Multiplicative-Depth Optimality Engine
-- ============================================================================

/-- Pure-integer straight-line arithmetic circuit over {input, const, +, -, *}. -/
inductive PolyCircuit where
  | input : PolyCircuit
  | const : Int → PolyCircuit
  | add : PolyCircuit → PolyCircuit → PolyCircuit
  | sub : PolyCircuit → PolyCircuit → PolyCircuit
  | mul : PolyCircuit → PolyCircuit → PolyCircuit

def evalCircuit : PolyCircuit → Int → Int
  | .input, a => a
  | .const c, _ => c
  | .add l r, a => evalCircuit l a + evalCircuit r a
  | .sub l r, a => evalCircuit l a - evalCircuit r a
  | .mul l r, a => evalCircuit l a * evalCircuit r a

def mulDepth : PolyCircuit → Nat
  | .input => 0
  | .const _ => 0
  | .add l r => max (mulDepth l) (mulDepth r)
  | .sub l r => max (mulDepth l) (mulDepth r)
  | .mul l r => max (mulDepth l) (mulDepth r) + 1

end AdicNewtonOptimality
