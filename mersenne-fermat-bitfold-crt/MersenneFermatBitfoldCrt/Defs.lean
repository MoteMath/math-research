/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`mersenne-fermat-bitfold-crt`)

Bit-folding programs, symbolic envelope compiler, Mersenne and Fermat thresholds, carry conservation, dyadic Fermat-Mersenne tower and CRT idempotents.
-/

namespace BitFoldEngine


-- ============================================================================
-- Section 3: Exact Parametric Carry-Absorption Thresholds & Attractor Dichotomy
-- ============================================================================

/-- Unsigned Mersenne `k`-bit fold on `Nat`. -/
def foldM (k n : Nat) : Nat := n % 2 ^ k + n / 2 ^ k

def iterFoldM (k : Nat) : Nat → Nat → Nat
  | 0, n => n
  | r + 1, n => iterFoldM k r (foldM k n)

/-- Canonical non-zero-absorbing Mersenne fixed point (`0 ↦ 0`, `n > 0 ↦ ((n-1) % (2^k - 1)) + 1`). -/
def canonM (k n : Nat) : Nat :=
  if n = 0 then 0 else ((n - 1) % (2 ^ k - 1)) + 1

-- ----------------------------------------------------------------------------
-- Signed Fermat Fold: Exact Asymmetric Envelope, Dual-End Sharpness & 2-Cycle
-- ----------------------------------------------------------------------------

/-- Signed Euclidean Fermat `k`-bit fold on `Int`. -/
def foldF (k : Nat) (x : Int) : Int :=
  x % (2 : Int) ^ k - x / (2 : Int) ^ k

def iterFoldF (k : Nat) : Nat → Int → Int
  | 0, x => x
  | r + 1, x => iterFoldF k r (foldF k x)

-- ============================================================================
-- Section 4: Schedule-Invariant Total-Carry Conservation Law
-- ============================================================================

/-- Binary Hamming weight (popcount) defined directly from bits. -/
def popcount (n : Nat) : Nat :=
  if h : n = 0 then 0
  else n % 2 + popcount (n / 2)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- Pure-silicon ripple-carry adder counting EVERY binary carry bit generated in `a + b + c`. -/
def carryCountAux (a b c : Nat) : Nat :=
  if h : a = 0 ∧ b = 0 ∧ c = 0 then 0
  else
    let s := a % 2 + b % 2 + c
    s / 2 + carryCountAux (a / 2) (b / 2) (s / 2)
termination_by a + b + c
decreasing_by
  have : a / 2 + b / 2 + (a % 2 + b % 2 + c) / 2 < a + b + c := by omega
  exact this

def carryCount (a b : Nat) : Nat := carryCountAux a b 0

/-- Multi-level Mersenne folding schedule on `Nat`, returning final value and exact carry sum. -/
def evalNatMersenne (k : Nat) : List Nat → Nat → Nat
  | [], n => n
  | m :: ms, n => evalNatMersenne k ms (n % 2 ^ (m * k) + n / 2 ^ (m * k))

def carryNatMersenne (k : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | m :: ms, n =>
    let lo := n % 2 ^ (m * k)
    let hi := n / 2 ^ (m * k)
    carryCount lo hi + carryNatMersenne k ms (lo + hi)

-- ============================================================================
-- Section 5: Recursive Dyadic Fermat–Mersenne Tower, Rademacher CRT Idempotents
--            & Pure-Silicon Bit-Folding Butterfly Isomorphism
-- ============================================================================

def towerMod (d k : Nat) : Nat := 2 ^ (2 ^ d * k) - 1

def fermatFactor (j k : Nat) : Nat := 2 ^ (2 ^ j * k) + 1

def fermatProd : Nat → Nat → Nat
  | 0, _ => 1
  | d + 1, k => fermatProd d k * fermatFactor d k

-- ----------------------------------------------------------------------------
-- Pure-Silicon Cyclic Right Rotation `rotR`
-- ----------------------------------------------------------------------------

def rotR (W x s : Nat) : Nat := x / 2 ^ s + (x % 2 ^ s) * 2 ^ (W - s)

-- ----------------------------------------------------------------------------
-- Periodic Comb & Rademacher Square-Wave Bitmasks
-- ----------------------------------------------------------------------------

/-- Geometric bit-comb `geoSum step count = ∑_{i < count} 2^(i * step)`. -/
def geoSum (step : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => 1 + 2 ^ step * geoSum step c

-- ----------------------------------------------------------------------------
-- Explicit Rademacher CRT Idempotents `idemM` & `idemF`
-- ----------------------------------------------------------------------------

def mersenneComb (d k : Nat) : Nat := geoSum k (2 ^ d)

def rademacherHiWave (d k j : Nat) : Nat :=
  ((2 ^ (2 ^ j * k) - 1) * 2 ^ (2 ^ j * k)) * geoSum (2 ^ (j + 1) * k) (2 ^ (d - 1 - j))

def idemM (d k : Nat) : Nat := rotR (2 ^ d * k) (mersenneComb d k) d

def idemF (d k j : Nat) : Nat := rotR (2 ^ d * k) (rademacherHiWave d k j) (d - j)

/-- Sum of all Fermat idempotents `∑_{j < m} idemF d k j`. -/
def sumIdemF (d k : Nat) : Nat → Int
  | 0 => 0
  | m + 1 => sumIdemF d k m + (idemF d k m : Int)

-- ----------------------------------------------------------------------------
-- Pure-Silicon Dyadic Bit-Folding Tree ↔ Butterfly Reconstruction Isomorphism
-- ----------------------------------------------------------------------------

/-- Top-down dyadic bit-folding tree splitting `x` into `(r_M, [r_{F,0}, ..., r_{F,d-1}])`. -/
def dyadicFoldTree : Nat → Nat → Int → Int × List Int
  | 0, _, x => (x, [])
  | d + 1, k, x =>
    let w : Int := (2 : Int) ^ (2 ^ d * k)
    let (rM, fs) := dyadicFoldTree d k (x % w + x / w)
    (rM, fs ++ [x % w - x / w])

/-- Single-level pure-silicon CRT butterfly lifting `(a mod 2^w - 1, b mod 2^w + 1)`
    to `mod 2^(2w) - 1` using ONLY `+`, `-`, and bit-shifts `2^w`, `2^(w-1)`! -/
def butterflyLift (w : Nat) (a b : Int) : Int :=
  (2 : Int) ^ (w - 1) * ((a + b) * (2 : Int) ^ w + (a - b))

/-- Bottom-up dyadic butterfly reconstruction inverting `dyadicFoldTree` mod `2^(2^d * k) - 1`. -/
def dyadicButterflyRecon : Nat → Nat → Int × List Int → Int
  | 0, _, (rM, _) => rM
  | d + 1, k, (rM, fs) =>
    let a := dyadicButterflyRecon d k (rM, fs.take d)
    let b := fs.getD d 0
    butterflyLift (2 ^ d * k) a b

end BitFoldEngine
