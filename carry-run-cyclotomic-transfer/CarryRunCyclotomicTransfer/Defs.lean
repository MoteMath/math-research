/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`CarryRunCyclotomicTransfer`)

All definitions and helper lemmas needed to state the headline theorems.
-/

namespace SiliconCarryTransfer

-- ============================================================================
-- SECTION 1: Exact Finite Integer Sums, Vectors, Linear Operators & Powers
-- ============================================================================

def sumNat : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumNat n f + f n

def iterOp {α : Type} (F : α → α) : Nat → α → α
  | 0, x => x
  | w + 1, x => F (iterOp F w x)

-- ============================================================================
-- SECTION 3: Concrete Radix-B Addition, Popcount, Ripple Depth & Carry Runs
-- ============================================================================

/-- Exact parity sign `(-1)^n ∈ {-1, +1}`. -/
def paritySign (n : Nat) : Int :=
  if n % 2 = 0 then 1 else -1

/-- Sum of the lowest `w` base-`B` digits of `n` (for `B = 2`, exact `w`-bit `popcount`). -/
def digitSum (B : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, n => n % B + digitSum B w (n / B)

/-- Exact binary `w`-bit popcount (Hamming weight of low `w` bits). -/
abbrev popcount (w n : Nat) : Nat := digitSum 2 w n

/-- Concrete carry-bit run-length tracker (state `cur` = current consecutive carry-1 run length).
    Returns `true` iff every carry run during `w` base-`B` digits has length `≤ L`. -/
def carryRunBounded (B L : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, cur, _, _ => cur ≤ L
  | w + 1, cur, x, y =>
    let cin := if cur = 0 then 0 else 1
    let cout := (x % B + y % B + cin) / B
    let nextCur := if cout = 0 then 0 else cur + 1
    decide (nextCur ≤ L) && carryRunBounded B L w nextCur (x / B) (y / B)

/-- Concrete carry-run bound predicate on `(x, y)` from zero incoming carry (`cur = 0`). -/
def maxCarryRunLe (B L w x y : Nat) : Bool :=
  carryRunBounded B L w 0 x y

/-- Concrete ripple-carry propagation depth tracker (state `cur` = current active dependency chain).
    Generate (`xi + yi ≥ B`) resets dependency depth to `1`; Propagate extends `cur` to `cur + 1`;
    Kill/absorb resets to `0`. Returns `true` iff ripple depth stays `≤ L` at every bit. -/
def rippleDepthBounded (B L : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, cur, _, _ => cur ≤ L
  | w + 1, cur, x, y =>
    let xi := x % B
    let yi := y % B
    let cin := if cur = 0 then 0 else 1
    let cout := (xi + yi + cin) / B
    let nextCur :=
      if cout = 0 then 0
      else if xi + yi ≥ B then 1
      else cur + 1
    decide (nextCur ≤ L) && rippleDepthBounded B L w nextCur (x / B) (y / B)

/-- Concrete ripple-carry propagation depth predicate on `(x, y)` from zero incoming carry. -/
def maxRippleDepthLe (B L w x y : Nat) : Bool :=
  rippleDepthBounded B L w 0 x y

/-- Concrete count of carry absorptions (`c_i = 1` and `c_{i+1} = 0`) over `w` base-`B` digits. -/
def carryAbsorptionsFrom (B : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | w + 1, cin, x, y =>
    let cout := (x % B + y % B + cin) / B
    let absorbed := if cin = 1 ∧ cout = 0 then 1 else 0
    absorbed + carryAbsorptionsFrom B w cout (x / B) (y / B)

/-- Concrete count of carry absorptions in `w`-digit base-`B` addition `x + y`. -/
def carryAbsorptions (B w x y : Nat) : Nat :=
  carryAbsorptionsFrom B w 0 x y

-- ============================================================================
-- SECTION 5: Universal Parametric Transfer Operators & Exact Matrix Annihilators
-- ============================================================================

/-- General 3-parameter `(L+1) × (L+1)` ripple-carry transfer operator `M_rip(L; k, p, g)`. -/
def rippleOp (L : Nat) (k p g : Int) (v : Nat → Int) : Nat → Int :=
  fun i =>
    if i = 0 then k * sumNat (L + 1) v + p * v 0
    else if i = 1 then g * sumNat (L + 1) v
    else if i ≤ L then p * v (i - 1)
    else 0

-- ----------------------------------------------------------------------------
-- General 4-parameter `(L+1) × (L+1)` Carry-Run Transfer Operator `M_run(L; a, b, c, r)`
-- ----------------------------------------------------------------------------

/-- General 4-parameter `(L+1) × (L+1)` carry-bit run-length transfer operator `M_run(L; a, b, c, r)`. -/
def runOp (L : Nat) (a b c r : Int) (v : Nat → Int) : Nat → Int :=
  fun i =>
    if i = 0 then a * v 0 + c * sumNat L (fun j => v (j + 1))
    else if i = 1 then b * v 0
    else if i ≤ L then r * v (i - 1)
    else 0

/-- Convenience definition for the absorption-weighted binary carry-run Thue–Morse sum `A_L(t, w)`. -/
def carryRunAbsSum (t : Int) (L w : Nat) : Int :=
  sumNat (2 ^ w) (fun x => sumNat (2 ^ w) (fun y =>
    if maxCarryRunLe 2 L w x y then
      paritySign (popcount w ((x + y) % 2 ^ w)) * t ^ carryAbsorptions 2 w x y
    else 0))

end SiliconCarryTransfer
