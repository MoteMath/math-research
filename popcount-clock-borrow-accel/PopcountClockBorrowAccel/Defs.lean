/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Popcount Clock and Borrow Acceleration (`popcount-clock-borrow-accel`)

Pure-`Init` (zero Mathlib) definitions: popcount, orbit iteration, the XOR flow `T_xor`, the unit potential `V_unit`, the borrow flow `T_sub` with potential `phi`, and the wrapped modular flows `F_xor_wrap`, `F_sub_wrap`, `F_add_dual_wrap`.
-/

namespace Dynsil11

/-- Iteration helper (`f^[n] x`). -/
def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iter f n (f x)

/-- Structurally recursive binary bit-length (reduces cleanly in `decide`!). -/
def bitLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else bitLenAux fuel (n / 2) + 1

def bitLen (n : Nat) : Nat := bitLenAux n n

/-- Population count of bits strictly below `B`. -/
def popcountBelow (x : Nat) : Nat → Nat
  | 0 => 0
  | B + 1 => popcountBelow x B + if x.testBit B then 1 else 0

/-- Arbitrary-weight sum `∑_{i < B} μ(i) * x_i`. -/
def weightSumBelow (μ : Nat → Int) (x : Nat) : Nat → Int
  | 0 => 0
  | B + 1 => weightSumBelow μ x B + if x.testBit B then μ B else 0

/-- Canonical width-independent binary population count `s_2(x)`. -/
def popcount (x : Nat) : Nat := popcountBelow x (bitLen x)

/-- Canonical width-independent weighted bit-moment `∑_{i ≥ 0} μ(i) * x_i`. -/
def weightSum (μ : Nat → Int) (x : Nat) : Int := weightSumBelow μ x (bitLen x)

/-- First bit-index moment `∑_{i ≥ 0} i * x_i`. -/
def indexSum (x : Nat) : Int := weightSum (fun i => (i : Int)) x

/-- Binary inversion energy (Young-diagram area):
    `phi(x) = ∑ i * x_i - s_2(x) * (s_2(x) - 1) / 2` (in `Int`, proven ≥ 0). -/
def phi (x : Nat) : Int :=
  indexSum x - ((popcount x * (popcount x - 1)) / 2 : Nat)

/-- Canonical carry-free popcount-pointer flow on `Nat`: `T_xor x = x ^^^ 2^(s_2 x)`. -/
def T_xor (x : Nat) : Nat := x ^^^ 2 ^ popcount x

/-- Canonical unit-clock potential `V(x) = 2 * indexSum(x) - s_2(x)^2 = 2 * phi(x) - s_2(x)`. -/
def V_unit (x : Nat) : Int := 2 * indexSum x - (popcount x : Int) * (popcount x : Int)

/-- Structurally recursive trailing zero count (`ctzPos 0 = 0`, reduces cleanly in `decide`). -/
def ctzPosAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n = 0 then 0
    else if n % 2 = 1 then 0
    else ctzPosAux fuel (n / 2) + 1

def ctzPos (n : Nat) : Nat := ctzPosAux n n

/-- Borrow-coupled popcount-pointer flow `T_sub x = x - 2^(s_2 x)` on `Nat`. -/
def T_sub (x : Nat) : Nat := x - 2 ^ popcount x

def F_xor_wrap (w : Nat) (x : Nat) : Nat := x ^^^ 2 ^ (popcount x % w)

/-- Borrow-coupled modular flow on `[0, 2^w)`: `(x - 2^(popcount x % w)) mod 2^w`. -/
def F_sub_wrap (w : Nat) (x : Nat) : Nat :=
  (x + 2 ^ w - 2 ^ (popcount x % w)) % 2 ^ w

/-- Bitwise complement on `w`-bit words: `comp w x = (2^w - 1) - x`. -/
def comp (w x : Nat) : Nat := (2 ^ w - 1) - x

/-- Carry-synchronized zero-count modular flow: `(x + 2^((w - s_2(x)) % w)) % 2^w`. -/
def F_add_dual_wrap (w x : Nat) : Nat :=
  (x + 2 ^ ((w - popcount x) % w)) % 2 ^ w

end Dynsil11
