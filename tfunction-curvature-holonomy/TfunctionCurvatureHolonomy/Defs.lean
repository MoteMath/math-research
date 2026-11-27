/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for T-Function Curvature-Holonomy Lifting (`tfunction-curvature-holonomy`)

Pure-`Init` (zero Mathlib) definitions: orbit iteration `iter`, Lipschitz predicates, `IsSingleCycle`, unit slice derivative, bit-slice holonomy, curvature sum, carry mask, the hybrid family `hybridH` and the d-run family `runT`.
-/

namespace SiliconTFunc

def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => f (iter f n x)

def IsOneLipschitz (f : Nat → Nat) : Prop :=
  ∀ w x y, x % 2 ^ w = y % 2 ^ w → f x % 2 ^ w = f y % 2 ^ w

structure IsSingleCycle (f : Nat → Nat) (w : Nat) : Prop where
  period : iter f (2 ^ w) 0 % 2 ^ w = 0
  distinct : ∀ i j, i < 2 ^ w → j < 2 ^ w →
    iter f i 0 % 2 ^ w = iter f j 0 % 2 ^ w → i = j

def HasUnitSliceDeriv (f : Nat → Nat) (w : Nat) : Prop :=
  ∀ r < 2 ^ w, f (r + 2 ^ w) % 2 ^ (w + 1) = (f r + 2 ^ w) % 2 ^ (w + 1)

def bitXorSum (g : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => xor (bitXorSum g n) (g n)

def holonomy (f : Nat → Nat) (w : Nat) : Bool :=
  bitXorSum (fun r => (f r).testBit w) (2 ^ w)

def intSum (g : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => intSum g n + g n

def curvatureSum (f : Nat → Nat) (w : Nat) : Int :=
  intSum (fun r => (f (r + 2 ^ w) : Int) - (f r : Int) - (2 ^ w : Int)) (2 ^ w)

def carryMask (x : Nat) : Nat := x ^^^ (x + 1)

def runD : Nat → Nat → Nat
  | 0, _ => 0
  | 1, x => x
  | d + 2, x => runD (d + 1) x &&& (x <<< (d + 1))

def hybridBase (a b C : Nat) (x : Nat) : Nat :=
  x + (((a * x * x) ^^^ (2 * runD 2 x) ^^^ (2 * b * runD 3 x)) ||| C)

def hybridH (a b C k : Nat) (x : Nat) : Nat :=
  hybridBase a b C x ^^^ (2 * k * carryMask x)

def runT (d C : Nat) (x : Nat) : Nat :=
  x + ((2 * runD d x) ||| C)

end SiliconTFunc
