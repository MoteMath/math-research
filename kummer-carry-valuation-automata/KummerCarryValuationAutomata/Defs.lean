/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Kummer Carry-Valuation Automata (`kummer-carry-valuation-automata`)

Pure-`Init` (zero Mathlib) definitions: factorial, binomial and trinomial coefficients, popcount, 2-adic valuation `v2`, Gray code, and the sharpness family `fam55`.
-/

namespace CVAEngine

def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

def trinom (a b c : Nat) : Nat :=
  binom (a + b + c) a * binom (b + c) b

def popcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n => n % 2 + popcountAux fuel (n / 2)

def popcount (n : Nat) : Nat := popcountAux n n

def v2Aux : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n => if n % 2 = 1 then 0 else 1 + v2Aux fuel (n / 2)

def v2 (n : Nat) : Nat := v2Aux n n

def fromBits : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * fromBits bs

def repeatBits (cyc : List Bool) : Nat → List Bool
  | 0 => []
  | m + 1 => cyc ++ repeatBits cyc m

def pumpBits (pref cyc suff : List Bool) (m : Nat) : Nat :=
  fromBits (pref ++ repeatBits cyc m ++ suff)

def gray (n : Nat) : Nat := n ^^^ (n / 2)

def cyc55 : List Bool :=
  [false, true, false, true, false, false, true, false, false, false, false, false, true]

def suff55 : List Bool :=
  [false, true, false, true, false, false, true]

def fam55 (m : Nat) : Nat :=
  2 * pumpBits cyc55 cyc55 suff55 m + 1

end CVAEngine
