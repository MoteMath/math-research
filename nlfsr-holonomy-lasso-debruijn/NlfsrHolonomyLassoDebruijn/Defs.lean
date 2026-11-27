/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Hybrid Carry-AND NLFSR Holonomy & De Bruijn Engine (`nlfsr-holonomy-lasso-debruijn`)

Pure-`Init` (zero Mathlib) definitions of `iter`, `ExactPeriod`, `SingleCycle`, `BitSlicedInvertible`, `CarryTransducer`, `runTransducer`, `LassoCert`, `cylinderVec`, `checkLasso`, `H111`, `H121`, `F0`, `TwoDelayed`, `hybridCarryNLFSR`, `NonPrefixTap`, `prefixTap`, and `hybridTapNLFSR`.
-/

namespace DynSil12

/-- `n`-fold iteration of a discrete dynamical map `f`. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => f (iter f n x)

/-- Exact minimal period `L` of `x` under `f` modulo `2^w`. -/
def ExactPeriod (f : Nat → Nat) (w x L : Nat) : Prop :=
  L > 0 ∧
  iter f L x % 2 ^ w = x % 2 ^ w ∧
  ∀ t, 0 < t → t < L → iter f t x % 2 ^ w ≠ x % 2 ^ w

/-- Full De Bruijn completeness at width `w`: every state lies on a single cycle of length `2^w`. -/
def SingleCycle (f : Nat → Nat) (w : Nat) : Prop :=
  ∀ x, ExactPeriod f w x (2 ^ w)

/-- Causal (bit-sliced / 1-Lipschitz 2-adic) map: low `w` bits of `f x` depend only on low `w` bits of `x`. -/
def Causal (f : Nat → Nat) : Prop :=
  ∀ w x y, x % 2 ^ w = y % 2 ^ w → f x % 2 ^ w = f y % 2 ^ w

/-- A causal bit-sliced invertible map: bit `w` of `f x` flips `x.testBit w` by `delta w (x % 2^w)`. -/
def BitSlicedInvertible (f : Nat → Nat) (delta : Nat → Nat → Bool) : Prop :=
  Causal f ∧ ∀ w x, (f x).testBit w = xor (x.testBit w) (delta w (x % 2 ^ w))

/-- A finite-state hardware carry-and-tap transducer scanning bits LSB-to-MSB. -/
structure CarryTransducer (S : Nat) where
  init   : Nat
  next   : Nat → Bool → Nat
  toggle : Nat → Bool

def CarryTransducer.Valid {S : Nat} (T : CarryTransducer S) : Prop :=
  T.init < S ∧ ∀ s < S, ∀ b, T.next s b < S

/-- Run the transducer over bits `0 .. w-1` of `x`. -/
def runTransducer {S : Nat} (T : CarryTransducer S) : Nat → Nat → Nat
  | 0, _ => T.init
  | w + 1, x => T.next (runTransducer T w x) (x.testBit w)

/-- F_2-linear transfer step on an `S`-bit state-parity mask `v`. -/
def vecStepAux {S : Nat} (T : CarryTransducer S) (v : Nat) : Nat → Nat
  | 0 => 0
  | s + 1 =>
    let rest := vecStepAux T v s
    if v.testBit s then rest ^^^ (1 <<< T.next s false) ^^^ (1 <<< T.next s true) else rest

def vecStep {S : Nat} (T : CarryTransducer S) (v : Nat) : Nat :=
  vecStepAux T v S

/-- F_2 holonomy readout on an `S`-bit state-parity mask `v`. -/
def vecHolAux {S : Nat} (T : CarryTransducer S) (v : Nat) : Nat → Bool
  | 0 => false
  | s + 1 =>
    let rest := vecHolAux T v s
    if v.testBit s then xor rest (T.toggle s) else rest

def vecHol {S : Nat} (T : CarryTransducer S) (v : Nat) : Bool :=
  vecHolAux T v S

/-- XOR-sum of bitmasks over `0 .. n-1`. -/
def xorMaskRange : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, g => xorMaskRange n g ^^^ g n

/-- State-parity vector of transducer `T` over cylinder `P` at width `w`. -/
def cylinderVec {S : Nat} (T : CarryTransducer S) (P : Nat → Bool) (w0 w : Nat) : Nat :=
  xorMaskRange (2 ^ w) (fun y => if P (y % 2 ^ w0) then 1 <<< runTransducer T w y else 0)

/-- Finite F_2 Lasso Certificate `(pre, cyc)` for infinite-width holonomy verification. -/
structure LassoCert where
  pre : List Nat
  cyc : List Nat

def checkChain (step : Nat → Nat) : List Nat → Nat → Bool
  | [], _ => true
  | v :: vs, expected => (v == expected) && checkChain step vs (step v)

def checkLasso {S : Nat} (T : CarryTransducer S) (v0 : Nat) (cert : LassoCert) : Bool :=
  match cert.cyc with
  | [] => false
  | c0 :: _ =>
    let full := cert.pre ++ cert.cyc
    let last := cert.cyc.getLast!
    checkChain (vecStep T) full v0 &&
    (vecStep T last == c0) &&
    full.all (fun v => vecHol T v)

def H111 (x : Nat) : Nat := x + 2 * (x &&& (x <<< 1)) + 1

def H121 (x : Nat) : Nat := x + 2 * (x &&& (x <<< 2)) + 1

/-- A 2-delayed causal nonlinear feedback `N`:
    bits 0 and 1 vanish identically, and bit `w ≥ 2` depends only on `x % 2^(w - 1)`. -/
def TwoDelayed (N : Nat → Nat) : Prop :=
  (∀ x, (N x).testBit 0 = false ∧ (N x).testBit 1 = false) ∧
  (∀ w x, w ≥ 2 → (N x).testBit w = (N (x % 2 ^ (w - 1))).testBit w)

/-- General Hybrid Carry-AND NLFSR family `F_{N, c}(x) = (x ^^^ (x <<< 1) ^^^ N x) + c`. -/
def hybridCarryNLFSR (N : Nat → Nat) (c : Nat) (x : Nat) : Nat :=
  (x ^^^ (x <<< 1) ^^^ N x) + c

def F0 (x : Nat) : Nat := (x ^^^ (x <<< 1)) + 1

/-- Evaluate a multi-way nonlinear AND tap `T = [s1, ..., sm]` on `x`:
    computes `(x <<< s1) &&& ... &&& (x <<< sm)`. -/
def evalTap : List Nat → Nat → Nat
  | [], _ => 0
  | [s], x => x <<< s
  | s :: rest, x => (x <<< s) &&& evalTap rest x

/-- Evaluate an XOR sum of nonlinear AND taps `M = [T1, ..., Tr]` on `x`. -/
def evalPoly : List (List Nat) → Nat → Nat
  | [], _ => 0
  | T :: rest, x => evalTap T x ^^^ evalPoly rest x

/-- Arbitrary Multi-Way Hybrid XOR-AND-Carry NLFSR `F_{M, c}(x) = (x ^^^ evalPoly M x) + c`. -/
def hybridTapNLFSR (M : List (List Nat)) (c : Nat) (x : Nat) : Nat :=
  (x ^^^ evalPoly M x) + c

/-- A tap set `T` is non-prefix iff it is nonempty, all shifts `s ≥ 1`, and it has a gap
    `1 ≤ g < s_max` with `g ∉ T` (so `T` is NOT a contiguous prefix `{1, 2, ..., d}`)! -/
def NonPrefixTap (T : List Nat) : Prop :=
  T ≠ [] ∧ (∀ s ∈ T, 1 ≤ s) ∧ ∃ g, 1 ≤ g ∧ (∃ s ∈ T, g < s) ∧ g ∉ T

/-- Contiguous prefix tap `P_d = [1, 2, ..., d]`. -/
def prefixTap (d : Nat) : List Nat :=
  (List.range d).map (· + 1)

end DynSil12
