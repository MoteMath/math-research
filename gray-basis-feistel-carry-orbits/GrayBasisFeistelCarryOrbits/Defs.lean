/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Gray-Basis & Feistel-Carry Orbit Dichotomies (`gray-basis-feistel-carry-orbits`)

Pure-`Init` (zero Mathlib) definitions of `iter`, `HasMinPeriod`, `IsSingleCycle`, `phi`, `gray`, `invGray`, `GrayInvolutionSpec`, `grayInvMap`, `compiledDefect`, `applyBitPerm`, `bitrevFin`, `feistelCarry`, and `feistelZeroLen`.
-/

namespace SiliconOrbitEngine

def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => iter f k (f x)

/-- Exact minimal period of `x` under `f`. -/
def HasMinPeriod {α : Type} (f : α → α) (x : α) (p : Nat) : Prop :=
  0 < p ∧ iter f p x = x ∧ ∀ k, 0 < k → k < p → iter f k x ≠ x

/-- Full-period Hamiltonian single cycle on `BitVec w`:
    `0#w` has exact minimal period `2^w`, and its orbit visits every `x : BitVec w`. -/
def IsSingleCycle (w : Nat) (f : BitVec w → BitVec w) : Prop :=
  HasMinPeriod f 0#w (2 ^ w) ∧ ∀ x : BitVec w, ∃ k, k < 2 ^ w ∧ iter f k 0#w = x

/-- Core XOR-carry map: `phi n γ v = (v ^^^ γ) + 1#n`. -/
def phi (n : Nat) (γ v : BitVec n) : BitVec n :=
  (v ^^^ γ) + 1#n

/-- Number of trailing 1-bits of `g` within width `n` (equals `min n (v_2 (g + 1))`). -/
def trailingOnesNat : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, g => if g % 2 = 1 then 1 + trailingOnesNat n (g / 2) else 0

def trailingOnes {n : Nat} (γ : BitVec n) : Nat :=
  trailingOnesNat n γ.toNat

def gray {w : Nat} (x : BitVec w) : BitVec w :=
  x ^^^ (x >>> 1)

def invGrayAux {w : Nat} : Nat → BitVec w → BitVec w
  | 0, _ => 0#w
  | k + 1, y => y ^^^ invGrayAux k (y >>> 1)

def invGray {w : Nat} (y : BitVec w) : BitVec w :=
  invGrayAux w y

def xorRange (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | k + 1 => xor (xorRange f k) (f k)

def parityVec {w : Nat} (y : BitVec w) : Bool :=
  xorRange (fun i => y.getLsbD i) w

/-- The general Gray-basis involution + carry-increment + XOR-mask dynamical system. -/
def grayInvMap {w : Nat} (P : BitVec w → BitVec w) (δ : BitVec w) (x : BitVec w) : BitVec w :=
  (invGray (P (gray x)) + 1#w) ^^^ δ

/-- Reusable finite-signature specification for Compiler A:
    ANY parity-preserving involution `P` on `BitVec (n+1)` that satisfies single-coset
    equivariance `P (y ^^^ (1 ^^^ gray δ)) = P y ^^^ m` compiles to `phi n γ`! -/
structure GrayInvolutionSpec {n : Nat}
    (P : BitVec (n + 1) → BitVec (n + 1)) (δ m : BitVec (n + 1)) : Prop where
  involutive : ∀ y, P (P y) = y
  parity_pres : ∀ y, parityVec (P y) = parityVec y
  delta_even : δ.toNat % 2 = 0
  coset_equiv : ∀ y, P (y ^^^ (1#(n + 1) ^^^ gray δ)) = P y ^^^ m

/-- The compiled `n`-bit defect signature `γ(P, δ)` of Compiler A. -/
def compiledDefect {n : Nat} (δ m : BitVec (n + 1)) : BitVec n :=
  BitVec.ofNat n ((invGray m ^^^ δ).toNat / 2)

def ofBitsNat (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * ofBitsNat (fun i => b (i + 1)) k + if b 0 then 1 else 0

/-- Arbitrary bit-permutation operator `π : Fin w → Fin w` on `BitVec w`. -/
def applyBitPerm (w : Nat) (π : Fin w → Fin w) (x : BitVec w) : BitVec w :=
  BitVec.ofNat w (ofBitsNat (fun i => if h : i < w then x.getLsbD (π ⟨i, h⟩).val else false) w)

/-- Bit-reversal index involution on `Fin w`. -/
def bitrevFin (w : Nat) (i : Fin w) : Fin w :=
  ⟨w - 1 - i.val, by omega⟩

/-- Pack high `m`-bit word `a` and low `k`-bit word `b` into `BitVec (m + k)`. -/
def pack (m k : Nat) (a : BitVec m) (b : BitVec k) : BitVec (m + k) :=
  BitVec.ofNat (m + k) (a.toNat * 2 ^ k + b.toNat)

/-- General Feistel-Carry dynamical system on `BitVec (m + k)`:
    XOR the low `k`-bit lane by `h(hi)`, then apply full-width carry-increment `+ 1`. -/
def feistelCarry (m k : Nat) (h : BitVec m → BitVec k) (x : BitVec (m + k)) : BitVec (m + k) :=
  let a : BitVec m := BitVec.ofNat m (x.toNat / 2 ^ k)
  let b : BitVec k := BitVec.ofNat k (x.toNat % 2 ^ k)
  pack m k a (b ^^^ h a) + 1#(m + k)

def fiberLen (k : Nat) (g : BitVec k) : Nat :=
  2 ^ (k - trailingOnes g)

/-- Cumulative prefix sum of fiber lengths across `r` fibers `0, ..., r - 1`. -/
def fiberPrefixSum (m k : Nat) (h : BitVec m → BitVec k) : Nat → Nat
  | 0 => 0
  | r + 1 => fiberPrefixSum m k h r + fiberLen k (h (BitVec.ofNat m r))

/-- Total length of the spliced giant zero-orbit of `feistelCarry m k h`. -/
def feistelZeroLen (m k : Nat) (h : BitVec m → BitVec k) : Nat :=
  fiberPrefixSum m k h (2 ^ m)

end SiliconOrbitEngine
