/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Pure-`Init` Definitions for `rag-popcnt-matryoshka-bounds`

Zero Mathlib, zero floating-point approximations, zero `native_decide`.
All definitions operate purely over `Bool`, `Nat`, `Int`, `Rat`, and `Fin d`.
-/

namespace RagPopcntMatryoshka

/-! ## Finite sums and absolute values -/

def ratAbs (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then x else -x

def intAbs (x : Int) : Int :=
  if (0 : Int) ≤ x then x else -x

def finSumNat : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => finSumNat (fun i : Fin n => f i.castSucc) + f (Fin.last n)

def finSumInt : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => finSumInt (fun i : Fin n => f i.castSucc) + f (Fin.last n)

def finSumRat : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => finSumRat (fun i : Fin n => f i.castSucc) + f (Fin.last n)

def leftBlock {α : Type} {a b : Nat} (f : Fin (a + b) → α) : Fin a → α :=
  fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩

def rightBlock {α : Type} {a b : Nat} (f : Fin (a + b) → α) : Fin b → α :=
  fun i => f ⟨a + i.val, Nat.add_lt_add_left i.isLt a⟩

/-! ## Pillar 1A: 1-Bit, 1.58-Bit Ternary, and 2-Bit 2-Bitplane POPCNT Inner Products -/

def bipolar (b : Bool) : Int :=
  if b then 1 else -1

def popcnt {d : Nat} (p : Fin d → Bool) : Nat :=
  finSumNat (fun i => if p i then 1 else 0)

def hamming {d : Nat} (q x : Fin d → Bool) : Nat :=
  popcnt (fun i => xor (q i) (x i))

def dotBool {d : Nat} (q x : Fin d → Bool) : Int :=
  finSumInt (fun i => bipolar (q i) * bipolar (x i))

def ternaryVal (p n : Bool) : Int :=
  (if p then 1 else 0) - (if n then 1 else 0)

def dotTernary {d : Nat} (qp qn xp xn : Fin d → Bool) : Int :=
  finSumInt (fun i => ternaryVal (qp i) (qn i) * ternaryVal (xp i) (xn i))

def popcntTernaryDot {d : Nat} (qp qn xp xn : Fin d → Bool) : Int :=
  (popcnt (fun i => qp i && xp i) : Int) +
  (popcnt (fun i => qn i && xn i) : Int) -
  (popcnt (fun i => qp i && xn i) : Int) -
  (popcnt (fun i => qn i && xp i) : Int)

def twoBitVal (s h : Bool) : Int :=
  bipolar s * (if h then 3 else 1)

def dotTwoBit {d : Nat} (qs qh xs xh : Fin d → Bool) : Int :=
  finSumInt (fun i => twoBitVal (qs i) (qh i) * twoBitVal (xs i) (xh i))

def popcntTwoBitDot {d : Nat} (qs qh xs xh : Fin d → Bool) : Int :=
  let same : Fin d → Bool := fun i => !(xor (qs i) (xs i))
  let mOne : Fin d → Bool := fun i => xor (qh i) (xh i)
  let mBoth : Fin d → Bool := fun i => qh i && xh i
  let cAll : Int := 2 * (popcnt same : Int) - (d : Int)
  let cOne : Int := 2 * (popcnt (fun i => mOne i && same i) : Int) - (popcnt mOne : Int)
  let cBoth : Int := 2 * (popcnt (fun i => mBoth i && same i) : Int) - (popcnt mBoth : Int)
  cAll + 2 * cOne + 8 * cBoth

/-! ## Pillar 1B: 2-Stage Oversample Cantelli Concentration & SNR² Hierarchy -/

def cantelliTail (snrSq : Rat) : Rat :=
  1 / (1 + snrSq)

def stage1SnrSq (d delta etaSq : Rat) : Rat :=
  etaSq * d * delta * delta

def cantelliOversample (N K snrSq : Rat) : Rat :=
  (N / K) * cantelliTail snrSq

def eta1bSq (piRat : Rat) : Rat :=
  4 / (piRat * piRat)

def etaTernarySq : Rat :=
  8096 / 10000

def eta2bSq : Rat :=
  883 / 1000

/-! ## Pillar 2A: Matryoshka Prefix-Truncation vs Full-Dim Quantized Crossover -/

def totalEnergy {D : Nat} (lam : Fin D → Rat) : Rat :=
  finSumRat lam

def prefixEnergy {D : Nat} (dM : Nat) (h : dM ≤ D) (lam : Fin D → Rat) : Rat :=
  finSumRat (fun i : Fin dM => lam ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩)

def tailEnergy {D : Nat} (dM : Nat) (h : dM ≤ D) (lam : Fin D → Rat) : Rat :=
  finSumRat (fun i : Fin (D - dM) => lam ⟨dM + i.val, by omega⟩)

def energyFrac {D : Nat} (dM : Nat) (h : dM ≤ D) (lam : Fin D → Rat) : Rat :=
  prefixEnergy dM h lam / totalEnergy lam

def flatSpectrum (D : Nat) : Fin D → Rat :=
  fun _ => 1

def telescopingInvSqSpectrum (D : Nat) : Fin D → Rat :=
  fun i => (1 : Rat) / (((i.val + 1 : Nat) : Rat) * ((i.val + 2 : Nat) : Rat))

/-! ## Pillar 2B: Hypercube Sign-WHT Automatic Spectral Normalization -/

def sgnVec {D : Nat} (v : Fin D → Rat) : Fin D → Int :=
  fun i => if (0 : Rat) ≤ v i then 1 else -1

def dotInt {D : Nat} (q x : Fin D → Int) : Int :=
  finSumInt (fun i => q i * x i)

def normSqInt {D : Nat} (v : Fin D → Int) : Int :=
  dotInt v v

def dotRat {D : Nat} (q x : Fin D → Rat) : Rat :=
  finSumRat (fun i => q i * x i)

def normSqRat {D : Nat} (v : Fin D → Rat) : Rat :=
  dotRat v v

def prefixDotRat {D : Nat} (dM : Nat) (h : dM ≤ D) (q x : Fin D → Rat) : Rat :=
  finSumRat (fun i : Fin dM =>
    q ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩ * x ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩)

def prefixNormSqRat {D : Nat} (dM : Nat) (h : dM ≤ D) (x : Fin D → Rat) : Rat :=
  prefixDotRat dM h x x

def tailNormSqRat {D : Nat} (dM : Nat) (h : dM ≤ D) (x : Fin D → Rat) : Rat :=
  finSumRat (fun i : Fin (D - dM) =>
    x ⟨dM + i.val, by omega⟩ * x ⟨dM + i.val, by omega⟩)

def scaleRat {D : Nat} (c : Rat) (x : Fin D → Rat) : Fin D → Rat :=
  fun i => c * x i

/-! ## Pillar 1C: Stage-2 Symmetric INT4 Rescore Margin Preservation -/

def l1NormRat {D : Nat} (v : Fin D → Rat) : Rat :=
  finSumRat (fun i => ratAbs (v i))

def l1NormInt {D : Nat} (v : Fin D → Int) : Int :=
  finSumInt (fun i => intAbs (v i))

def clampInt (v lo hi : Int) : Int :=
  if v < lo then lo else if hi < v then hi else v

/-- Exact pure-integer symmetric `INT4` quantizer from `rag_rescore_kernels.hip`:
    step size `64`, half-step rounding offset `32`, symmetric range `[-7, +7]`. -/
def quantInt4Step64 (v : Int) : Int :=
  let q := if (0 : Int) ≤ v then (v + 32) / 64 else -((-v + 32) / 64)
  clampInt q (-7) 7

/-! ## Pillar 3: Memory-Footprint & Bandwidth-Roofline Speedup Model -/

def bytes1Bit (N D : Rat) : Rat := N * D / 8
def bytes2Bit (N D : Rat) : Rat := N * D / 4
def bytesInt4 (N D : Rat) : Rat := N * D / 2
def bytesInt8 (N D : Rat) : Rat := N * D
def bytesFP16 (N D : Rat) : Rat := 2 * N * D
def bytesFP32 (N D : Rat) : Rat := 4 * N * D

def twoStage1BitBytes (N D MK : Rat) : Rat :=
  N * (D / 8) + MK * (D / 2)

def twoStage2BitBytes (N D MK : Rat) : Rat :=
  N * (D / 4) + MK * (D / 2)

end RagPopcntMatryoshka
