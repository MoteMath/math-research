/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`unsigned-fp4-softmax-v`)

Pure-`Init` (zero Mathlib) exact rational and discrete bit-level definitions for:
1. IEEE/OCP subnormal unsigned 4-bit formats (`U-E0M4`, `U-E1M3`, `U-E2M2`, `U-E3M1`, `U-E4M0`)
   and signed `S-E2M1` / `FP8-E4M3` probability codebooks.
2. Exact EF21 contraction functional `1 - α(U, B)`.
3. Exact Softmax RTN simplex-sum conservation drift `D(U, N)`.
4. Discrete pair-antithetic and zero-carry stratified XOR-VDC stochastic rounding.
5. Finite-dimensional exact attention value centering (`V_c = V - 1 μ_V^T`).
6. Signed `FP4-E2M1` active codebook level count under raw vs centered value scaling.
-/

namespace UnsignedFp4SoftmaxV

/-- Standard IEEE/OCP subnormal unsigned floating-point integer decoder for `(eBits, mBits)`
    and raw code `c`.
    - When `eBits = 0`, returns `c` (uniform unsigned integer `UINT4`).
    - When `eBits ≥ 1`, splits `c` into exponent `E = c / 2^mBits` and mantissa `M = c % 2^mBits`:
      `E = 0` is subnormal with integer value `M`;
      `E ≥ 1` is normal with integer value `(2^mBits + M) * 2^(E - 1)`. -/
def decodeUnsignedIEEE (eBits mBits c : Nat) : Nat :=
  if eBits = 0 then
    c
  else
    let mSize := 2 ^ mBits
    let e := c / mSize
    let m := c % mSize
    if e = 0 then m else (mSize + m) * 2 ^ (e - 1)

/-- Full 16-entry integer codebook of an unsigned 4-bit IEEE/OCP format `(eBits, mBits)`. -/
def unsignedFp4IntLevels (eBits mBits : Nat) : List Nat :=
  (List.range 16).map (decodeUnsignedIEEE eBits mBits)

/-- Normalize an integer codebook by its maximum value `maxVal` into exact rationals in `[0, 1]`. -/
def normalizeLevels (lvls : List Nat) (maxVal : Nat) : List Rat :=
  lvls.map (fun (v : Nat) => (v : Rat) / (maxVal : Rat))

/-- Unsigned 4-bit uniform codebook `U-E0M4` (`UINT4`), 16 levels `{0/15, ..., 15/15}`. -/
def uE0M4Levels : List Rat := normalizeLevels (unsignedFp4IntLevels 0 4) 15

/-- Unsigned 4-bit IEEE-subnormal `U-E1M3`, 16 levels (collapses identically to `U-E0M4`). -/
def uE1M3Levels : List Rat := normalizeLevels (unsignedFp4IntLevels 1 3) 15

/-- Unsigned 4-bit `U-E2M2`, 16 levels scaled by `28`. -/
def uE2M2Levels : List Rat := normalizeLevels (unsignedFp4IntLevels 2 2) 28

/-- Unsigned 4-bit `U-E3M1`, 16 levels scaled by `192`. -/
def uE3M1Levels : List Rat := normalizeLevels (unsignedFp4IntLevels 3 1) 192

/-- Unsigned 4-bit `U-E4M0`, 16 levels scaled by `16384`. -/
def uE4M0Levels : List Rat := normalizeLevels (unsignedFp4IntLevels 4 0) 16384

/-- Nonnegative half of signed `FP4-E2M1` (`S-E2M1`), 8 levels `{0, 1, 2, 3, 4, 6, 8, 12} / 12`. -/
def sE2M1Levels : List Rat := normalizeLevels [0, 1, 2, 3, 4, 6, 8, 12] 12

/-- OCP `FP8-E4M3` nonnegative integer level for exponent `e < 16` and mantissa `m < 8`
    (with `(15, 7)` reserved for NaN, so max finite value is `(8 + 6) * 2^14 = 229376`). -/
def fp8E4M3IntLevel (e m : Nat) : Nat :=
  if e = 0 then m else (8 + m) * 2 ^ (e - 1)

/-- Maximum finite integer level in OCP `FP8-E4M3`. -/
def fp8E4M3MaxInt : Nat := 229376

/-- Exact EF21 contraction value attained at midpoint of bin `[u0, u1]` for block size `B`:
    `((B - 1) * h^2) / (1 + (B - 1) * m^2)` where `h = (u1 - u0)/2`, `m = (u0 + u1)/2`. -/
def ef21Bin (u0 u1 : Rat) (B : Nat) : Rat :=
  let h := (u1 - u0) / 2
  let m := (u0 + u1) / 2
  let b1 : Rat := ((B - 1 : Nat) : Rat)
  (b1 * (h * h)) / (1 + b1 * (m * m))

/-- Exact Softmax RTN simplex-sum drift value attained at midpoint of bin `[u0, u1]` for
    simplex dimension `N`: `((N - 1) * h) / (1 + (N - 1) * m)`. -/
def driftBin (u0 u1 : Rat) (N : Nat) : Rat :=
  let h := (u1 - u0) / 2
  let m := (u0 + u1) / 2
  let n1 : Rat := ((N - 1 : Nat) : Rat)
  (n1 * h) / (1 + n1 * m)

/-- Maximum of a bin functional `f` over all adjacent level pairs `(u_k, u_{k+1})` in `U`. -/
def maxAdjacentBins (f : Rat → Rat → Rat) : List Rat → Rat
  | [] => 0
  | [_] => 0
  | u0 :: u1 :: rest => max (f u0 u1) (maxAdjacentBins f (u1 :: rest))

/-- Closed-form worst-case EF21 contraction `1 - α(U, B)` over codebook `U` and block size `B`. -/
def ef21OneMinusAlpha (U : List Rat) (B : Nat) : Rat :=
  maxAdjacentBins (fun u0 u1 => ef21Bin u0 u1 B) U

/-- Closed-form worst-case RTN simplex-sum drift `D(U, N)` over codebook `U` and dimension `N`. -/
def simplexRtnDrift (U : List Rat) (N : Nat) : Rat :=
  maxAdjacentBins (fun u0 u1 => driftBin u0 u1 N) U

/-- Absolute value on `Rat`. -/
def ratAbs (x : Rat) : Rat :=
  if 0 ≤ x then x else -x

/-- Nonnegative RTN quantization distance to nearest endpoint of `[u0, u1]`. -/
def rtnDist (u0 u1 x : Rat) : Rat :=
  if x ≤ (u0 + u1) / 2 then x - u0 else u1 - x

/-- Signed RTN quantization error `Q(x) - x` inside bin `[u0, u1]`. -/
def rtnSignedErr (u0 u1 x : Rat) : Rat :=
  if x ≤ (u0 + u1) / 2 then u0 - x else u1 - x

/-- Finite rational sum `∑_{j : Fin n} f j`. -/
def sumFin : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => sumFin (fun i : Fin n => f i.castSucc) + f (Fin.last n)

/-- Finite natural-number sum `∑_{j : Fin n} f j`. -/
def sumFinNat : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumFinNat (fun i : Fin n => f i.castSucc) + f (Fin.last n)

/-- Finite inner product `∑_{j : Fin n} a j * b j`. -/
def dotFin {n : Nat} (a b : Fin n → Rat) : Rat :=
  sumFin (fun j => a j * b j)

/-- Discrete stochastic rounding indicator bit: rounds up (`1`) iff threshold `u < k`. -/
def srBit (k u : Nat) : Nat :=
  if u < k then 1 else 0

/-- Bit-reversal of the lowest `b` bits of `x` (Van der Corput permutation numerator). -/
def bitRevAux : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | b + 1, x, acc => bitRevAux b (x / 2) (2 * acc + x % 2)

/-- `b`-bit reversal `bitRev b x`. -/
def bitRev (b x : Nat) : Nat :=
  bitRevAux b x 0

/-- Zero-carry stratified XOR-VDC threshold for index `j` with `b`-bit scramble `mask`. -/
def xorVdcThreshold (b mask j : Nat) : Nat :=
  (bitRev b j) ^^^ mask

/-- Full signed `FP4-E2M1` integer codebook (15 distinct levels scaled by `12`). -/
def e2m1SignedInt : List Int :=
  [-12, -8, -6, -4, -3, -2, -1, 0, 1, 2, 3, 4, 6, 8, 12]

/-- Full signed `FP4-E2M1` rational codebook in `[-1, 1]` (15 distinct levels). -/
def e2m1SignedLevels : List Rat :=
  e2m1SignedInt.map (fun (z : Int) => (z : Rat) / 12)

/-- Number of codebook levels in `lvls` falling inside the closed interval `[lo, hi]`. -/
def countLevelsInInterval (lvls : List Rat) (lo hi : Rat) : Nat :=
  (lvls.filter (fun v => decide (lo ≤ v ∧ v ≤ hi))).length

end UnsignedFp4SoftmaxV
