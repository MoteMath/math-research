/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`FlashAttnDyadicSlack.Defs`)

Pure-`Init` (zero Mathlib) exact rational, integer, and natural-number definitions for:
1. IEEE-754 normal binary floating-point numbers and exact dyadic power-of-two scaling (`2^-k`).
2. IEEE-754 Round-to-Nearest-Even (RNE) division rounding and sequential multiplication by
   `α = 1 - 2^{-(p+1)}` (eager online-softmax 1-ULP-per-step collapse).
3. `FP8-E4M3` (`max = 448`) and `FP16` (`max = 65504`, `ulp = 32`, overflow midpoint `65520`)
   slack overflow boundaries and extended-float division (`Inf/Inf = NaN`, `finite/Inf = 0`).
4. Dyadic exponent normalization (`|l| >= 2^14`) for arbitrary-length online softmax.
5. Signed `int32` (`Q8.20`) Kulisch tile accumulator for `64`-element `FP8`/`UE3M1` `P * V` tiles.
-/

namespace FlashAttnDyadicSlack

/-! ### Basic Rational & Power-of-Two Utilities -/

def pow2Rat (k : Nat) : Rat :=
  ((2 ^ k : Nat) : Rat)

def invPow2Rat (k : Nat) : Rat :=
  (1 : Rat) / pow2Rat k

def pow2IntRat (e : Int) : Rat :=
  if 0 ≤ e then
    ((2 ^ e.toNat : Nat) : Rat)
  else
    (1 : Rat) / ((2 ^ (-e).toNat : Nat) : Rat)

def ratPow (x : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => ratPow x n * x

/-! ### Pillar 1A: IEEE-754 Normal Binary Floats & Exact Dyadic Power-of-Two Rescaling -/

/-- Exact IEEE-754 normal binary floating-point number with `p` explicit mantissa bits
    (`BF16: p = 7`, `FP16: p = 10`, `FP32: p = 23`), unbiased exponent `exp`,
    sign bit `neg`, and trailing mantissa `mant < 2^p`. -/
structure NormalFloat (p : Nat) where
  neg : Bool
  exp : Int
  mant : Nat
  hMant : mant < 2 ^ p

def NormalFloat.signRat {p : Nat} (x : NormalFloat p) : Rat :=
  if x.neg then (-1 : Rat) else (1 : Rat)

def NormalFloat.sig {p : Nat} (x : NormalFloat p) : Nat :=
  2 ^ p + x.mant

/-- Exact rational value `(-1)^s * (1 + m / 2^p) * 2^e` of a normal binary float. -/
def NormalFloat.toRat {p : Nat} (x : NormalFloat p) : Rat :=
  x.signRat * ((x.sig : Rat) / pow2Rat p) * pow2IntRat x.exp

/-- Exact dyadic power-of-two scaling by `2^-k`: shifts ONLY the exponent `e ↦ e - k`
    while leaving sign and mantissa bits untouched. -/
def NormalFloat.scaleNegPow2 {p : Nat} (x : NormalFloat p) (k : Nat) : NormalFloat p :=
  { neg := x.neg, exp := x.exp - (k : Int), mant := x.mant, hMant := x.hMant }

/-- Exact IEEE-754 Round-to-Nearest-Even (RNE) rounding of the nonnegative rational `num / den`
    (`den > 0`) to the nearest natural number (ties to even). -/
def rneNatDiv (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r < den then
    q
  else if den < 2 * r then
    q + 1
  else if q % 2 = 0 then
    q
  else
    q + 1

/-! ### Pillar 1B: Eager Online-Softmax One-ULP-Per-Step Collapse -/

/-- Exact single IEEE-754 RNE multiplication step of a positive normal `p`-mantissa-bit float
    `(e, s)` (`2^p ≤ s < 2^(p+1)`, value `s * 2^(e - p)`) by `α = 1 - 2^{-(p+1)}`.
    When `s = 2^p`, the exact product `(2^(p+1) - 1) * 2^(e - 1 - p)` lies in binade `e - 1`;
    when `2^p < s < 2^(p+1)`, the product stays in binade `e` and rounds via `rneNatDiv`. -/
def rneMulOneMinusHalfUlpStep (p : Nat) (st : Int × Nat) : Int × Nat :=
  let (e, s) := st
  if s ≤ 2 ^ p then
    (e - 1, 2 ^ (p + 1) - 1)
  else
    (e, rneNatDiv (s * (2 ^ (p + 1) - 1)) (2 ^ (p + 1)))

/-- Iterated sequential IEEE-754 RNE multiplication by `α = 1 - 2^{-(p+1)}`. -/
def seqPowState (p : Nat) : Nat → Int × Nat → Int × Nat
  | 0, st => st
  | n + 1, st => seqPowState p n (rneMulOneMinusHalfUlpStep p st)

/-- Exact rational value of a positive normal float state `(e, s)` with `p` mantissa bits. -/
def posFloatVal (p : Nat) (st : Int × Nat) : Rat :=
  ((st.2 : Rat) / pow2Rat p) * pow2IntRat st.1

/-- Value of `n` sequential eager IEEE-754 RNE multiplications by `1 - 2^{-(p+1)}`
    starting from `1 = (0, 2^p)`. -/
def seqPow (p n : Nat) : Rat :=
  posFloatVal p (seqPowState p n (0, 2 ^ p))

/-! ### Pillar 1C & 2A: Slack Overflow Boundaries & FP16 65520 Overflow Cliff -/

/-- Exact integer ULP in binade `[2^k, 2^(k+1))` for a `p`-mantissa-bit binary float (`k ≥ p`). -/
def binadeUlp (p k : Nat) : Nat :=
  2 ^ (k - p)

/-- Exact IEEE-754 RNE rounding of an integer `m` in binade `[2^k, 2^(k+1))` for precision `p`. -/
def binadeRneNat (p k m : Nat) : Nat :=
  if k ≤ p then
    m
  else
    let u := 2 ^ (k - p)
    let h := 2 ^ (k - p - 1)
    let q := m / u
    let r := m % u
    if r < h then
      q * u
    else if h < r then
      (q + 1) * u
    else if q % 2 = 0 then
      q * u
    else
      (q + 1) * u

/-- Maximum finite value of OCP `FP8-E4M3FN`: `(1 + 6/8) * 2^8 = 448`. -/
def fp8E4M3Max : Nat := 448

/-- Maximum finite normal value of IEEE-754 binary16 (`FP16`): `(2^11 - 1) * 2^5 = 65504`. -/
def fp16MaxNormal : Nat := (2 ^ 11 - 1) * 2 ^ 5

/-- ULP in the top finite binade `[2^15, 2^16)` of `FP16`: `2^(15 - 10) = 32`. -/
def fp16TopUlp : Nat := binadeUlp 10 15

/-- Exact `FP16` RNE overflow-to-`+Inf` midpoint threshold: `65504 + 16 = 65520`. -/
def fp16OverflowThreshold : Nat := fp16MaxNormal + fp16TopUlp / 2

/-- Standard FlashAttention key/value tile width `B_c = 64`. -/
def tileWidthBc : Nat := 64

/-- Extended floating-point value for modeling `FP16` `O / l` overflow and `NaN` outcomes. -/
inductive ExtFloat where
  | finite (v : Rat)
  | posInf
  | negInf
  | nan
  deriving DecidableEq, Repr

/-- Exact IEEE-754 division on `ExtFloat` (capturing `Inf/Inf = NaN` and `finite/Inf = 0`). -/
def fpDiv : ExtFloat → ExtFloat → ExtFloat
  | .nan, _ => .nan
  | _, .nan => .nan
  | .posInf, .posInf => .nan
  | .posInf, .negInf => .nan
  | .negInf, .posInf => .nan
  | .negInf, .negInf => .nan
  | .finite _, .posInf => .finite 0
  | .finite _, .negInf => .finite 0
  | .posInf, .finite y =>
    if y = 0 then .nan else if (0 : Rat) < y then .posInf else .negInf
  | .negInf, .finite y =>
    if y = 0 then .nan else if (0 : Rat) < y then .negInf else .posInf
  | .finite x, .finite y =>
    if y = 0 then .nan else .finite (x / y)

/-- Exact IEEE-754 `FP16` RNE rounding of a nonnegative integer flat-attention sum `L`. -/
def fp16RneNatToExt (L : Nat) : ExtFloat :=
  if L < 2 ^ 15 then
    .finite (L : Rat)
  else if L < 2 ^ 16 then
    let r := binadeRneNat 10 15 L
    if r = 2 ^ 16 then .posInf else .finite (r : Rat)
  else
    .posInf

/-! ### Pillar 2B: Dyadic Exponent Normalization (`|l| >= 2^14`) -/

/-- Exact `FP16` dyadic normalization trigger threshold `2^14 = 16384`. -/
def fp16NormThreshold : Rat := (16384 : Rat)

/-- Single step of dyadic-normalized online-softmax accumulation: adds scaled `(w * 2^-k * v, w * 2^-k)`
    and whenever `l' >= 2^14`, scales both `(O', l')` by exact `2^-1` (`0.5`) and increments `k`. -/
def dyadicNormStep (st : Rat × Rat × Nat) (wv : Rat × Rat) : Rat × Rat × Nat :=
  let (O, l, k) := st
  let (w, v) := wv
  let sc := invPow2Rat k
  let O' := O + w * sc * v
  let l' := l + w * sc
  if l' < fp16NormThreshold then
    (O', l', k)
  else
    (O' / 2, l' / 2, k + 1)

/-- Online dyadic-normalized accumulation over an arbitrary list of `(weight, value)` pairs. -/
def dyadicNormRun (xs : List (Rat × Rat)) : Rat × Rat × Nat :=
  xs.foldl dyadicNormStep (0, 0, 0)

/-- Exact unnormalized numerator `∑ w_i * v_i`. -/
def exactAttentionO (xs : List (Rat × Rat)) : Rat :=
  xs.foldl (fun acc wv => acc + wv.1 * wv.2) 0

/-- Exact unnormalized denominator `∑ w_i`. -/
def exactAttentionL (xs : List (Rat × Rat)) : Rat :=
  xs.foldl (fun acc wv => acc + wv.1) 0

/-! ### Pillar 3: Signed `int32` (`Q8.20`) Kulisch Tile Accumulator -/

/-- Minimum signed 32-bit two's-complement integer `-2^31 = -2147483648`. -/
def int32Min : Int := -((2 ^ 31 : Nat) : Int)

/-- Maximum signed 32-bit two's-complement integer `2^31 - 1 = 2147483647`. -/
def int32Max : Int := ((2 ^ 31 : Nat) : Int) - 1

/-- Predicate asserting an integer lies strictly within signed `int32` range without overflow. -/
def inInt32Range (x : Int) : Prop :=
  int32Min ≤ x ∧ x ≤ int32Max

/-- Fixed-point `Q8.20` scale factor `2^20 = 1048576`. -/
def kulischScale : Nat := 2 ^ 20

/-- Exact `Q8.20` embedding of an `FP8-E4M3` (`2^-9`) × `FP8-E4M3` (`2^-9`) product:
    `(pInt * 2^-9) * (vInt * 2^-9) = (pInt * vInt * 4) * 2^-20`. -/
def fp8ProdToQ20 (pInt vInt : Int) : Int :=
  pInt * vInt * 4

/-- Exact `Q8.20` embedding of a `UE3M1` (`2^-7`) × `FP8-E4M3` (`2^-9`) product:
    `(pInt * 2^-7) * (vInt * 2^-9) = (pInt * vInt * 16) * 2^-20`. -/
def ue3m1ProdToQ20 (pInt vInt : Int) : Int :=
  pInt * vInt * 16

/-- Exact integer Kulisch tile sum. -/
def kulischSum : List Int → Int
  | [] => 0
  | x :: xs => x + kulischSum xs

/-- Exact rational tile sum. -/
def ratSum : List Rat → Rat
  | [] => 0
  | x :: xs => x + ratSum xs

/-- Left-fold integer accumulation (matching sequential GPU loop accumulation). -/
def kulischFoldl (xs : List Int) : Int :=
  xs.foldl (· + ·) 0

end FlashAttnDyadicSlack
