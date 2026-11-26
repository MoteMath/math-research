/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`rmsnorm-hybrid-linf-l1`)

Pure-`Init` (zero Mathlib) exact rational and bit-level IEEE-754 RNE definitions for:
1. `L∞ + L1` hybrid norm `H_{α,β}(x)`, exact vector norms (`linfNorm`, `l1Norm`, `sumSq`, `meanSq`),
   and squared condition number `hybridKappaSq`.
2. Bit-exact IEEE-754 Round-to-Nearest-Even (RNE) formats (`BF16`, `FP16`, `FP8_E4M3`,
   `FP8_E5M2`, `MXFP4_E2M1`), sequential `sum(x_i^2)` accumulation, and 1-pass LayerNorm variance.
3. Exact and rounded 2-pass shifted-mean LayerNorm variance.
-/

namespace RmsnormHybridLinfL1

/-! ## Dyadic powers and elementary `Rat` helpers -/

/-- Exact rational power of two `2^k`. -/
def pow2Rat (k : Nat) : Rat := ((2 ^ k : Nat) : Rat)

/-- Exact rational inverse power of two `2^(-k)`. -/
def invPow2Rat (k : Nat) : Rat := (1 : Rat) / pow2Rat k

/-- Exact rational signed power of two `2^e` for `e : Int`. -/
def pow2Int (e : Int) : Rat :=
  if 0 ≤ e then pow2Rat e.toNat else invPow2Rat (-e).toNat

/-- Exact rational absolute value. -/
def ratAbs (q : Rat) : Rat := if q < 0 then -q else q

/-- Exact rational binary maximum. -/
def ratMax (a b : Rat) : Rat := if a ≤ b then b else a

/-! ## Vector norms and `L∞ + L1` hybrid norm over `Fin d → Rat` -/

/-- Exact rational finite sum `∑_{i : Fin d} f i`. -/
def finSum : (d : Nat) → (Fin d → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => finSum n (fun i => f i.castSucc) + f ⟨n, Nat.lt_succ_self n⟩

/-- Exact `L1` norm `∑ |x_i|`. -/
def l1Norm {d : Nat} (x : Fin d → Rat) : Rat :=
  finSum d (fun i => ratAbs (x i))

/-- Exact sum of squares `∑ x_i^2`. -/
def sumSq {d : Nat} (x : Fin d → Rat) : Rat :=
  finSum d (fun i => x i * x i)

/-- Exact mean square `MS(x) = (1/d) ∑ x_i^2 = RMS(x)^2`. -/
def meanSq {d : Nat} (x : Fin d → Rat) : Rat :=
  sumSq x / (d : Rat)

/-- Exact arithmetic mean `(1/d) ∑ x_i`. -/
def vecMean {d : Nat} (x : Fin d → Rat) : Rat :=
  finSum d x / (d : Rat)

/-- Exact `L∞` norm `max_i |x_i|` (defined as `0` for `d = 0`). -/
def linfNorm : {d : Nat} → (Fin d → Rat) → Rat
  | 0, _ => 0
  | n + 1, x => ratMax (linfNorm (fun i => x i.castSucc)) (ratAbs (x ⟨n, Nat.lt_succ_self n⟩))

/-- The `L∞ + L1` hybrid norm `H_{α,β}(x) = α ‖x‖_∞ + (β / d) ‖x‖_1`. -/
def hybridNorm {d : Nat} (α β : Rat) (x : Fin d → Rat) : Rat :=
  α * linfNorm x + (β / (d : Rat)) * l1Norm x

/-- Upper-envelope squared constant `R_max(d, α, β)^2 = α^2 d + 2 α β + β^2`. -/
def hybridUpperConstSq (d : Nat) (α β : Rat) : Rat :=
  α * α * (d : Rat) + 2 * α * β + β * β

/-- Lower-envelope squared constant `R_min_lb(α, β)^2 = 4 α β`. -/
def hybridLowerConstSq (α β : Rat) : Rat :=
  4 * α * β

/-- Squared distortion ratio `κ(d, α, β)^2 = (α^2 d + 2 α β + β^2) / (4 α β)`. -/
def hybridKappaSq (d : Nat) (α β : Rat) : Rat :=
  hybridUpperConstSq d α β / hybridLowerConstSq α β

/-- Upper-envelope extremal spike-plus-uniform vector `x_0 = 1`, `x_i = β / (α d + β)` (`i ≥ 1`). -/
def upperExtremalVec (d : Nat) (α β : Rat) : Fin d → Rat :=
  fun i => if i.val = 0 then 1 else β / (α * (d : Rat) + β)

/-- `k`-sparse binary vector `x_i = 1` for `i < k`, `x_i = 0` for `i ≥ k`. -/
def kSparseVec (d k : Nat) : Fin d → Rat :=
  fun i => if i.val < k then 1 else 0

/-! ## Exact Bit-Level IEEE-754 Round-to-Nearest-Even (RNE) Model -/

/-- Specification of an IEEE-754 / OCP binary floating-point format. -/
structure FloatFormat where
  ebits : Nat
  mbits : Nat
  bias : Nat
  hasInf : Bool
  hasNaNAtMax : Bool
  maxExpField : Nat
  maxMantAtMaxExp : Nat
deriving DecidableEq, Repr

/-- Precision `p = mbits + 1` in bits. -/
def FloatFormat.precision (fmt : FloatFormat) : Nat := fmt.mbits + 1

/-- Decoded value of a bit pattern. -/
inductive FloatVal where
  | finite (val : Rat)
  | inf (neg : Bool)
  | nan
deriving DecidableEq, Repr

/-- BF16 (`p = 8`, `ebits = 8`, `mbits = 7`, `bias = 127`). -/
def fmtBF16 : FloatFormat :=
  { ebits := 8, mbits := 7, bias := 127, hasInf := true, hasNaNAtMax := false,
    maxExpField := 254, maxMantAtMaxExp := 127 }

/-- FP16 (`p = 11`, `ebits = 5`, `mbits = 10`, `bias = 15`). -/
def fmtFP16 : FloatFormat :=
  { ebits := 5, mbits := 10, bias := 15, hasInf := true, hasNaNAtMax := false,
    maxExpField := 30, maxMantAtMaxExp := 1023 }

/-- OCP FP8 E4M3 (`p = 4`, `ebits = 4`, `mbits = 3`, `bias = 7`, saturating, `exp=15,mant=7` is NaN). -/
def fmtFP8E4M3 : FloatFormat :=
  { ebits := 4, mbits := 3, bias := 7, hasInf := false, hasNaNAtMax := true,
    maxExpField := 15, maxMantAtMaxExp := 6 }

/-- IEEE FP8 E5M2 (`p = 3`, `ebits = 5`, `mbits = 2`, `bias = 15`). -/
def fmtFP8E5M2 : FloatFormat :=
  { ebits := 5, mbits := 2, bias := 15, hasInf := true, hasNaNAtMax := false,
    maxExpField := 30, maxMantAtMaxExp := 3 }

/-- OCP MXFP4 E2M1 (`p = 2`, `ebits = 2`, `mbits = 1`, `bias = 1`, saturating, no Inf/NaN). -/
def fmtMXFP4 : FloatFormat :=
  { ebits := 2, mbits := 1, bias := 1, hasInf := false, hasNaNAtMax := false,
    maxExpField := 3, maxMantAtMaxExp := 1 }

/-- Canonical NaN bit pattern for a format. -/
def FloatFormat.nanBits (fmt : FloatFormat) : Nat :=
  if fmt.hasInf then
    (((1 <<< fmt.ebits) - 1) <<< fmt.mbits) ||| 1
  else
    (1 <<< (fmt.ebits + fmt.mbits)) - 1

/-- Exact integer-quotient IEEE-754 Round-to-Nearest-Even of `n / d` (`d > 0`). -/
def rneDivNat (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if 2 * r > d then q + 1
  else if 2 * r < d then q
  else q + (q &&& 1)

/-- Decoded dyadic value `mant * 2^exp` of a bit pattern (pure integer binary representation). -/
inductive DyadicVal where
  | finite (mant : Int) (exp : Int)
  | inf (neg : Bool)
  | nan
deriving DecidableEq, Repr

/-- Exact dyadic decoding of an unsigned bit pattern in `fmt`. -/
def FloatFormat.decodeDyadic (fmt : FloatFormat) (bits : Nat) : DyadicVal :=
  let sign := (bits >>> (fmt.ebits + fmt.mbits)) &&& 1
  let exp := (bits >>> fmt.mbits) &&& ((1 <<< fmt.ebits) - 1)
  let mant := bits &&& ((1 <<< fmt.mbits) - 1)
  if fmt.hasInf && exp == (1 <<< fmt.ebits) - 1 then
    if mant == 0 then DyadicVal.inf (sign == 1) else DyadicVal.nan
  else if !fmt.hasInf && fmt.hasNaNAtMax && exp == fmt.maxExpField &&
      mant == (1 <<< fmt.mbits) - 1 then
    DyadicVal.nan
  else
    let rawMant : Int :=
      if exp == 0 then (mant : Int)
      else (((1 <<< fmt.mbits) + mant : Nat) : Int)
    let rawExp : Int :=
      if exp == 0 then (1 : Int) - (fmt.bias : Int) - (fmt.mbits : Int)
      else (exp : Int) - (fmt.bias : Int) - (fmt.mbits : Int)
    DyadicVal.finite (if sign == 1 then -rawMant else rawMant) rawExp

/-- Exact rational decoding of an unsigned bit pattern in `fmt`. -/
def FloatFormat.decode (fmt : FloatFormat) (bits : Nat) : FloatVal :=
  match fmt.decodeDyadic bits with
  | DyadicVal.finite m e => FloatVal.finite ((m : Rat) * pow2Int e)
  | DyadicVal.inf neg => FloatVal.inf neg
  | DyadicVal.nan => FloatVal.nan

/-- Pure-integer dyadic comparison `a * 2^ea ≥ b * 2^eb`. -/
def dyadicGe (a : Nat) (ea : Int) (b : Nat) (eb : Int) : Bool :=
  if eb ≤ ea then
    decide (b ≤ a * (2 ^ (ea - eb).toNat))
  else
    decide (b * (2 ^ (eb - ea).toNat) ≤ a)

/-- Pure-integer IEEE-754 RNE scaling `roundNearestEven(a * 2^delta)`. -/
def rneShiftNat (a : Nat) (delta : Int) : Nat :=
  if 0 ≤ delta then
    a * (2 ^ delta.toNat)
  else
    rneDivNat a (2 ^ (-delta).toNat)

/-- Pure-integer bit-exact IEEE-754 RNE encoding of dyadic `m * 2^e` into `fmt`. -/
def FloatFormat.encodeDyadic (fmt : FloatFormat) (m : Int) (e : Int) : Nat :=
  let sign : Nat := if m < 0 then 1 else 0
  let am : Nat := m.natAbs
  if am == 0 then
    sign <<< (fmt.ebits + fmt.mbits)
  else
    let maxM : Nat := (1 <<< fmt.mbits) + fmt.maxMantAtMaxExp
    let maxE : Int := (fmt.maxExpField : Int) - (fmt.bias : Int) - (fmt.mbits : Int)
    if fmt.hasInf && dyadicGe am e (2 * maxM + 1) (maxE - 1) then
      (sign <<< (fmt.ebits + fmt.mbits)) ||| (((1 <<< fmt.ebits) - 1) <<< fmt.mbits)
    else if !fmt.hasInf && dyadicGe am e maxM maxE then
      (sign <<< (fmt.ebits + fmt.mbits)) ||| (fmt.maxExpField <<< fmt.mbits) ||| fmt.maxMantAtMaxExp
    else
      let minNormExp : Int := (1 : Int) - (fmt.bias : Int)
      if !dyadicGe am e 1 minNormExp then
        let q := rneShiftNat am (e - (minNormExp - (fmt.mbits : Int)))
        if q == (1 <<< fmt.mbits) then
          (sign <<< (fmt.ebits + fmt.mbits)) ||| (1 <<< fmt.mbits)
        else
          (sign <<< (fmt.ebits + fmt.mbits)) ||| q
      else
        let eVal : Int := (Nat.log2 am : Int) + e
        let expField0 : Nat := (eVal + (fmt.bias : Int)).toNat
        let q0 := rneShiftNat am (e - (eVal - (fmt.mbits : Int)))
        let (q, expField) :=
          if q0 == (1 <<< (fmt.mbits + 1)) then (q0 >>> 1, expField0 + 1)
          else (q0, expField0)
        if fmt.hasInf && (1 <<< fmt.ebits) - 1 ≤ expField then
          (sign <<< (fmt.ebits + fmt.mbits)) ||| (((1 <<< fmt.ebits) - 1) <<< fmt.mbits)
        else if !fmt.hasInf && fmt.maxExpField < expField then
          (sign <<< (fmt.ebits + fmt.mbits)) ||| (fmt.maxExpField <<< fmt.mbits) ||| fmt.maxMantAtMaxExp
        else
          let mant0 := q - (1 <<< fmt.mbits)
          let mant :=
            if !fmt.hasInf && expField == fmt.maxExpField && fmt.maxMantAtMaxExp < mant0 then
              fmt.maxMantAtMaxExp
            else
              mant0
          (sign <<< (fmt.ebits + fmt.mbits)) ||| (expField <<< fmt.mbits) ||| mant

/-- Exact dyadic addition `(m1 * 2^e1) + (m2 * 2^e2)`. -/
def dyadicAdd (m1 e1 m2 e2 : Int) : Int × Int :=
  if e1 ≤ e2 then
    (m1 + m2 * ((2 ^ (e2 - e1).toNat : Nat) : Int), e1)
  else
    (m1 * ((2 ^ (e1 - e2).toNat : Nat) : Int) + m2, e2)

/-- Bit-exact RNE addition in `fmt`. -/
def FloatFormat.flAdd (fmt : FloatFormat) (a b : Nat) : Nat :=
  match fmt.decodeDyadic a, fmt.decodeDyadic b with
  | DyadicVal.finite m1 e1, DyadicVal.finite m2 e2 =>
    let (m, e) := dyadicAdd m1 e1 m2 e2
    fmt.encodeDyadic m e
  | _, _ => fmt.nanBits

/-- Bit-exact RNE subtraction in `fmt`. -/
def FloatFormat.flSub (fmt : FloatFormat) (a b : Nat) : Nat :=
  match fmt.decodeDyadic a, fmt.decodeDyadic b with
  | DyadicVal.finite m1 e1, DyadicVal.finite m2 e2 =>
    let (m, e) := dyadicAdd m1 e1 (-m2) e2
    fmt.encodeDyadic m e
  | _, _ => fmt.nanBits

/-- Bit-exact RNE multiplication in `fmt`. -/
def FloatFormat.flMul (fmt : FloatFormat) (a b : Nat) : Nat :=
  match fmt.decodeDyadic a, fmt.decodeDyadic b with
  | DyadicVal.finite m1 e1, DyadicVal.finite m2 e2 =>
    fmt.encodeDyadic (m1 * m2) (e1 + e2)
  | _, _ => fmt.nanBits

/-- Sequential addition of `n` unit squares (`1.0`) starting from accumulator `acc`. -/
def FloatFormat.seqAddOnes (fmt : FloatFormat) (acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => fmt.seqAddOnes (fmt.flAdd acc (fmt.encodeDyadic 1 0)) n

/-- 1-pass LayerNorm variance in `fmt` on a symmetric pair `(fl(c + 1), fl(c - 1))`. -/
def FloatFormat.onePassVarPairBits (fmt : FloatFormat) (cBits : Nat) : Nat × Nat × Nat :=
  let oneBits := fmt.encodeDyadic 1 0
  let halfBits := fmt.encodeDyadic 1 (-1)
  let x0 := fmt.flAdd cBits oneBits
  let x1 := fmt.flSub cBits oneBits
  let mu := fmt.flMul halfBits (fmt.flAdd x0 x1)
  let m2 := fmt.flMul halfBits (fmt.flAdd (fmt.flMul x0 x0) (fmt.flMul x1 x1))
  let mu2 := fmt.flMul mu mu
  let varBits := fmt.flSub m2 mu2
  (m2, mu2, varBits)

/-! ## 2-Pass Shifted-Mean LayerNorm Variance -/

/-- Exact rational 2-pass shifted-mean variance `(1/d) ∑ (x_i - μ)^2`. -/
def twoPassVar {d : Nat} (x : Fin d → Rat) (μ : Rat) : Rat :=
  finSum d (fun i => (x i - μ) * (x i - μ)) / (d : Rat)

/-- Sequential rounded accumulation under an arbitrary rounding operator `fl : Rat → Rat`. -/
def flSeqSum (fl : Rat → Rat) : (d : Nat) → (Fin d → Rat) → Rat
  | 0, _ => fl 0
  | n + 1, f => fl (flSeqSum fl n (fun i => f i.castSucc) + f ⟨n, Nat.lt_succ_self n⟩)

/-- Rounded 2-pass shifted-mean variance under an arbitrary rounding operator `fl : Rat → Rat`. -/
def twoPassVarRounded (fl : Rat → Rat) {d : Nat} (x : Fin d → Rat) (μHat : Rat) : Rat :=
  fl (flSeqSum fl d (fun i => fl (fl (x i - μHat) * fl (x i - μHat))) / (d : Rat))

end RmsnormHybridLinfL1
