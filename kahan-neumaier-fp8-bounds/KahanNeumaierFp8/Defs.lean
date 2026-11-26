/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Shared Definitions for Low-Precision Microbatch Accumulation & Compensated Separation Laws

Pure `Init` (zero Mathlib) exact integer, rational, and IEEE-754 RNE definitions for:
1. Exact IEEE-754 Round-to-Nearest-Even (RNE) rounding `flRNE P` on integers for any
   binary floating-point format with `P` explicit mantissa bits, plus sequential RNE
   and pairwise binary-tree RNE accumulators.
2. Exact Kahan (1965) and Neumaier (1974) compensated summation loops over `flRNE P`,
   late dipole spike streams, and Neumaier's self-swamping ceiling `2^{P+2}`.
3. Exact signed Kulisch bit-width law `W_min(M, P, ΔE) = 1 + ceil(log2 M) + (P + 1) + ΔE`
   and the bit-exact OCP `FP8-E4M3FN` finite grid in units of `2^{-9}`.
4. Microbatch-stratified XOR-VDC stochastic rounding (`u_m = u0 ^^^ bitrev K m`) over
   `M = 2^K` microbatches, exact bias, and MSE laws (`1/6` vs `M/6`).
5. Shared-exponent exact integer (`Int`, `Int32`, `Int64`) microbatch block accumulators.
-/

namespace KahanNeumaierFp8

/-- Exact IEEE-754 Round-to-Nearest-Even (RNE) rounding of a nonnegative integer `n`
    to a binary floating-point format with `P` explicit mantissa bits (`P + 1` total
    significand bits, unbounded exponent). -/
def flRNENat (P n : Nat) : Nat :=
  if n = 0 then 0
  else
    let e := Nat.log2 n
    if e ≤ P then n
    else
      let u := 2 ^ (e - P)
      let h := 2 ^ (e - P - 1)
      let q := n / u
      let r := n % u
      if r < h then q * u
      else if h < r then (q + 1) * u
      else if q % 2 = 0 then q * u
      else (q + 1) * u

/-- Exact signed IEEE-754 RNE rounding of an integer `x` with `P` explicit mantissa bits. -/
def flRNE (P : Nat) (x : Int) : Int :=
  if 0 ≤ x then Int.ofNat (flRNENat P x.natAbs)
  else -Int.ofNat (flRNENat P x.natAbs)

/-- Exact IEEE-754 RNE addition `fl_P(a + b)`. -/
def rneAdd (P : Nat) (a b : Int) : Int := flRNE P (a + b)

/-- Exact IEEE-754 RNE subtraction `fl_P(a - b)`. -/
def rneSub (P : Nat) (a b : Int) : Int := flRNE P (a - b)

/-- Exact worst-case IEEE-754 RNE freeze threshold `ρ_{freeze,min}(P) = 2^{P+1}`. -/
def rhoFreezeMin (P : Nat) : Nat := 2 ^ (P + 1)

/-- Exact maximum non-freeze ratio `ρ_{nonfreeze,max}(P) = 2^{P+2} - 2`. -/
def rhoNonfreezeMax (P : Nat) : Nat := 2 ^ (P + 2) - 2

/-- Sequential left-to-right IEEE-754 RNE accumulation. -/
def seqRNE (P : Nat) (xs : List Int) : Int :=
  xs.foldl (rneAdd P) 0

/-- One level of pairwise binary reduction. -/
def pairwiseStep {α : Type} (op : α → α → α) : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: rest => op a b :: pairwiseStep op rest

/-- Fuel-bounded pairwise binary-tree reduction. -/
def treeReduceAux {α : Type} (op : α → α → α) (zero : α) : Nat → List α → α
  | 0, xs => xs.headD zero
  | _ + 1, [] => zero
  | _ + 1, [a] => a
  | fuel + 1, xs => treeReduceAux op zero fuel (pairwiseStep op xs)

/-- Pairwise binary-tree IEEE-754 RNE accumulation. -/
def treeRNE (P : Nat) (xs : List Int) : Int :=
  treeReduceAux (rneAdd P) 0 xs.length xs

/-- Single step of Kahan (1965) compensated summation in `P`-bit mantissa RNE. -/
def kahanStep (P : Nat) (st : Int × Int) (x : Int) : Int × Int :=
  let (s, c) := st
  let y := rneSub P x c
  let t := rneAdd P s y
  let c' := rneSub P (rneSub P t s) y
  (t, c')

/-- Run Kahan summation over a stream, returning final `(s, c)`. -/
def kahanRun (P : Nat) (xs : List Int) : Int × Int :=
  xs.foldl (kahanStep P) (0, 0)

/-- Final Kahan sum `s`. -/
def kahanSum (P : Nat) (xs : List Int) : Int :=
  (kahanRun P xs).1

/-- Single step of Neumaier (1974) improved Kahan-Babuška summation in `P`-bit mantissa RNE. -/
def neumaierStep (P : Nat) (st : Int × Int) (x : Int) : Int × Int :=
  let (s, c) := st
  let t := rneAdd P s x
  let c' :=
    if s.natAbs ≥ x.natAbs then
      rneAdd P c (rneAdd P (rneSub P s t) x)
    else
      rneAdd P c (rneAdd P (rneSub P x t) s)
  (t, c')

/-- Run Neumaier summation over a stream, returning final `(s, c)`. -/
def neumaierRun (P : Nat) (xs : List Int) : Int × Int :=
  xs.foldl (neumaierStep P) (0, 0)

/-- Final Neumaier sum `fl_P(s + c)`. -/
def neumaierSum (P : Nat) (xs : List Int) : Int :=
  let (s, c) := neumaierRun P xs
  rneAdd P s c

/-- Exact Neumaier self-swamping ceiling `M_{Neumaier,max}(P) = 2^{P+2}`. -/
def neumaierCeiling (P : Nat) : Nat := 2 ^ (P + 2)

/-- Late dipole spike stream `[1, ..., 1 (mPre times), +S, -S, 1, ..., 1 (mPost times)]`. -/
def dipoleStream (mPre mPost : Nat) (S : Int) : List Int :=
  List.replicate mPre 1 ++ [S, -S] ++ List.replicate mPost 1

/-- Ceiling base-2 logarithm `⌈log2 M⌉` for `M : Nat`. -/
def ceilLog2 (M : Nat) : Nat :=
  if M ≤ 1 then 0 else Nat.log2 (M - 1) + 1

/-- Exact minimum signed two's-complement Kulisch accumulator bit width:
    `W_min(M, P, ΔE) = 1 + ⌈log2 M⌉ + (P + 1) + ΔE`. -/
def kulischMinBits (M P deltaE : Nat) : Nat :=
  1 + ceilLog2 M + (P + 1) + deltaE

/-- Signed 32-bit two's-complement maximum `2^31 - 1 = 2,147,483,647`. -/
def int32Max : Int := (2 ^ 31 : Int) - 1

/-- Signed 32-bit two's-complement minimum `-2^31 = -2,147,483,648`. -/
def int32Min : Int := -(2 ^ 31 : Int)

/-- Signed 64-bit two's-complement maximum `2^63 - 1`. -/
def int64Max : Int := (2 ^ 63 : Int) - 1

/-- Signed 64-bit two's-complement minimum `-2^63`. -/
def int64Min : Int := -(2 ^ 63 : Int)

/-- Finite OCP `FP8-E4M3FN` encoding: sign bit `sign`, 4-bit exponent `exp < 16`,
    3-bit mantissa `mant < 8`, excluding the single NaN encoding `(exp = 15, mant = 7)`. -/
structure Fp8E4M3FN where
  sign : Bool
  exp : Nat
  mant : Nat
  hExp : exp < 16
  hMant : mant < 8
  hNotNaN : ¬ (exp = 15 ∧ mant = 7)

/-- Exact magnitude of a finite OCP `FP8-E4M3FN` value in integer units of `2^{-9}`. -/
def Fp8E4M3FN.magUnits (x : Fp8E4M3FN) : Nat :=
  if x.exp = 0 then x.mant else (8 + x.mant) * 2 ^ (x.exp - 1)

/-- Exact signed integer value of a finite OCP `FP8-E4M3FN` value in units of `2^{-9}`. -/
def Fp8E4M3FN.toUnits (x : Fp8E4M3FN) : Int :=
  if x.sign then -(Int.ofNat x.magUnits) else Int.ofNat x.magUnits

/-- Exact rational value of a finite OCP `FP8-E4M3FN` value (`toUnits / 512`). -/
def Fp8E4M3FN.toRat (x : Fp8E4M3FN) : Rat :=
  (x.toUnits : Rat) / (512 : Rat)

/-- Maximum finite OCP `FP8-E4M3FN` value: `+448 = 229,376 * 2^{-9}`. -/
def fp8E4M3MaxFinite : Fp8E4M3FN :=
  ⟨false, 15, 6, by omega, by omega, by omega⟩

/-- Minimum positive subnormal OCP `FP8-E4M3FN` value: `2^{-9} = 1 * 2^{-9}`. -/
def fp8E4M3MinSubnormal : Fp8E4M3FN :=
  ⟨false, 0, 1, by omega, by omega, by omega⟩

/-- Maximum finite OCP `FP8-E4M3FN` magnitude in units of `2^{-9}` (`448 * 512 = 229,376`). -/
def e4m3MaxUnits : Nat := 229376

/-- Exact maximum count of arbitrary OCP `FP8-E4M3FN` values guaranteed overflow-free in `int32_t`. -/
def e4m3MaxInt32Count : Nat := 9362

/-- Reverse the lowest `K` bits of `x : Nat`. -/
def bitrev : Nat → Nat → Nat
  | 0, _ => 0
  | K + 1, x => (x % 2) * 2 ^ K + bitrev K (x / 2)

/-- Microbatch-stratified XOR-VDC threshold `u_m = u0 ^^^ bitrev K m`. -/
def xorVdc (K u0 m : Nat) : Nat :=
  u0 ^^^ bitrev K m

/-- Exact absolute value on `Rat`. -/
def ratAbs (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then x else -x

/-- Recursive finite sum over `Fin k → Rat`. -/
def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f =>
    finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum `∑_{j : Fin n} f j` over `Rat`. -/
def finSum {n : Nat} (f : Fin n → Rat) : Rat := finSumAux n f

/-- Exact indicator for stratified threshold `(u + v) / 2^K` against target `(a + r) / 2^K`. -/
def vdcIndicator (u a : Nat) (v r : Rat) : Rat :=
  if (u : Rat) + v < (a : Rat) + r then 1 else 0

/-- Independent SR sum MSE at fractional drift `p` over `M` microbatches: `M * p * (1 - p)`. -/
def mseIndSR (M : Nat) (p : Rat) : Rat :=
  (M : Rat) * (p * (1 - p))

/-- Stratified XOR-VDC SR sum MSE at boundary remainder `r ∈ [0, 1)`: `r * (1 - r)`. -/
def mseXorVdcSR (r : Rat) : Rat :=
  r * (1 - r)

/-- Uniform-drift average MSE of independent SR over `M` microbatches: `M / 6`. -/
def mseIndSRAvg (M : Nat) : Rat :=
  (M : Rat) / 6

/-- Uniform-drift average MSE of stratified XOR-VDC SR: `1 / 6`. -/
def mseXorVdcSRAvg : Rat :=
  1 / 6

/-- Sequential exact integer sum. -/
def seqIntSum (xs : List Int) : Int :=
  xs.foldl (· + ·) 0

/-- Pairwise binary-tree exact integer sum. -/
def treeIntSum (xs : List Int) : Int :=
  treeReduceAux (· + ·) 0 xs.length xs

/-- Exact integer vector addition for a shared-exponent block of width `d`. -/
def blockAdd {d : Nat} (a b : Fin d → Int) : Fin d → Int :=
  fun j => a j + b j

/-- Zero vector for a shared-exponent block of width `d`. -/
def blockZero (d : Nat) : Fin d → Int :=
  fun _ => 0

/-- Exact integer shared-exponent microbatch block accumulator. -/
def blockAccum {d : Nat} (gs : List (Fin d → Int)) : Fin d → Int :=
  gs.foldl blockAdd (blockZero d)

/-- `Int32` register vector addition for a shared-exponent block of width `d`. -/
def blockAddInt32 {d : Nat} (a b : Fin d → Int32) : Fin d → Int32 :=
  fun j => a j + b j

/-- `Int32` zero block of width `d`. -/
def blockZeroInt32 (d : Nat) : Fin d → Int32 :=
  fun _ => 0

/-- `Int32` register shared-exponent microbatch block accumulator. -/
def blockAccumInt32 {d : Nat} (gs : List (Fin d → Int32)) : Fin d → Int32 :=
  gs.foldl blockAddInt32 (blockZeroInt32 d)

/-- `Int64` register vector addition for a shared-exponent block of width `d`. -/
def blockAddInt64 {d : Nat} (a b : Fin d → Int64) : Fin d → Int64 :=
  fun j => a j + b j

/-- `Int64` zero block of width `d`. -/
def blockZeroInt64 (d : Nat) : Fin d → Int64 :=
  fun _ => 0

/-- `Int64` register shared-exponent microbatch block accumulator. -/
def blockAccumInt64 {d : Nat} (gs : List (Fin d → Int64)) : Fin d → Int64 :=
  gs.foldl blockAddInt64 (blockZeroInt64 d)

end KahanNeumaierFp8
