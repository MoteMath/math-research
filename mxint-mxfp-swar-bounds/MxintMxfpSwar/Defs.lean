/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`mxint-mxfp-swar-bounds`)

Pure-`Init` (zero Mathlib) definitions for:
1. Exact symmetric `MXINT_w` EF21 contraction bounds under Continuous AbsMax and OCP `E8M0`.
2. Exact `MXFP_w` format specifications and EF21 crossover frontiers (`MXFP4-E2M1`,
   `MXFP6-E2M3`, `MXFP6-E3M2`, `MXFP8-E4M3`, `MXFP8-E2M5`).
3. Exact signed Kulisch integer dot-product accumulation and two's-complement width bounds.
4. Zero-free half-integer `MXINT_w` collapse and `E8M0` divergence thresholds.
5. Asymmetric `MXINT4 [-8, 7]` vs symmetric `MXINT4 [-7, 7]` AbsMax crossover and `E8M0`
   `7 vs 8` non-power-of-two scale cliff.
6. Exact integer block-split associativity and permutation invariance.
-/

namespace MxintMxfpSwar

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if x < 0 then -x else x

/-- Exact rational max of two rationals. -/
def ratMax (a b : Rat) : Rat :=
  if a ≤ b then b else a

/-- Finite sum over `Fin n` in `Rat`. -/
def finSum : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | _ + 1, f => finSum (fun i => f i.castSucc) + f (Fin.last _)

/-- Finite sum over `Fin n` excluding a distinguished index `i0`. -/
def finSumExcept {n : Nat} (i0 : Fin n) (f : Fin n → Rat) : Rat :=
  finSum (fun j => if j = i0 then 0 else f j)

/-- Squared Euclidean norm over `Fin n` in `Rat`. -/
def l2NormSq {n : Nat} (u : Fin n → Rat) : Rat :=
  finSum (fun i => u i * u i)

/-- Finite sum over `Fin n` in `Int`. -/
def intFinSum : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | _ + 1, f => intFinSum (fun i => f i.castSucc) + f (Fin.last _)

/-- Exact integer Kulisch dot product over `Fin n`. -/
def intDot {n : Nat} (x y : Fin n → Int) : Int :=
  intFinSum (fun i => x i * y i)

/-- Concatenation of two `Int`-valued block vectors of lengths `B1` and `B2`. -/
def appendVec {B1 B2 : Nat} (f : Fin B1 → Int) (g : Fin B2 → Int) : Fin (B1 + B2) → Int :=
  fun i =>
    if h : i.val < B1 then f ⟨i.val, h⟩
    else g ⟨i.val - B1, by omega⟩

/-- Bijectivity predicate in pure `Init` (zero Mathlib). -/
def IsBijective {α β : Type} (f : α → β) : Prop :=
  (∀ a1 a2, f a1 = f a2 → a1 = a2) ∧ (∀ b, ∃ a, f a = b)

/-! ### Section 1: Symmetric `MXINT_w` EF21 Contraction Definitions -/

/-- Maximum positive integer level `M = 2^(w - 1) - 1` of symmetric `MXINT_w`. -/
def mxintMax (w : Nat) : Nat :=
  2 ^ (w - 1) - 1

/-- Rational cast of `mxintMax w`. -/
def mxintMaxRat (w : Nat) : Rat :=
  ((mxintMax w : Nat) : Rat)

/-- Exact Continuous AbsMax worst-case EF21 defect for symmetric `MXINT_w`:
    `ω_AbsMax(w, B) = (B - 1) / (4 M^2 + B - 1)`. -/
def omegaMxintAbsMax (w B : Nat) : Rat :=
  ((B - 1 : Nat) : Rat) / (4 * mxintMaxRat w * mxintMaxRat w + ((B - 1 : Nat) : Rat))

/-- Exact OCP no-overflow `E8M0` worst-case EF21 defect for symmetric `MXINT_w`:
    `ω_E8M0(w, B) = B / (M^2 + B - 1)`. -/
def omegaMxintE8M0 (w B : Nat) : Rat :=
  (B : Rat) / (mxintMaxRat w * mxintMaxRat w + ((B - 1 : Nat) : Rat))

/-- Nearest-integer quantization error admissibility for symmetric `MXINT_w`
    containing `0` with unit integer spacing: every coordinate error satisfies
    `0 ≤ e_j ≤ 1/4` and `e_j ≤ u_j^2`. -/
def IsMxintErr {B : Nat} (u e : Fin B → Rat) : Prop :=
  ∀ j : Fin B, (0 : Rat) ≤ e j ∧ e j ≤ (1 / 4 : Rat) ∧ e j ≤ u j * u j

/-! ### Section 2: `MXFP_w` Specifications and Crossover Frontiers -/

/-- Exact rational parameters of a symmetric OCP `MXFP` codebook containing `0`:
    - `M`: maximum representable magnitude (`c_K`)
    - `c1`: smallest positive (subnormal) magnitude
    - `vHi`: worst normal-binade midpoint maximizing `e(v) / v^2` in the top binade
    - `eHi`: exact squared quantization error at `vHi`
    - `rhoNorm`: exact normal-binade relative error ceiling `1 / (2^(m+1) + 1)^2` -/
structure MxfpSpec where
  M : Rat
  c1 : Rat
  vHi : Rat
  eHi : Rat
  rhoNorm : Rat

/-- OCP `MXFP4-E2M1`: `M = 6`, `c1 = 1/2`, `vHi = 5`, `eHi = 1`, `ρ = 1/25`. -/
def mxfp4E2M1 : MxfpSpec :=
  { M := 6, c1 := 1 / 2, vHi := 5, eHi := 1, rhoNorm := 1 / 25 }

/-- OCP `MXFP6-E2M3`: `M = 15/2`, `c1 = 1/8`, `vHi = 17/4`, `eHi = 1/16`, `ρ = 1/289`. -/
def mxfp6E2M3 : MxfpSpec :=
  { M := 15 / 2, c1 := 1 / 8, vHi := 17 / 4, eHi := 1 / 16, rhoNorm := 1 / 289 }

/-- OCP `MXFP6-E3M2`: `M = 28`, `c1 = 1/16`, `vHi = 18`, `eHi = 4`, `ρ = 1/81`. -/
def mxfp6E3M2 : MxfpSpec :=
  { M := 28, c1 := 1 / 16, vHi := 18, eHi := 4, rhoNorm := 1 / 81 }

/-- OCP `MXFP8-E4M3`: `M = 448`, `c1 = 1/512`, `vHi = 272`, `eHi = 256`, `ρ = 1/289`. -/
def mxfp8E4M3 : MxfpSpec :=
  { M := 448, c1 := 1 / 512, vHi := 272, eHi := 256, rhoNorm := 1 / 289 }

/-- Finite `MXFP8-E2M5`: `M = 63/8`, `c1 = 1/32`, `vHi = 65/16`, `eHi = 1/256`, `ρ = 1/4225`. -/
def mxfp8E2M5 : MxfpSpec :=
  { M := 63 / 8, c1 := 1 / 32, vHi := 65 / 16, eHi := 1 / 256, rhoNorm := 1 / 4225 }

/-- Two-region quantization error law for any `MXFP` format: every coordinate is either
    normal (`e_j ≤ eHi` and `e_j ≤ rhoNorm * u_j^2`) or subnormal (`e_j ≤ (c1/2)^2` and `e_j ≤ u_j^2`). -/
def IsMxfpErr {B : Nat} (spec : MxfpSpec) (u e : Fin B → Rat) : Prop :=
  ∀ j : Fin B,
    (0 : Rat) ≤ e j ∧
    ((e j ≤ spec.eHi ∧ e j ≤ spec.rhoNorm * (u j * u j)) ∨
     (e j ≤ (spec.c1 / 2) * (spec.c1 / 2) ∧ e j ≤ u j * u j))

/-- Exact Continuous AbsMax worst-case EF21 defect for `MXFP` (2-branch closed form):
    `max(((B-1)*eHi)/(M^2 + (B-1)*vHi^2), ((B-1)*(c1/2)^2)/(M^2 + (B-1)*(c1/2)^2))`. -/
def omegaMxfpAbsMax (spec : MxfpSpec) (B : Nat) : Rat :=
  let bm1 : Rat := ((B - 1 : Nat) : Rat)
  let bNorm : Rat := (bm1 * spec.eHi) / (spec.M * spec.M + bm1 * (spec.vHi * spec.vHi))
  let c1h2 : Rat := (spec.c1 / 2) * (spec.c1 / 2)
  let bSub : Rat := (bm1 * c1h2) / (spec.M * spec.M + bm1 * c1h2)
  ratMax bNorm bSub

/-- Exact OCP no-overflow `E8M0` worst-case EF21 defect for `MXFP` (dominant 2-branch form):
    `max((eHi + (B-1)*(c1/2)^2)/(vHi^2 + (B-1)*(c1/2)^2), ((B-1)*(c1/2)^2)/((M/2)^2 + (B-1)*(c1/2)^2))`. -/
def omegaMxfpE8M0 (spec : MxfpSpec) (B : Nat) : Rat :=
  let bm1 : Rat := ((B - 1 : Nat) : Rat)
  let c1h2 : Rat := (spec.c1 / 2) * (spec.c1 / 2)
  let bHi : Rat := (spec.eHi + bm1 * c1h2) / (spec.vHi * spec.vHi + bm1 * c1h2)
  let mh : Rat := spec.M / 2
  let bLo : Rat := (bm1 * c1h2) / (mh * mh + bm1 * c1h2)
  ratMax bHi bLo

/-- Exact OCP `E8M0` worst-case EF21 defect for `MXFP4-E2M1`, including the intermediate
    midpoint branch `(t = 7/2, e(t) = 1/4, v = 1/4)`. -/
def omegaMxfp4E2M1E8M0 (B : Nat) : Rat :=
  let bm1 : Rat := ((B - 1 : Nat) : Rat)
  let bMid : Rat := ((1 / 4 : Rat) + bm1 * (1 / 16 : Rat)) / ((49 / 4 : Rat) + bm1 * (1 / 16 : Rat))
  ratMax (omegaMxfpE8M0 mxfp4E2M1 B) bMid

/-! ### Section 3: Exact Kulisch Accumulator Bit-Width Definitions -/

/-- Exact worst-case magnitude `B * (2^(w-1) - 1)^2` of a symmetric `MXINT_w` dot product. -/
def kulischSymMax (w B : Nat) : Int :=
  (B : Int) * ((mxintMax w : Int) * (mxintMax w : Int))

/-- Exact maximum value `B * (2^(w-1))^2` of an asymmetric two's-complement `MXINT_w` dot product. -/
def kulischAsymMax (w B : Nat) : Int :=
  (B : Int) * (((2 ^ (w - 1) : Nat) : Int) * ((2 ^ (w - 1) : Nat) : Int))

/-- Exact minimum value `-B * 2^(w-1) * (2^(w-1) - 1)` of an asymmetric `MXINT_w` dot product. -/
def kulischAsymMin (w B : Nat) : Int :=
  -((B : Int) * (((2 ^ (w - 1) : Nat) : Int) * (((2 ^ (w - 1) : Nat) : Int) - 1)))

/-- Signed `k`-bit two's-complement representability: `v ∈ [-2^(k-1), 2^(k-1) - 1]`. -/
def fitsSignedWidth (k : Nat) (v : Int) : Prop :=
  -(((2 ^ (k - 1) : Nat) : Int)) ≤ v ∧ v ≤ (((2 ^ (k - 1) : Nat) : Int)) - 1

/-- Vector lies in symmetric `MXINT_w` range `[-(2^(w-1)-1), 2^(w-1)-1]`. -/
def InSymRange {B : Nat} (w : Nat) (x : Fin B → Int) : Prop :=
  ∀ i : Fin B, -((mxintMax w : Nat) : Int) ≤ x i ∧ x i ≤ ((mxintMax w : Nat) : Int)

/-- Vector lies in asymmetric two's-complement `MXINT_w` range `[-2^(w-1), 2^(w-1)-1]`. -/
def InAsymRange {B : Nat} (w : Nat) (x : Fin B → Int) : Prop :=
  ∀ i : Fin B, -(((2 ^ (w - 1) : Nat) : Int)) ≤ x i ∧ x i ≤ (((2 ^ (w - 1) : Nat) : Int)) - 1

/-! ### Section 4: Zero-Free Half-Integer `MXINT_w` Collapse Definitions -/

/-- Maximum level `M = (2^w - 1) / 2` of zero-free half-integer `MXINT_w`. -/
def halfIntMax (w : Nat) : Rat :=
  ((2 ^ w - 1 : Nat) : Rat) / 2

/-- Unrescaled Continuous AbsMax EF21 defect of zero-free half-integer `MXINT_w`
    on `u = (M, 0, ..., 0)`: `(B - 1) / (2^w - 1)^2`. -/
def omegaHalfAbsMax (w B : Nat) : Rat :=
  ((B - 1 : Nat) : Rat) / (((2 ^ w - 1 : Nat) : Rat) * ((2 ^ w - 1 : Nat) : Rat))

/-- Optimal-rescaled Continuous AbsMax EF21 contraction rate of zero-free half-integer `MXINT_w`:
    `α_rescaled(w, B) = (2^w - 1)^2 / ((2^w - 1)^2 + B - 1)`. -/
def alphaHalfRescaled (w B : Nat) : Rat :=
  let d : Rat := ((2 ^ w - 1 : Nat) : Rat) * ((2 ^ w - 1 : Nat) : Rat)
  d / (d + ((B - 1 : Nat) : Rat))

/-- Unrescaled OCP `E8M0` EF21 defect of zero-free half-integer `MXINT_w`
    on `u = (M/2, 0, ..., 0)`: `(4B - 3) / (2^w - 1)^2` for `B ≥ 1`. -/
def omegaHalfE8M0 (w B : Nat) : Rat :=
  ((4 * B - 3 : Nat) : Rat) / (((2 ^ w - 1 : Nat) : Rat) * ((2 ^ w - 1 : Nat) : Rat))

/-- Exact integer `E8M0` divergence threshold `B_div^E8M0(w) = 4^(w-1) - 2^(w-1) + 1`. -/
def halfDivE8M0 (w : Nat) : Nat :=
  4 ^ (w - 1) - 2 ^ (w - 1) + 1

/-! ### Section 5: Asymmetric `MXINT4 [-8, 7]` vs Symmetric `[-7, 7]` Definitions -/

/-- Continuous AbsMax EF21 defect for symmetric `MXINT4 [-7, 7]` (`S = max|x|/7`). -/
def omegaMxint4SymAbsMax (B : Nat) : Rat :=
  ((B - 1 : Nat) : Rat) / (196 + ((B - 1 : Nat) : Rat))

/-- Continuous AbsMax EF21 defect for unsigned-scale asymmetric `MXINT4 [-8, 7]` (`S = max|x|/8`):
    `(1 + (B-1)/4) / (64 + (B-1)/4) = (B + 3) / (256 + B - 1)`. -/
def omegaMxint4AsymAbsMax (B : Nat) : Rat :=
  ((B + 3 : Nat) : Rat) / (256 + ((B - 1 : Nat) : Rat))

/-- Continuous AbsMax EF21 defect for signed-scale asymmetric `MXINT4 [-8, 7]`:
    `((B-1)/4) / (64 + (B-1)/4) = (B - 1) / (256 + B - 1)`. -/
def omegaMxint4AsymSignedAbsMax (B : Nat) : Rat :=
  ((B - 1 : Nat) : Rat) / (256 + ((B - 1 : Nat) : Rat))

/-- Uniform quantization MSE `Δ^2 / 12` for step size `Δ`. -/
def uniformStepMse (step : Rat) : Rat :=
  (step * step) / 12

end MxintMxfpSwar
