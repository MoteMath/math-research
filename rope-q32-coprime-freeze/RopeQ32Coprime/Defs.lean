/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`RopeQ32Coprime.Defs`)

Pure-`Init` (zero Mathlib) exact rational and natural-number definitions for:
1. Binary floating-point binade ULP, integer RNE quantization, and FP16 `+Inf` overflow cliff.
2. High-frequency (`θ_0 = 1` rad/token) random-phase horizon.
3. Exact `Q32` modular integer phase `φ(m) = (m * ω) mod 2^32`.
4. Exact OCP `MXFP4-E2M1` and `FP8-E4M3` rotation quantizers on `[-1, 1]`.
5. Exact `2 × 2` rotation matrices, relative-position attention score, and rational Cayley rotations.
-/

namespace RopeQ32Coprime

/-! ### Basic Rational & Finite-Sum Utilities -/

def ratAbs (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then x else -x

def pow2Rat (k : Nat) : Rat :=
  ((2 ^ k : Nat) : Rat)

def invPow2Rat (k : Nat) : Rat :=
  1 / pow2Rat k

def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f =>
    finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

def finSum {n : Nat} (f : Fin n → Rat) : Rat :=
  finSumAux n f

/-! ### Pillar 1: Binary Float Binade ULP, RNE Quantization & FP16 Overflow Cliff -/

/-- Exact integer ULP in binade `[2^k, 2^(k+1))` for a binary floating-point format
    with `p` explicit mantissa bits (`BF16: p = 7`, `FP16: p = 10`, `FP32: p = 23`),
    when `k ≥ p`. -/
def binadeUlp (p k : Nat) : Nat :=
  2 ^ (k - p)

/-- Exact IEEE-754 Round-to-Nearest-Even (RNE) rounding of an integer `m` in binade
    `[2^k, 2^(k+1))` for a `p`-mantissa-bit binary floating-point format.
    When `k ≤ p`, every integer in the binade is exact (`binadeRneNat p k m = m`).
    When `k > p`, `u = 2^(k - p)` and `h = 2^(k - p - 1)` is the exact half-ULP. -/
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

/-- Largest finite normal value of IEEE-754 binary16 (`FP16`, `E5M10`, max exponent `15`):
    `(2 - 2^-10) * 2^15 = 2^16 - 2^5 = 65504`. -/
def fp16MaxNormal : Nat := (2 ^ 11 - 1) * 2 ^ 5

/-- ULP in the top finite binade `[2^15, 2^16)` of `FP16`: `2^(15 - 10) = 32`. -/
def fp16TopUlp : Nat := binadeUlp 10 15

/-- Exact `FP16` RNE overflow-to-`+Inf` threshold: `65504 + 16 = 65520`. -/
def fp16OverflowThreshold : Nat := fp16MaxNormal + fp16TopUlp / 2

/-- High-frequency (`θ_0 = 1` rad/token) exact first random-phase token position
    for a `p`-mantissa-bit binary floating-point format: `2^(p + 1) + 1`. -/
def highFreqRandomPhasePos (p : Nat) : Nat := 2 ^ (p + 1) + 1

/-! ### Pillar 1 & 3: Exact Modular Integer Phase (`Q32`) -/

/-- Modular phase modulus for `b`-bit unsigned modular phase (`b = 32` gives `2^32`). -/
def modPhase (b omega m : Nat) : Nat :=
  (m * omega) % (2 ^ b)

/-- `Q32` modulus `2^32 = 4294967296`. -/
def q32Mod : Nat := 2 ^ 32

/-- Exact `Q32` modular integer phase `φ(m) = (m * ω) mod 2^32`. -/
def q32Phase (omega m : Nat) : Nat :=
  modPhase 32 omega m

/-- `Q32` modular phase map as an endomorphism of `Fin (2^32)`. -/
def q32PhaseFin (omega : Nat) (m : Fin q32Mod) : Fin q32Mod :=
  ⟨q32Phase omega m.val, Nat.mod_lt _ (by decide)⟩

/-! ### Pillar 2A: Exact `MXFP4-E2M1` and `FP8-E4M3` Rotation Quantizers -/

/-- Exact `MXFP4-E2M1` (with `E8M0` block scale `2^-2`) quantizer on `[0, 1]`,
    mapping onto `{0, 1/8, 1/4, 3/8, 1/2, 3/4, 1}` with exact midpoint boundaries
    `1/16, 3/16, 5/16, 7/16, 5/8, 7/8` (bit-identical to `py_quant_q30_mxfp4_e2m1`). -/
def quantMXFP4Nonneg (x : Rat) : Rat :=
  if x < 1 / 16 then 0
  else if x < 3 / 16 then 1 / 8
  else if x < 5 / 16 then 1 / 4
  else if x < 7 / 16 then 3 / 8
  else if x < 5 / 8 then 1 / 2
  else if x < 7 / 8 then 3 / 4
  else 1

/-- Signed `MXFP4-E2M1` quantizer on `[-1, 1]`. -/
def quantMXFP4 (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then quantMXFP4Nonneg x else -quantMXFP4Nonneg (-x)

/-- Round `x ∈ [0, 1]` to the nearest multiple of `step = 1 / 2^k` (RNE on `8..16` grid).
    Specifically, for `x ∈ [1/2, 1]`, OCP `FP8-E4M3` has ULP `1/16` and representable
    values `{8/16, 9/16, 10/16, 11/16, 12/16, 13/16, 14/16, 15/16, 16/16}` with
    midpoints `17/32, 19/32, 21/32, 23/32, 25/32, 27/32, 29/32, 31/32`. -/
def quantFP8E4M3Top (x : Rat) : Rat :=
  if x ≤ 17 / 32 then 8 / 16
  else if x < 19 / 32 then 9 / 16
  else if x ≤ 21 / 32 then 10 / 16
  else if x < 23 / 32 then 11 / 16
  else if x ≤ 25 / 32 then 12 / 16
  else if x < 27 / 32 then 13 / 16
  else if x ≤ 29 / 32 then 14 / 16
  else if x < 31 / 32 then 15 / 16
  else 1

/-- Exact RNE rounding of `x ≥ 0` onto a uniform grid of step `u > 0`
    (used for each lower binade of OCP `FP8-E4M3`). -/
def rneUniformStep (n : Nat) (x : Rat) : Rat :=
  let s := ((n : Rat) * x)
  let q := s.floor
  let r := s - (q : Rat)
  let qR :=
    if r < 1 / 2 then q
    else if (1 / 2 : Rat) < r then q + 1
    else if q % 2 = 0 then q else q + 1
  (qR : Rat) / (n : Rat)

/-- Exact OCP `FP8-E4M3` quantizer on `[0, 1]` across all normal binades
    `[2^-6, 1]` and subnormals `[0, 2^-6)` (`step = 2^-9 = 1/512`). -/
def quantFP8E4M3Nonneg (x : Rat) : Rat :=
  if 31 / 64 ≤ x then quantFP8E4M3Top x
  else if 1 / 4 ≤ x then rneUniformStep 32 x
  else if 1 / 8 ≤ x then rneUniformStep 64 x
  else if 1 / 16 ≤ x then rneUniformStep 128 x
  else if 1 / 32 ≤ x then rneUniformStep 256 x
  else rneUniformStep 512 x

/-- Signed OCP `FP8-E4M3` quantizer on `[-1, 1]`. -/
def quantFP8E4M3 (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then quantFP8E4M3Nonneg x else -quantFP8E4M3Nonneg (-x)

/-! ### Pillar 2B & Cayley Group: `2 × 2` Rotations & Rational Cayley Parameterization -/

/-- A `2 × 2` rotation-form matrix `[[c, -s], [s, c]]` over `Rat`. -/
structure Rot2 where
  c : Rat
  s : Rat
  deriving DecidableEq

def Rot2.id : Rot2 := ⟨1, 0⟩

def Rot2.transpose (R : Rot2) : Rot2 := ⟨R.c, -R.s⟩

def Rot2.mul (A B : Rot2) : Rot2 :=
  ⟨A.c * B.c - A.s * B.s, A.s * B.c + A.c * B.s⟩

def Rot2.add (A B : Rot2) : Rot2 :=
  ⟨A.c + B.c, A.s + B.s⟩

def Rot2.sub (A B : Rot2) : Rot2 :=
  ⟨A.c - B.c, A.s - B.s⟩

def Rot2.apply (R : Rot2) (v : Rat × Rat) : Rat × Rat :=
  (R.c * v.1 - R.s * v.2, R.s * v.1 + R.c * v.2)

def dot2 (u v : Rat × Rat) : Rat :=
  u.1 * v.1 + u.2 * v.2

def normSq2 (v : Rat × Rat) : Rat :=
  v.1 * v.1 + v.2 * v.2

def l1Norm2 (v : Rat × Rat) : Rat :=
  ratAbs v.1 + ratAbs v.2

/-- RoPE `2D` attention logit `q^T R_m^T R_n k = ⟨R_m q, R_n k⟩`. -/
def rotScore (q k : Rat × Rat) (Rm Rn : Rot2) : Rat :=
  dot2 (Rm.apply q) (Rn.apply k)

/-- Exact relative-position `2D` attention logit `q^T R_{n-m} k`. -/
def relScore (q k : Rat × Rat) (Rrel : Rot2) : Rat :=
  dot2 q (Rrel.apply k)

/-- Rational Cayley cosine `c(t) = (1 - t^2) / (1 + t^2)`. -/
def cayleyCos (t : Rat) : Rat :=
  (1 - t * t) / (1 + t * t)

/-- Rational Cayley sine `s(t) = 2t / (1 + t^2)`. -/
def cayleySin (t : Rat) : Rat :=
  (2 * t) / (1 + t * t)

/-- Rational Cayley rotation matrix `R_Cayley(t) ∈ SO(2, Q)`. -/
def cayleyRot (t : Rat) : Rot2 :=
  ⟨cayleyCos t, cayleySin t⟩

end RopeQ32Coprime
