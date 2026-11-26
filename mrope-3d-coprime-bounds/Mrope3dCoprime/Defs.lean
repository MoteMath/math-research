/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Pure-`Init` Definitions for 3D Multimodal `mRoPE` Coprime & Spectral-Resolution Bounds

Zero Mathlib, zero floating-point approximations, zero `native_decide`.
All definitions operate purely over `Nat`, `Int`, and `Rat` from Lean 4's `Init`.
-/

namespace Mrope3dCoprime

/-! ### Rational Arithmetic & Finite Sum Primitives -/

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then x else -x

/-- Exact dyadic power `2^k` as a `Rat`. -/
def pow2Rat (k : Nat) : Rat :=
  ((2 ^ k : Nat) : Rat)

/-- Exact inverse dyadic power `2^{-k} = 1 / 2^k` as a `Rat`. -/
def invPow2Rat (k : Nat) : Rat :=
  (1 : Rat) / pow2Rat k

/-- Exact natural-number power `x^k` over `Rat`. -/
def ratPow (x : Rat) : Nat → Rat
  | 0 => 1
  | k + 1 => ratPow x k * x

/-- Helper for finite sums over `Fin k`. -/
def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f => finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum `∑_{j : Fin n} f j` over `Rat`. -/
def finSum {n : Nat} (f : Fin n → Rat) : Rat :=
  finSumAux n f

/-- Exact finite inner product `∑_{j : Fin n} a j * b j`. -/
def dotProd {n : Nat} (a b : Fin n → Rat) : Rat :=
  finSum (fun j => a j * b j)

/-- Exact squared Euclidean norm `∑_{j : Fin n} (a j)^2`. -/
def l2NormSq {n : Nat} (a : Fin n → Rat) : Rat :=
  dotProd a a

/-- Minimum of three natural numbers. -/
def min3 (a b c : Nat) : Nat :=
  min a (min b c)

/-! ### Pillar 1 & 2: Separable vs Coupled 3D `mRoPE` Attention Kernels -/

/-- Sum of rotary pair cosines along a single axis with `P` pairs. -/
def sepAxisSum (P : Nat) (c : Fin P → Int → Rat) (Δ : Int) : Rat :=
  finSum (fun k => c k Δ)

/-- Normalized separable 3D `mRoPE` attention kernel splitting `P = PT + PH + PW` rotary pairs
    independently across `(T, H, W)`. -/
def sep3DKernel (PT PH PW : Nat)
    (cT : Fin PT → Int → Rat)
    (cH : Fin PH → Int → Rat)
    (cW : Fin PW → Int → Rat)
    (dT dH dW : Int) : Rat :=
  (sepAxisSum PT cT dT + sepAxisSum PH cH dH + sepAxisSum PW cW dW) /
    ((PT + PH + PW : Nat) : Rat)

/-- Exact quarter-turn cosine `cos(π m / 2) ∈ {-1, 0, 1}` over `Rat`. -/
def cosQ4 (m : Int) : Rat :=
  match m % 4 with
  | 0 => 1
  | 2 => -1
  | _ => 0

/-- Exact quarter-turn sine `sin(π m / 2) ∈ {-1, 0, 1}` over `Rat`. -/
def sinQ4 (m : Int) : Rat :=
  match m % 4 with
  | 1 => 1
  | 3 => -1
  | _ => 0

/-- General coupled 3D `mRoPE` kernel where every pair `k : Fin P` depends on all three offsets
    `(dT, dH, dW)`. -/
def coupled3DGeneral (P : Nat) (c : Fin P → Int → Int → Int → Rat) (dT dH dW : Int) : Rat :=
  finSum (fun k => c k dT dH dW) / (P : Rat)

/-- Coupled 3D `mRoPE` kernel using quarter-turn rotary phase
    `φ_k(dT, dH, dW) = dT * ωT_k + dH * ωH_k + dW * ωW_k`. -/
def coupled3DKernelQ4 (P : Nat) (ωT ωH ωW : Fin P → Int) (dT dH dW : Int) : Rat :=
  finSum (fun k => cosQ4 (dT * ωT k + dH * ωH k + dW * ωW k)) / (P : Rat)

/-- Full 64-pair `Z_4^3` coupled frequency lattice (`4 × 4 × 4 = 64` pairs, matching Qwen2-VL `d = 128`). -/
def ωT64 (k : Fin 64) : Int := (k.val / 16 : Nat)
def ωH64 (k : Fin 64) : Int := ((k.val / 4) % 4 : Nat)
def ωW64 (k : Fin 64) : Int := (k.val % 4 : Nat)

/-- 27-pair all-nonzero-axis `{1, 2, 3}^3` coupled frequency lattice where every pair
    actively rotates on all three axes `(T, H, W)`. -/
def ωT27 (k : Fin 27) : Int := (k.val / 9 + 1 : Nat)
def ωH27 (k : Fin 27) : Int := ((k.val / 3) % 3 + 1 : Nat)
def ωW27 (k : Fin 27) : Int := (k.val % 3 + 1 : Nat)

/-! ### Pillar 1: IEEE-754 RNE `BF16` Cosine Freeze & Geometric Resolution Gap -/

/-- Exact IEEE-754 RNE condition for `x ≤ 1` to snap to `1.0` in a binary format with `m`
    explicit significand bits: the predecessor of `1.0` is `1 - 2^{-(m+1)}` (odd significand),
    and `1.0` has even significand `2^m`, so the tie-to-even midpoint is `1 - 2^{-(m+2)}`. -/
def rneSnapsToOne (m : Nat) (x : Rat) : Prop :=
  1 - invPow2Rat (m + 2) ≤ x ∧ x ≤ 1

/-- `BF16` (`m = 7` explicit mantissa bits) RNE snap-to-one predicate (`[511/512, 1]`). -/
def bf16SnapsToOne (x : Rat) : Prop :=
  rneSnapsToOne 7 x

/-- Local second-order spatial resolution `(1/2) ∑_{k ∈ W} θ_k^2` for contiguous `mRoPE`
    Width allocation (`pairs 40..63`, 24 pairs) with squared frequency step ratio `q = b^{-2/64}`. -/
def geomResContigW (θ0sq q : Rat) : Rat :=
  (1 / 2 : Rat) * finSum (fun j : Fin 24 => θ0sq * ratPow q (40 + j.val))

/-- Local second-order spatial resolution `(1/2) ∑_{k ∈ W} θ_k^2` for round-robin stride-3
    interleaved Width allocation (`pairs 2, 5, 8, ..., 71`, 24 pairs). -/
def geomResInterleavedStride3 (θ0sq q : Rat) : Rat :=
  (1 / 2 : Rat) * finSum (fun j : Fin 24 => θ0sq * ratPow q (2 + 3 * j.val))

/-- Exact 64-pair Qwen3-VL interleaved `(16, 24, 24)` Width pair indices inside `0..63`:
    `2, 5, 8, ..., 47` (16 triples) followed by `49, 51, ..., 63` (8 alternating H/W pairs). -/
def qwen3InterleavedWIdx (j : Fin 24) : Nat :=
  if j.val < 16 then 2 + 3 * j.val else 49 + 2 * (j.val - 16)

/-- Local second-order spatial resolution `(1/2) ∑_{k ∈ W} θ_k^2` for Qwen3-VL interleaved
    `(16, 24, 24)` Width allocation. -/
def geomResQwen3InterleavedW (θ0sq q : Rat) : Rat :=
  (1 / 2 : Rat) * finSum (fun j : Fin 24 => θ0sq * ratPow q (qwen3InterleavedWIdx j))

/-! ### Pillar 3: `Q32` Modular 3D Phase & Cross-Modal `BF16` / `FP16` Phase Drift -/

/-- Modulus `2^32` for `Q32` unsigned 32-bit modular phase arithmetic. -/
def Q32_MOD : Int := 2 ^ 32

/-- Exact 3D modular integer phase `(T * ωT + H * ωH + W * ωW) mod 2^32`. -/
def q32Phase (ωT ωH ωW T H W : Int) : Int :=
  (T * ωT + H * ωH + W * ωW) % Q32_MOD

/-- Exact modular phase difference `(φ2 - φ1) mod 2^32`. -/
def q32PhaseDiff (φ2 φ1 : Int) : Int :=
  (φ2 - φ1) % Q32_MOD

/-- Exact ULP spacing `2^e / 2^p = 2^{e - p}` at binade `[2^e, 2^{e+1})` for a binary
    floating-point format with `p` explicit mantissa bits. -/
def fpUlpAtPow2 (p e : Nat) : Rat :=
  pow2Rat e / pow2Rat p

/-- Exact IEEE-754 RNE snap-to-`2^e` interval for `e ≥ 1, p ≥ 1`:
    since `2^e` has even significand `2^p`, ties at both `2^e - ulp(2^{e-1})/2` and
    `2^e + ulp(2^e)/2` round to `2^e`. -/
def rneSnapsToPow2 (p e : Nat) (x : Rat) : Prop :=
  pow2Rat e - fpUlpAtPow2 p (e - 1) / 2 ≤ x ∧ x ≤ pow2Rat e + fpUlpAtPow2 p e / 2

/-- Exact IEEE-754 `FP16` (`e_max = 15, p = 10`) maximum finite value `(2 - 2^{-10}) * 2^{15} = 65504`. -/
def FP16_MAX : Rat := 65504

/-- Exact `FP16` overflow predicate (`x > 65504`). -/
def fp16Overflows (x : Rat) : Prop :=
  FP16_MAX < x

end Mrope3dCoprime
