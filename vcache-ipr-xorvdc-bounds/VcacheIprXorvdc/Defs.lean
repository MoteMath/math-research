/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`VcacheIprXorvdc.Defs`)

Pure-`Init` (zero Mathlib) exact rational, integer, and natural-number definitions for:
1. Attention simplex weights, Inverse Participation Ratio (`IPR`), Effective Support (`N_eff`),
   and exact SR vs RNE output MSE decompositions and crossover thresholds.
2. Zero-carry XOR-VDC stratified stochastic rounding on `Fin (2^K)` (`bitrevNat`, `xorVdcFin`),
   discrete round-up indicators, and conditional variance identities.
3. Rank-1 attention sink simplex weights (`sinkWeights`) and bulk uniform weights.
4. Orthogonal Walsh–Hadamard transforms (`whtMat`), matrix-vector multiplication, and attention
   output operators (`attnOut`).
5. Sub-4-bit V-cache bit-packing (`INT16`, `INT4`, `INT2`, `5-trit/B Ternary`) and `128K`-context
   `int64` accumulator bounds.
-/

namespace VcacheIprXorvdc

/-! ### Basic Rational, Integer & Finite-Sum Utilities -/

def ratAbs (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then x else -x

def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f =>
    finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

def finSum {n : Nat} (f : Fin n → Rat) : Rat :=
  finSumAux n f

def finSumNatAux : (k : Nat) → (Fin k → Nat) → Nat
  | 0, _ => 0
  | k + 1, f =>
    finSumNatAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

def finSumNat {n : Nat} (f : Fin n → Nat) : Nat :=
  finSumNatAux n f

def finSumIntAux : (k : Nat) → (Fin k → Int) → Int
  | 0, _ => 0
  | k + 1, f =>
    finSumIntAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

def finSumInt {n : Nat} (f : Fin n → Int) : Int :=
  finSumIntAux n f

/-! ### Pillar 1: IPR, Effective Support & SR vs RNE Output MSE -/

/-- Inverse Participation Ratio `IPR(p) = ∑_j p_j^2`. -/
def ipr {L : Nat} (p : Fin L → Rat) : Rat :=
  finSum (fun j => p j * p j)

/-- Effective Support `N_eff(p) = 1 / IPR(p)`. -/
def neff {L : Nat} (p : Fin L → Rat) : Rat :=
  1 / ipr p

/-- Uniform attention weights `p_j = 1 / L` on `Fin L`. -/
def uniformWeights (L : Nat) : Fin L → Rat :=
  fun _ => 1 / (L : Rat)

/-- Peaked (one-hot) attention weights concentrated on token `j0`. -/
def peakedWeights (L : Nat) (j0 : Fin L) : Fin L → Rat :=
  fun j => if j = j0 then 1 else 0

/-- Exact i.i.d. Stochastic Rounding (SR) attention-output MSE:
    `∑_j p_j^2 * σ_SR^2`. -/
def srOutputMse {L : Nat} (p : Fin L → Rat) (sigmaSrSq : Rat) : Rat :=
  finSum (fun j => p j * p j * sigmaSrSq)

/-- Exact Round-to-Nearest-Even (RNE) attention-output MSE:
    `(∑_j p_j * μ_bias)^2 + ∑_j p_j^2 * σ_RNE^2`. -/
def rneOutputMse {L : Nat} (p : Fin L → Rat) (muBias sigmaRneSq : Rat) : Rat :=
  let b := finSum (fun j => p j * muBias)
  b * b + finSum (fun j => p j * p j * sigmaRneSq)

/-- Exact RNE-vs-SR phase transition threshold:
    `N_eff* = (σ_SR^2 - σ_RNE^2) / μ_bias^2`. -/
def neffThreshold (sigmaSrSq sigmaRneSq muBias : Rat) : Rat :=
  (sigmaSrSq - sigmaRneSq) / (muBias * muBias)

/-- Exact zero-mean IID uniform SR variance for step `Δ`: `Δ^2 / 6`. -/
def srUniformVar (delta : Rat) : Rat :=
  delta * delta / 6

/-- Exact zero-mean IID uniform RNE variance for step `Δ`: `Δ^2 / 12`. -/
def rneUniformVar (delta : Rat) : Rat :=
  delta * delta / 12

/-! ### Pillar 1/2: Zero-Carry XOR-VDC Stratified SR on `Fin (2^K)` -/

/-- Exact `K`-bit bit-reversal of a natural number `x`. -/
def bitrevNat : Nat → Nat → Nat
  | 0, _ => 0
  | K + 1, x => (x % 2) * 2 ^ K + bitrevNat K (x / 2)

theorem bitrevNat_lt (K x : Nat) : bitrevNat K x < 2 ^ K := by
  induction K generalizing x with
  | zero => simp [bitrevNat]
  | succ K ih =>
    simp only [bitrevNat, Nat.pow_succ]
    have h1 : bitrevNat K (x / 2) < 2 ^ K := ih (x / 2)
    have h2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases h2 with h2 | h2 <;> simp [h2] <;> omega

/-- Zero-carry XOR Van der Corput threshold `u_j = u_0 ⊕ bitrev_K(j)`. -/
def xorVdcNat (K u0 j : Nat) : Nat :=
  u0 ^^^ bitrevNat K j

theorem xorVdcNat_lt (K u0 j : Nat) (hu0 : u0 < 2 ^ K) : xorVdcNat K u0 j < 2 ^ K := by
  exact Nat.xor_lt_two_pow hu0 (bitrevNat_lt K j)

/-- Zero-carry XOR-VDC permutation as an endomorphism of `Fin (2^K)`. -/
def xorVdcFin (K : Nat) (u0 : Fin (2 ^ K)) (j : Fin (2 ^ K)) : Fin (2 ^ K) :=
  ⟨xorVdcNat K u0.val j.val, xorVdcNat_lt K u0.val j.val u0.isLt⟩

/-- Discrete SR round-up indicator `1_{u < r}` in `{0, 1}`. -/
def srRoundUpBit (r u : Nat) : Nat :=
  if u < r then 1 else 0

/-- Half-bin centered rational threshold `t_j = (2 * xorVdc(j) + 1) / 2^(K+1)` in `(0, 1)`. -/
def xorVdcCenteredThresh (K : Nat) (u0 j : Fin (2 ^ K)) : Rat :=
  ((2 * (xorVdcFin K u0 j).val + 1 : Nat) : Rat) / ((2 ^ (K + 1) : Nat) : Rat)

/-- Exact conditional second moment `E[e^2 | u] = (u^3 + (1 - u)^3) / 3` for uniform `f ∈ [0, 1)`. -/
def condSecondMoment (u : Rat) : Rat :=
  (u * u * u + (1 - u) * (1 - u) * (1 - u)) / 3

/-- Exact conditional mean `E[e | u] = 1/2 - u` for uniform `f ∈ [0, 1)`. -/
def condMean (u : Rat) : Rat :=
  1 / 2 - u

/-- Exact conditional variance `Var(e | u) = E[e^2 | u] - (E[e | u])^2`. -/
def condVar (u : Rat) : Rat :=
  condSecondMoment u - condMean u * condMean u

/-! ### Pillar 1: Rank-1 Attention Sink Weights -/

/-- Rank-1 attention sink distribution: token `0` carries mass `α`, and the remaining
    `L - 1` bulk tokens uniformly share `(1 - α) / (L - 1)`. -/
def sinkWeights (L : Nat) (alpha : Rat) : Fin L → Rat :=
  fun j => if j.val = 0 then alpha else (1 - alpha) / ((L - 1 : Nat) : Rat)

/-! ### Pillar 2: Rank-1 Mean Split & Walsh–Hadamard Orthogonality -/

/-- Matrix-vector product `(H v)_i = ∑_c H_{i,c} v_c`. -/
def matVecMul {d : Nat} (H : Fin d → Fin d → Rat) (v : Fin d → Rat) : Fin d → Rat :=
  fun i => finSum (fun c => H i c * v c)

/-- Matrix transpose `(H^T)_{i,j} = H_{j,i}`. -/
def matTranspose {d : Nat} (H : Fin d → Fin d → Rat) : Fin d → Fin d → Rat :=
  fun i j => H j i

/-- Multi-token attention output `(attnOut p V)_c = ∑_j p_j V_{j,c}`. -/
def attnOut {L d : Nat} (p : Fin L → Rat) (V : Fin L → Fin d → Rat) : Fin d → Rat :=
  fun c => finSum (fun j => p j * V j c)

/-- Scaled orthogonality predicate `H^T H = d * I_d`. -/
def isScaledOrthogonal {d : Nat} (H : Fin d → Fin d → Rat) : Prop :=
  ∀ a b : Fin d, finSum (fun i => H i a * H i b) = if a = b then (d : Rat) else 0

/-- Recursive Sylvester Walsh–Hadamard matrix `H_{2^m}` of size `2^m × 2^m` with entries in `{-1, +1}`. -/
def whtMat : (m : Nat) → Fin (2 ^ m) → Fin (2 ^ m) → Rat
  | 0, _, _ => 1
  | m + 1, i, j =>
    let half := 2 ^ m
    let i0 : Fin (2 ^ m) := ⟨i.val % half, Nat.mod_lt _ (Nat.two_pow_pos m)⟩
    let j0 : Fin (2 ^ m) := ⟨j.val % half, Nat.mod_lt _ (Nat.two_pow_pos m)⟩
    let sgn : Rat := if i.val < half ∨ j.val < half then 1 else -1
    sgn * whtMat m i0 j0

/-! ### Pillar 3: Sub-4-Bit V-Cache Bit-Packing & Exact `int64` Accumulator Bounds -/

def vcacheHeads : Nat := 32
def vcacheCtx128K : Nat := 131072
def vcacheHeadDim : Nat := 128

def vcacheBytesPerTokenInt16 : Nat := 256
def vcacheBytesPerTokenInt4 : Nat := 64
def vcacheBytesPerTokenInt2 : Nat := 32
def vcacheBytesPerTokenTernary : Nat := 28

/-- Total V-cache VRAM in MiB for `H = 32, L = 131072, D = 128`. -/
def vcacheMiB (bytesPerToken : Nat) : Nat :=
  vcacheHeads * vcacheCtx128K * bytesPerToken / (1024 * 1024)

/-- Exact base-3 packing of 5 ternary trits (`Fin 3`) into a single byte (`< 243 < 256`). -/
def pack5Trits (t0 t1 t2 t3 t4 : Fin 3) : Nat :=
  t0.val + 3 * (t1.val + 3 * (t2.val + 3 * (t3.val + 3 * t4.val)))

/-- Exact inverse unpacking of a packed 5-trit byte back into 5 `Fin 3` trits. -/
def unpack5Trits (b : Nat) : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 :=
  (⟨b % 3, Nat.mod_lt _ (by decide)⟩,
   ⟨(b / 3) % 3, Nat.mod_lt _ (by decide)⟩,
   ⟨(b / 9) % 3, Nat.mod_lt _ (by decide)⟩,
   ⟨(b / 27) % 3, Nat.mod_lt _ (by decide)⟩,
   ⟨(b / 81) % 3, Nat.mod_lt _ (by decide)⟩)

/-- Signed 64-bit integer maximum `2^63 - 1`. -/
def int64Max : Int := 2 ^ 63 - 1

/-- Signed 64-bit integer minimum `-2^63`. -/
def int64Min : Int := -(2 ^ 63)

end VcacheIprXorvdc
