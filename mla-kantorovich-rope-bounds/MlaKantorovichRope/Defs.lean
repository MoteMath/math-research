/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions for `mla-kantorovich-rope-bounds`

Pure-`Init` (zero Mathlib) exact rational and integer definitions for:
1. Finite-dimensional `Rat` vector/matrix operations (`finSum`, `dot`, `normSq`, `matVec`,
   `matTranspose`, `matMul`, `matId`, `diagMat`, `diagInv`).
2. Bilinear absorbed-MLA Kantorovich spectral leakage and diagonal preconditioning.
3. Decoupled NoPE + RoPE mixed-precision bit budgets and distortion crossover ratios.
4. Parseval tight-frame multi-head interference and Walsh-Hadamard orthogonal head frames.
5. Brahmagupta-Fibonacci exact Pythagorean `R = 1105` 2D RoPE rotations.
6. Sub-byte MLA per-token memory footprints and compression ratios vs BF16 MHA / BF16 MLA.
-/

namespace MlaKantorovichRope

/-- Exact finite sum over `Fin n` in `Rat`. -/
def finSum : (n : Nat) → (Fin n → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => finSum n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

/-- Standard Euclidean inner product on `Rat^n`. -/
def dot {n : Nat} (u v : Fin n → Rat) : Rat :=
  finSum n (fun i => u i * v i)

/-- Squared Euclidean norm on `Rat^n`. -/
def normSq {n : Nat} (v : Fin n → Rat) : Rat :=
  dot v v

/-- Matrix-vector product `A * x`. -/
def matVec {m n : Nat} (A : Fin m → Fin n → Rat) (x : Fin n → Rat) : Fin m → Rat :=
  fun i => finSum n (fun j => A i j * x j)

/-- Matrix transpose `A^T`. -/
def matTranspose {m n : Nat} (A : Fin m → Fin n → Rat) : Fin n → Fin m → Rat :=
  fun j i => A i j

/-- Matrix-matrix product `A * B`. -/
def matMul {m k n : Nat} (A : Fin m → Fin k → Rat) (B : Fin k → Fin n → Rat) : Fin m → Fin n → Rat :=
  fun i j => finSum k (fun r => A i r * B r j)

/-- `n × n` identity matrix over `Rat`. -/
def matId (n : Nat) : Fin n → Fin n → Rat :=
  fun i j => if i = j then 1 else 0

/-- Diagonal matrix `diag(d)` over `Rat`. -/
def diagMat {n : Nat} (d : Fin n → Rat) : Fin n → Fin n → Rat :=
  fun i j => if i = j then d i else 0

/-- Inverse diagonal matrix `diag(d^{-1})` over `Rat`. -/
def diagInv {n : Nat} (d : Fin n → Rat) : Fin n → Fin n → Rat :=
  fun i j => if i = j then (d i)⁻¹ else 0

/-- Left-inverse predicate `M_inv * M = I_n`. -/
def isLeftInverse {n : Nat} (M_inv M : Fin n → Fin n → Rat) : Prop :=
  matMul M_inv M = matId n

/-- Orthogonality predicate `U^T * U = I_n`. -/
def isOrthogonal {n : Nat} (U : Fin n → Fin n → Rat) : Prop :=
  matMul (matTranspose U) U = matId n

/-- Kantorovich spectral amplification factor `(κ + κ^{-1})^2 / 4`. -/
def kantorovichFactor (κ : Rat) : Rat :=
  ((κ + κ⁻¹) * (κ + κ⁻¹)) / 4

/-- Bilinear isotropic noise-variance objective after diagonal scaling `D_j^2 = dSq j`:
    `(∑ w_j^2 / dSq_j) * (∑ dSq_j * γ_j^2)`. -/
def bilinearWeightedCost {n : Nat} (w γ dSq : Fin n → Rat) : Rat :=
  finSum n (fun j => w j * w j / dSq j) * finSum n (fun j => dSq j * γ j * γ j)

/-- Unbalanced (`D = I`) bilinear noise-variance product `(∑ w_j^2) * (∑ γ_j^2)`. -/
def unbalancedCost {n : Nat} (w γ : Fin n → Rat) : Rat :=
  finSum n (fun j => w j * w j) * finSum n (fun j => γ j * γ j)

/-- Extremal 2-level query spectrum `(σ_min, σ_max)`. -/
def twoLevelW (σmin σmax : Rat) : Fin 2 → Rat :=
  fun i => if i.val = 0 then σmin else σmax

/-- Extremal 2-level reciprocal latent spectrum `(σ_min^{-1}, σ_max^{-1})`. -/
def twoLevelGamma (σmin σmax : Rat) : Fin 2 → Rat :=
  fun i => if i.val = 0 then σmin⁻¹ else σmax⁻¹

/-- Exact inverse power of four `4^{-b}` in `Rat`. -/
def invPow4Rat (b : Nat) : Rat :=
  (1 : Rat) / ((4 ^ b : Nat) : Rat)

/-- Total per-token KV bit budget `d_c * b_c + d_R * b_R`. -/
def mlaBitBudget (d_c d_R b_c b_R : Nat) : Nat :=
  d_c * b_c + d_R * b_R

/-- Decoupled NoPE + RoPE quantization distortion `α_c * 4^{-b_c} + α_R * 4^{-b_R}`. -/
def mlaDistortion (α_c α_R : Rat) (b_c b_R : Nat) : Rat :=
  α_c * invPow4Rat b_c + α_R * invPow4Rat b_R

/-- Exact rational sensitivity crossover threshold `(4^{-b_c} - 4^{-b_c'}) / (4^{-b_R'} - 4^{-b_R})`. -/
def crossoverThreshold (b_c b_R b_c' b_R' : Nat) : Rat :=
  (invPow4Rat b_c - invPow4Rat b_c') / (invPow4Rat b_R' - invPow4Rat b_R)

/-- Simultaneous `H`-head total squared logit distortion `∑_{h=0}^{H-1} ⟨w_h, e⟩^2`. -/
def multiheadDistSq {H d_c : Nat} (W : Fin H → Fin d_c → Rat) (e : Fin d_c → Rat) : Rat :=
  normSq (matVec W e)

/-- Parseval tight-frame condition `W^T W = c * I_{d_c}`. -/
def isTightFrame {H d_c : Nat} (W : Fin H → Fin d_c → Rat) (c : Rat) : Prop :=
  matMul (matTranspose W) W = fun i j => if i = j then c else 0

/-- Row-orthogonal frame condition `W W^T = s * I_H`. -/
def isRowOrthogonal {H d_c : Nat} (W : Fin H → Fin d_c → Rat) (s : Rat) : Prop :=
  matMul W (matTranspose W) = fun i j => if i = j then s else 0

/-- Coherent rank-1 Rademacher head matrix `W_{h,j} = 1`. -/
def coherentHeads (H d_c : Nat) : Fin H → Fin d_c → Rat :=
  fun _ _ => 1

/-- All-ones Rademacher error vector `z_j = 1`. -/
def allOnesVec (d_c : Nat) : Fin d_c → Rat :=
  fun _ => 1

/-- Exact recursive Walsh-Hadamard sign entry `H_{2^k}(i, j) ∈ {-1, +1}`. -/
def walshEntry : Nat → Nat → Nat → Rat
  | 0, _, _ => 1
  | k + 1, i, j =>
      (if i % 2 = 1 ∧ j % 2 = 1 then (-1 : Rat) else 1) * walshEntry k (i / 2) (j / 2)

/-- First `H` rows of the `2^k × 2^k` Walsh-Hadamard matrix. -/
def walshHeads (k H : Nat) : Fin H → Fin (2 ^ k) → Rat :=
  fun h j => walshEntry k h.val j.val

/-- Exact rational 2D RoPE rotation matrix `[[c/R, -s/R], [s/R, c/R]]`. -/
def ropeRotMat (c s R : Rat) : Fin 2 → Fin 2 → Rat :=
  fun i j =>
    if i.val = 0 then
      if j.val = 0 then c / R else -(s / R)
    else
      if j.val = 0 then s / R else c / R

/-- Apply exact rational 2D RoPE rotation to `v : Fin 2 → Rat`. -/
def ropeApply (c s R : Rat) (v : Fin 2 → Rat) : Fin 2 → Rat :=
  matVec (ropeRotMat c s R) v

/-- Four primitive Brahmagupta-Fibonacci Pythagorean pairs with hypotenuse `R = 1105 = 5 * 13 * 17`. -/
def pythPrimitive1105 : List (Nat × Nat) :=
  [(1104, 47), (1073, 264), (943, 576), (817, 744)]

/-- All 10 verified Wave 7C campaign Pythagorean RoPE pairs sharing denominator `R = 1105`. -/
def pythCampaign1105 : List (Nat × Nat) :=
  [(1105, 0), (1104, 47), (1092, 169), (1073, 264), (1020, 425),
   (1001, 468), (975, 520), (952, 561), (884, 663), (817, 744)]

/-- Exact per-token KV-cache footprint in bytes for `(d_c, d_R, b_c, b_R)`. -/
def mlaBytesPerToken (d_c d_R b_c b_R : Nat) : Rat :=
  ((d_c * b_c + d_R * b_R : Nat) : Rat) / 8

/-- Exact per-token BF16 MHA KV-cache footprint in bytes (`2 * H * d_h * 2 = 4 * H * d_h`). -/
def bf16MhaBytesPerToken (H d_h : Nat) : Rat :=
  ((H * d_h * 4 : Nat) : Rat)

/-- Exact per-token BF16 MLA KV-cache footprint in bytes (`(d_c + d_R) * 2`). -/
def bf16MlaBytesPerToken (d_c d_R : Nat) : Rat :=
  (((d_c + d_R) * 2 : Nat) : Rat)

end MlaKantorovichRope
