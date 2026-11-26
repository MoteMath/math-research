/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`kronecker-cyclic-frustration`)

Pure-`Init` (zero Mathlib) definitions for:
1. Sum-of-2-Kronecker spectral distortion, Corner-Geometric-Mean preconditioner, and K-FAC factors.
2. Multi-head block-diagonal Hessians, 2-head geometric-mean vs K-FAC, directed Karp cycle products,
   and the exact `H`-head cyclic frustration witness `b_{h,j} = M^{(j - h) mod H}`.
3. 2-stage Monarch matrix entry factorization, integer row/column norm-squared and sparsity (`nnz`),
   OCP `E2M1` grid membership, and universal Quaternion (`4×4`) / Octonion (`8×8`) orthogonal blocks.
-/

namespace KroneckerCyclicFrustration

/-- Nonnegative integer power on `Rat` (pure `Init`, zero Mathlib). -/
def ratPow (x : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => ratPow x n * x

/-- Finite product over `Fin n` on `Rat`. -/
def finProdRat : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 1
  | _ + 1, f => finProdRat (fun i => f i.castSucc) * f ⟨_, Nat.lt_succ_self _⟩

/-- Finite sum over `Fin n` on `Int`. -/
def finSumInt : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | _ + 1, f => finSumInt (fun i => f i.castSucc) + f ⟨_, Nat.lt_succ_self _⟩

/-- Finite sum over `Fin n` on `Nat`. -/
def finSumNat : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _ + 1, f => finSumNat (fun i => f i.castSucc) + f ⟨_, Nat.lt_succ_self _⟩

/-- Finite sum over `Fin n` on `Rat`. -/
def finSumRat : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | _ + 1, f => finSumRat (fun i => f i.castSucc) + f ⟨_, Nat.lt_succ_self _⟩

/-! ## 1. Sum-of-2-Kronecker Spectral Distortion & Corner-Geometric-Mean Preconditioner -/

/-- Exact optimal squared condition number `(κ*_⊗)^2` for `A_1 ⊗ B_1 + A_2 ⊗ B_2`
    with generalized eigenvalue ranges `[α_min, α_max]` and `[β_min, β_max]`. -/
def cornerOptKappaSq (α_max α_min β_max β_min : Rat) : Rat :=
  ((1 + α_max * β_max) * (1 + α_min * β_min)) /
    ((1 + α_max * β_min) * (1 + α_min * β_max))

/-- Squared left factor `(ℓ*_i)^2` of the Corner-Geometric-Mean Preconditioner. -/
def cornerEllSq (α_i β_max β_min : Rat) : Rat :=
  (1 + α_i * β_max) * (1 + α_i * β_min)

/-- Squared right factor `(r*_j)^2` of the Corner-Geometric-Mean Preconditioner. -/
def cornerRSq (α_max α_min β_j : Rat) : Rat :=
  (1 + α_max * β_j) * (1 + α_min * β_j)

/-- Squared preconditioned eigenvalue `(1 + α_i β_j)^2 / ((ℓ*_i)^2 (r*_j)^2)` under
    the Corner-Geometric-Mean Preconditioner. -/
def cornerPrecondEigSq (α_i β_j α_max α_min β_max β_min : Rat) : Rat :=
  ((1 + α_i * β_j) * (1 + α_i * β_j)) /
    (cornerEllSq α_i β_max β_min * cornerRSq α_max α_min β_j)

/-- K-FAC left factor `n + α_i * ∑ β_j` (scaled by `n` uniformly, scale-invariant for `κ`). -/
def kfacLeftFactor (n : Nat) (α_i sum_β : Rat) : Rat :=
  (n : Rat) + α_i * sum_β

/-- K-FAC right factor `n + β_j * ∑ α_i` (scaled by `n` uniformly, scale-invariant for `κ`). -/
def kfacRightFactor (n : Nat) (β_j sum_α : Rat) : Rat :=
  (n : Rat) + β_j * sum_α

/-- K-FAC preconditioned eigenvalue `(1 + α_i β_j) / (lk_i * rk_j)` for sum-of-2-Kronecker. -/
def kfacPrecondEig (n : Nat) (α_i β_j sum_α sum_β : Rat) : Rat :=
  (1 + α_i * β_j) / (kfacLeftFactor n α_i sum_β * kfacRightFactor n β_j sum_α)

/-! ## 2. Multi-Head Block-Diagonal Hessians & Cyclic Frustration -/

/-- Exact 2-head squared optimal Kronecker condition number for head eigenvalues `b1, b2`. -/
def twoHeadOptKappaSq (b1_max b2_max b1_min b2_min : Rat) : Rat :=
  (b1_max / b2_max) / (b1_min / b2_min)

/-- Exact K-FAC preconditioned eigenvalue on `B_1 = diag(1, M)`, `B_2 = diag(1, 1)`
    with `L_KFAC = (1 + M, 2)` and `R_KFAC = (1, (1 + M) / 2)`. -/
def twoHeadKfacEig (M : Rat) (h j : Fin 2) : Rat :=
  let b : Rat := if h.val = 0 then (if j.val = 0 then 1 else M) else 1
  let lk : Rat := if h.val = 0 then 1 + M else 2
  let rk : Rat := if j.val = 0 then 1 else (1 + M) / 2
  b / (lk * rk)

/-- Next cyclic index `(t + 1) mod L` for `Fin L` (`0 < L`). -/
def finNext {L : Nat} (hL : 0 < L) (t : Fin L) : Fin L :=
  ⟨(t.val + 1) % L, Nat.mod_lt _ hL⟩

/-- Multiplicative cycle product `∏_{t=0}^{L-1} b(head t, feat t) / b(head t, feat (t+1 mod L))`
    along a directed feature cycle of length `L`. -/
def karpCycleProduct {H d L : Nat} (hL : 0 < L)
    (b : Fin H → Fin d → Rat) (head : Fin L → Fin H) (feat : Fin L → Fin d) : Rat :=
  finProdRat (fun t : Fin L => b (head t) (feat t) / b (head t) (feat (finNext hL t)))

/-- Scaled cycle product after applying an arbitrary Kronecker preconditioner `(ℓ, r)`. -/
def karpScaledCycleProduct {H d L : Nat} (hL : 0 < L)
    (b : Fin H → Fin d → Rat) (ℓ : Fin H → Rat) (r : Fin d → Rat)
    (head : Fin L → Fin H) (feat : Fin L → Fin d) : Rat :=
  finProdRat (fun t : Fin L =>
    (b (head t) (feat t) / (ℓ (head t) * r (feat t))) /
      (b (head t) (feat (finNext hL t)) / (ℓ (head t) * r (feat (finNext hL t)))))

/-- Exact `H`-head, `H`-feature cyclic frustration witness:
    `b_{h,j} = M^{(j + H - h) mod H}`. -/
def cyclicWitness (H : Nat) (M : Rat) (h j : Fin H) : Rat :=
  ratPow M ((j.val + H - h.val) % H)

/-- Exact cyclic frustration exponent ratio `2(H - 1) / H`. -/
def cyclicFrustrationRatio (H : Nat) : Rat :=
  (2 * ((H - 1 : Nat) : Rat)) / (H : Rat)

/-! ## 3. 2-Stage Monarch Coherence & Sparse E2M1 Quaternion / Octonion Blocks -/

/-- Entry `Q_{(b', a'), (a, b)} = A_{a', a} * B_{b', b}` of a 2-stage Monarch transform `L P R`. -/
def monarchEntry {n1 n2 : Nat} (A : Fin n2 → Fin n2 → Int) (B : Fin n1 → Fin n1 → Int)
    (row : Fin n1 × Fin n2) (col : Fin n2 × Fin n1) : Int :=
  A row.2 col.1 * B row.1 col.2

/-- Column inner product `(M^T M)_{i, j} = ∑_k M_{k, i} * M_{k, j}` for an integer matrix. -/
def matColDot {n : Nat} (M : Fin n → Fin n → Int) (i j : Fin n) : Int :=
  finSumInt (fun k => M k i * M k j)

/-- Predicate that an integer `n × n` matrix satisfies exact scaled orthogonality `M^T M = S * I_n`. -/
def IsScaledOrtho {n : Nat} (M : Fin n → Fin n → Int) (S : Int) : Prop :=
  ∀ i j : Fin n, matColDot M i j = if i = j then S else 0

/-- Row norm-squared `∑_j (v j)^2` of an integer vector. -/
def vecNormSq {n : Nat} (v : Fin n → Int) : Int :=
  finSumInt (fun j => v j * v j)

/-- Row support size (number of nonzero entries) of an integer vector. -/
def vecNnz {n : Nat} (v : Fin n → Int) : Nat :=
  finSumNat (fun j => if v j = 0 then 0 else 1)

/-- Exact OCP `E2M1` (FP4) magnitude grid `{0, 1, 2, 3, 4, 6, 8, 12}` (signed, zero weight error). -/
def inE2M1Grid (x : Int) : Bool :=
  let a := x.natAbs
  a == 0 || a == 1 || a == 2 || a == 3 || a == 4 || a == 6 || a == 8 || a == 12

/-- Universal `4 × 4` Quaternion left-multiplication matrix `Q(a, b, c, d)`. -/
def quat4 (a b c d : Int) (i j : Fin 4) : Int :=
  match i.val, j.val with
  | 0, 0 =>  a | 0, 1 => -b | 0, 2 => -c | 0, 3 => -d
  | 1, 0 =>  b | 1, 1 =>  a | 1, 2 => -d | 1, 3 =>  c
  | 2, 0 =>  c | 2, 1 =>  d | 2, 2 =>  a | 2, 3 => -b
  | 3, 0 =>  d | 3, 1 => -c | 3, 2 =>  b | 3, 3 =>  a
  | _, _ =>  0

/-- Universal `8 × 8` Octonion left-multiplication matrix `O(c0..c7)` built from the
    7 Fano-plane triples `(1,2,3), (1,4,5), (1,7,6), (2,4,6), (2,5,7), (3,4,7), (3,6,5)`. -/
def oct8 (c0 c1 c2 c3 c4 c5 c6 c7 : Int) (i j : Fin 8) : Int :=
  match i.val with
  | 0 => match j.val with
    | 0 =>  c0 | 1 => -c1 | 2 => -c2 | 3 => -c3 | 4 => -c4 | 5 => -c5 | 6 => -c6 | _ => -c7
  | 1 => match j.val with
    | 0 =>  c1 | 1 =>  c0 | 2 => -c3 | 3 =>  c2 | 4 => -c5 | 5 =>  c4 | 6 =>  c7 | _ => -c6
  | 2 => match j.val with
    | 0 =>  c2 | 1 =>  c3 | 2 =>  c0 | 3 => -c1 | 4 => -c6 | 5 => -c7 | 6 =>  c4 | _ =>  c5
  | 3 => match j.val with
    | 0 =>  c3 | 1 => -c2 | 2 =>  c1 | 3 =>  c0 | 4 => -c7 | 5 =>  c6 | 6 => -c5 | _ =>  c4
  | 4 => match j.val with
    | 0 =>  c4 | 1 =>  c5 | 2 =>  c6 | 3 =>  c7 | 4 =>  c0 | 5 => -c1 | 6 => -c2 | _ => -c3
  | 5 => match j.val with
    | 0 =>  c5 | 1 => -c4 | 2 =>  c7 | 3 => -c6 | 4 =>  c1 | 5 =>  c0 | 6 =>  c3 | _ => -c2
  | 6 => match j.val with
    | 0 =>  c6 | 1 => -c7 | 2 => -c4 | 3 =>  c5 | 4 =>  c2 | 5 => -c3 | 6 =>  c0 | _ =>  c1
  | _ => match j.val with
    | 0 =>  c7 | 1 =>  c6 | 2 => -c5 | 3 => -c4 | 4 =>  c3 | 5 =>  c2 | 6 => -c1 | _ =>  c0

/-- Sparse Quaternion `4 × 4` block with `s ∈ {1, 2, 3, 4}` ones and `4 - s` zeros. -/
def sparseQuat4 (s : Nat) : Fin 4 → Fin 4 → Int :=
  quat4 (if 0 < s then 1 else 0) (if 1 < s then 1 else 0)
        (if 2 < s then 1 else 0) (if 3 < s then 1 else 0)

/-- Sparse Octonion `8 × 8` block with `s ∈ {1..8}` ones and `8 - s` zeros
    (includes `O8_4nnz` at `s = 4` and `O8_7nnz` at `s = 7`). -/
def sparseOct8 (s : Nat) : Fin 8 → Fin 8 → Int :=
  oct8 (if 0 < s then 1 else 0) (if 1 < s then 1 else 0)
       (if 2 < s then 1 else 0) (if 3 < s then 1 else 0)
       (if 4 < s then 1 else 0) (if 5 < s then 1 else 0)
       (if 6 < s then 1 else 0) (if 7 < s then 1 else 0)

/-- Predicate that an `n × n` integer block is exact zero-error `E2M1`, scaled orthogonal
    `M^T M = s * I`, has uniform row sparsity `s`, and attains optimal coherence `1 / s`
    (every entry satisfies `M_{i,j}^2 ≤ 1` and every row has `normSq = s` and `nnz = s`). -/
def IsOptimalSparseE2M1Block {n : Nat} (M : Fin n → Fin n → Int) (s : Nat) : Prop :=
  IsScaledOrtho M (s : Int) ∧
  (∀ i j : Fin n, inE2M1Grid (M i j) = true) ∧
  (∀ i j : Fin n, M i j * M i j ≤ 1) ∧
  (∀ i : Fin n, vecNnz (M i) = s) ∧
  (∀ i : Fin n, vecNormSq (M i) = (s : Int))

end KroneckerCyclicFrustration
