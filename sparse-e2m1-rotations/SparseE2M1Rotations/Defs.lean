/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`sparse-e2m1-rotations`)

Pure-`Init` (zero Mathlib) integer matrix algebra, Kronecker products, 2:4 structured sparsity,
doubled-E2M1 membership, Walsh–Hadamard matrices, doubly-2:4-sparse butterflies `B1`, `B2`,
Givens-Hadamard block `G4_1_2`, and Paley skew-conference constructions `C8`, `C16`, `Q32`, `Q16`.
-/

namespace SparseE2M1Rotations

/-- An `m × n` integer matrix represented as a function on `Fin m → Fin n → Int`. -/
abbrev IntMat (m n : Nat) := Fin m → Fin n → Int

/-- Finite sum of an integer-valued function over `Fin n`. -/
def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFin n (fun i => f i.castSucc) + f (Fin.last n)

/-- The `n × n` integer identity matrix. -/
def idMat (n : Nat) : IntMat n n :=
  fun i j => if i = j then 1 else 0

/-- Matrix transpose. -/
def transpose {m n : Nat} (A : IntMat m n) : IntMat n m :=
  fun i j => A j i

/-- Integer matrix multiplication. -/
def matMul {m k n : Nat} (A : IntMat m k) (B : IntMat k n) : IntMat m n :=
  fun i j => sumFin k (fun t => A i t * B t j)

/-- Scalar multiplication of an integer matrix. -/
def scaleMat {m n : Nat} (c : Int) (A : IntMat m n) : IntMat m n :=
  fun i j => c * A i j

/-- Entrywise addition of integer matrices. -/
def addMat {m n : Nat} (A B : IntMat m n) : IntMat m n :=
  fun i j => A i j + B i j

/-- Entrywise negation of an integer matrix. -/
def negMat {m n : Nat} (A : IntMat m n) : IntMat m n :=
  fun i j => -A i j

/-- Helper: if `Fin (a * b)` is inhabited, then `0 < b`. -/
theorem pos_right_of_fin_mul {a b : Nat} (i : Fin (a * b)) : 0 < b := by
  have hi : i.val < a * b := i.isLt
  cases b with
  | zero => simp at hi
  | succ b => exact Nat.succ_pos b

/-- Helper: for `i : Fin (a * b)`, `i.val / b < a`. -/
theorem div_lt_left_of_fin_mul {a b : Nat} (i : Fin (a * b)) : i.val / b < a :=
  Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq i.isLt (Nat.mul_comm a b))

/-- Kronecker product `A ⊗ B` of an `m1 × n1` matrix and an `m2 × n2` matrix. -/
def kron {m1 n1 m2 n2 : Nat} (A : IntMat m1 n1) (B : IntMat m2 n2) :
    IntMat (m1 * m2) (n1 * n2) :=
  fun i j =>
    A ⟨i.val / m2, div_lt_left_of_fin_mul i⟩
      ⟨j.val / n2, div_lt_left_of_fin_mul j⟩ *
    B ⟨i.val % m2, Nat.mod_lt _ (pos_right_of_fin_mul i)⟩
      ⟨j.val % n2, Nat.mod_lt _ (pos_right_of_fin_mul j)⟩

/-- Exact column-orthogonality `Q^T Q = c I`. -/
def isOrthogonal {n : Nat} (Q : IntMat n n) (c : Int) : Prop :=
  matMul (transpose Q) Q = scaleMat c (idMat n)

/-- Exact row-orthogonality `Q Q^T = c I`. -/
def isRowOrthogonal {n : Nat} (Q : IntMat n n) (c : Int) : Prop :=
  matMul Q (transpose Q) = scaleMat c (idMat n)

/-- Number of nonzero entries in a 4-tuple of integers. -/
def nzCount4 (a b c d : Int) : Nat :=
  (if a != 0 then 1 else 0) +
  (if b != 0 then 1 else 0) +
  (if c != 0 then 1 else 0) +
  (if d != 0 then 1 else 0)

/-- Row-wise 2:4 structured sparsity: every contiguous 4-tuple in every row has ≤ 2 nonzeros. -/
def is24SparseRows {r m : Nat} (A : IntMat r (m * 4)) : Prop :=
  ∀ (i : Fin r) (g : Fin m),
    nzCount4
      (A i ⟨g.val * 4 + 0, by omega⟩)
      (A i ⟨g.val * 4 + 1, by omega⟩)
      (A i ⟨g.val * 4 + 2, by omega⟩)
      (A i ⟨g.val * 4 + 3, by omega⟩) ≤ 2

/-- Doubly-2:4 structured sparsity: both `A` and `A^T` are row-wise 2:4-sparse. -/
def isDoubly24Sparse {m : Nat} (A : IntMat (m * 4) (m * 4)) : Prop :=
  is24SparseRows A ∧ is24SparseRows (transpose A)

/-- Membership in doubled FP4-E2M1: `2 * E2M1 = {0, ±1, ±2, ±3, ±4, ±6, ±8, ±12}`. -/
def isDoubledE2M1 (x : Int) : Prop :=
  x = 0 ∨ x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 ∨ x = 3 ∨ x = -3 ∨
  x = 4 ∨ x = -4 ∨ x = 6 ∨ x = -6 ∨ x = 8 ∨ x = -8 ∨ x = 12 ∨ x = -12

/-- Membership in the ternary set `{-1, 0, 1}`. -/
def isTernary (x : Int) : Prop :=
  x = -1 ∨ x = 0 ∨ x = 1

/-- Every entry of `A` satisfies predicate `P`. -/
def matEntriesIn {m n : Nat} (P : Int → Prop) (A : IntMat m n) : Prop :=
  ∀ i j, P (A i j)

/-- Fuel-bounded binary popcount parity (structurally recursive for fast kernel reduction). -/
def bitParityFuel : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, n =>
    if n = 0 then false
    else xor (n % 2 == 1) (bitParityFuel fuel (n / 2))

/-- Parity of the binary popcount of `n : Nat` (`true` iff odd number of 1-bits). -/
def bitParity (n : Nat) : Bool :=
  bitParityFuel n n

/-- `(i, j)` entry of the Sylvester Walsh–Hadamard matrix: `(-1)^(popcnt(i &&& j))`. -/
def walshEntry (i j : Nat) : Int :=
  if bitParity (i &&& j) then -1 else 1

/-- Sylvester Walsh–Hadamard matrix of size `n × n` (for `n` a power of 2). -/
def walshHadamardOf (n : Nat) : IntMat n n :=
  fun i j => walshEntry i.val j.val

/-- The `2^k × 2^k` Sylvester Walsh–Hadamard matrix `H_{2^k}`. -/
abbrev walshHadamard (k : Nat) : IntMat (2 ^ k) (2 ^ k) :=
  walshHadamardOf (2 ^ k)

/-- `4 × 4` doubly-2:4-sparse orthogonal butterfly `B1` (`B1^T B1 = 2 I_4`). -/
def B1 : IntMat 4 4 :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 1  | 0, 1 => 1  | 0, 2 => 0  | 0, 3 => 0
    | 1, 0 => 1  | 1, 1 => -1 | 1, 2 => 0  | 1, 3 => 0
    | 2, 0 => 0  | 2, 1 => 0  | 2, 2 => 1  | 2, 3 => 1
    | 3, 0 => 0  | 3, 1 => 0  | 3, 2 => 1  | 3, 3 => -1
    | _, _ => 0

/-- `4 × 4` doubly-2:4-sparse orthogonal butterfly `B2` (`B2^T B2 = 2 I_4`, `B1 * B2 = H_4`). -/
def B2 : IntMat 4 4 :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 1  | 0, 1 => 0  | 0, 2 => 1  | 0, 3 => 0
    | 1, 0 => 0  | 1, 1 => 1  | 1, 2 => 0  | 1, 3 => 1
    | 2, 0 => 1  | 2, 1 => 0  | 2, 2 => -1 | 2, 3 => 0
    | 3, 0 => 0  | 3, 1 => 1  | 3, 2 => 0  | 3, 3 => -1
    | _, _ => 0

/-- `4 × 4` doubly-2:4-sparse E2M1-native Givens-pair block `G_4(1, 2)` (`G^T G = 5 I_4`). -/
def G4_1_2 : IntMat 4 4 :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 1  | 0, 1 => 2  | 0, 2 => 0  | 0, 3 => 0
    | 1, 0 => -2 | 1, 1 => 1  | 1, 2 => 0  | 1, 3 => 0
    | 2, 0 => 0  | 2, 1 => 0  | 2, 2 => 1  | 2, 3 => 2
    | 3, 0 => 0  | 3, 1 => 0  | 3, 2 => -2 | 3, 3 => 1
    | _, _ => 0

/-- Quadratic-character Legendre symbol modulo 7 for `r ∈ {0..6}`. -/
def legendre7 (r : Nat) : Int :=
  if r == 0 then 0
  else if r == 1 || r == 2 || r == 4 then 1
  else -1

/-- Explicit `8 × 8` Paley skew-conference matrix `C_8` (`C_8^T = -C_8`, `C_8^T C_8 = 7 I_8`). -/
def paleyC8 : IntMat 8 8 :=
  fun i j =>
    if i.val = 0 then
      if j.val = 0 then 0 else 1
    else if j.val = 0 then
      -1
    else
      legendre7 ((j.val + 7 - i.val) % 7)

/-- Universal skew-conference doubling: from an `n × n` skew-conference matrix `C`,
    constructs the `(2 * n) × (2 * n)` block matrix `[[C, I + C], [-I + C, -C]]`. -/
def skewDouble {n : Nat} (C : IntMat n n) : IntMat (2 * n) (2 * n) :=
  fun i j =>
    have hn : 0 < n := pos_right_of_fin_mul i
    let bi := i.val / n
    let bj := j.val / n
    let ri : Fin n := ⟨i.val % n, Nat.mod_lt _ hn⟩
    let rj : Fin n := ⟨j.val % n, Nat.mod_lt _ hn⟩
    if bi = 0 then
      if bj = 0 then C ri rj
      else idMat n ri rj + C ri rj
    else
      if bj = 0 then -(idMat n ri rj) + C ri rj
      else -(C ri rj)

/-- Explicit `16 × 16` skew-conference matrix `C_16 = skewDouble C_8`. -/
def C16 : IntMat (2 * 8) (2 * 8) :=
  skewDouble paleyC8

/-- Explicit `32 × 32` power-of-2-norm E2M1-native rotation `Q_32 = H_4 ⊗ (I_8 + 3 C_8)`. -/
def Q32 : IntMat (4 * 8) (4 * 8) :=
  kron (walshHadamardOf 4) (addMat (idMat 8) (scaleMat 3 paleyC8))

/-- Explicit `16 × 16` NVFP4 winner `Q_16(4, 1) = 4 I_16 + C_16`. -/
def Q16 : IntMat (2 * 8) (2 * 8) :=
  addMat (scaleMat 4 (idMat (2 * 8))) C16

end SparseE2M1Rotations
