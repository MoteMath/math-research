/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Public Definitions (`mxfp6-ef21-rotations`)

Pure Lean 4 `Init` (zero Mathlib) definitions for:
1. Exact OCP `E2M1`, `E3M2`, and `E2M3` quantization grids and symmetric nearest-grid quantizers over `Rat`.
2. Universal all-`B` EF21 contraction functions `alphaMXFP6E3M2`, `alphaNVFP6E3M2`,
   `alphaMXFP6E2M3`, and `alphaNVFP6E2M3`.
3. Pure-`Init` integer matrix algebra (`IntMat`), Goethals–Seidel 4-circulant matrices
   (`GS_n16_E2M1_low`, `GS_n32_E2M1_pm13`), and universal Hamilton 4:8-sparse quaternion stages.
-/

namespace Mxfp6Ef21Rotations

/-! ### 1. Basic `Rat` Helpers and Finite Sums -/

def absRat (x : Rat) : Rat :=
  if x < 0 then -x else x

def sumFinRat : (n : Nat) → (Fin n → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => sumFinRat n (fun i => f i.castSucc) + f (Fin.last n)

def sumSq {B : Nat} (y : Fin B → Rat) : Rat :=
  sumFinRat B (fun i => y i * y i)

def sumSqErr {B : Nat} (q : Rat → Rat) (y : Fin B → Rat) : Rat :=
  sumFinRat B (fun i => (q (y i) - y i) * (q (y i) - y i))

/-! ### 2. Exact OCP Quantization Grids (`E2M1`, `E3M2`, `E2M3`) -/

/-- Exact OCP FP4-E2M1 nonnegative grid (8 levels, max `6`). -/
def e2m1Levels : List Rat :=
  [0, 1/2, 1, 3/2, 2, 3, 4, 6]

/-- Exact OCP FP6-E3M2 nonnegative grid (32 levels, units of `1/16`, max `28`). -/
def e3m2Levels : List Rat :=
  [ 0, 1/16, 1/8, 3/16,
    1/4, 5/16, 3/8, 7/16,
    1/2, 5/8, 3/4, 7/8,
    1, 5/4, 3/2, 7/4,
    2, 5/2, 3, 7/2,
    4, 5, 6, 7,
    8, 10, 12, 14,
    16, 20, 24, 28 ]

/-- Exact OCP FP6-E2M3 nonnegative grid (32 levels, units of `1/8`, max `15/2`). -/
def e2m3Levels : List Rat :=
  [ 0, 1/8, 1/4, 3/8, 1/2, 5/8, 3/4, 7/8,
    1, 9/8, 5/4, 11/8, 3/2, 13/8, 7/4, 15/8,
    2, 9/4, 5/2, 11/4, 3, 13/4, 7/2, 15/4,
    4, 9/2, 5, 11/2, 6, 13/2, 7, 15/2 ]

/-- Nearest grid point on a sorted nonnegative list of rational levels (ties round down). -/
def nearestNonneg : List Rat → Rat → Rat
  | [], _ => 0
  | [g], _ => g
  | g1 :: g2 :: rest, y =>
    if y ≤ (g1 + g2) / 2 then g1 else nearestNonneg (g2 :: rest) y

/-- Symmetric nearest-grid quantizer satisfying `symQuant levels (-y) = -symQuant levels y`. -/
def symQuant (levels : List Rat) (y : Rat) : Rat :=
  if y < 0 then -(nearestNonneg levels (-y)) else nearestNonneg levels y

def e2m1Quant : Rat → Rat := symQuant e2m1Levels
def e3m2Quant : Rat → Rat := symQuant e3m2Levels
def e2m3Quant : Rat → Rat := symQuant e2m3Levels

/-! ### 3. Universal All-`B` EF21 Contraction Functions -/

def alphaMXFP6E3M2 (B : Nat) : Rat :=
  min (327680 / ((B : Rat) + 331775))
    (min (229376 / ((B : Rat) + 230399)) (200704 / ((B : Rat) + 200703)))

def alphaNVFP6E3M2 (B : Nat) : Rat :=
  min ((80 * (B : Rat) + 116) / (81 * (B : Rat) + 115))
    (802816 / ((B : Rat) + 802815))

def alphaMXFP6E2M3 (B : Nat) : Rat :=
  min (4608 / ((B : Rat) + 4623))
    (min (3840 / ((B : Rat) + 3843)) (3600 / ((B : Rat) + 3599)))

def alphaNVFP6E2M3 (B : Nat) : Rat :=
  min ((288 * (B : Rat) + 612) / (289 * (B : Rat) + 611))
    (14400 / ((B : Rat) + 14399))

/-! ### 4. Integer Matrix Algebra -/

abbrev IntMat (m n : Nat) := Fin m → Fin n → Int

def sumFinInt : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFinInt n (fun i => f i.castSucc) + f (Fin.last n)

def transpose {m n : Nat} (A : IntMat m n) : IntMat n m :=
  fun i j => A j i

def idMat (n : Nat) : IntMat n n :=
  fun i j => if i = j then 1 else 0

def scaleMat {m n : Nat} (c : Int) (A : IntMat m n) : IntMat m n :=
  fun i j => c * A i j

def matMul {m k n : Nat} (A : IntMat m k) (B : IntMat k n) : IntMat m n :=
  fun i j => sumFinInt k (fun t => A i t * B t j)

def isOrthogonal {n : Nat} (Q : IntMat n n) (c : Int) : Prop :=
  matMul (transpose Q) Q = scaleMat c (idMat n)

def matProd (n : Nat) : List (IntMat n n) → IntMat n n
  | [] => idMat n
  | M :: rest => matMul M (matProd n rest)

def prodInt : List Int → Int
  | [] => 1
  | c :: rest => c * prodInt rest

/-! ### 5. Goethals–Seidel 4-Circulant Matrices (`GS_n16_E2M1_low`, `GS_n32_E2M1_pm13`) -/

def circMat (m : Nat) (row : Fin m → Int) : IntMat m m :=
  fun i j => row ⟨(j.val + m - i.val) % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

def mulBackRev (m : Nat) (X : IntMat m m) : IntMat m m :=
  fun i j => X i ⟨m - 1 - j.val, by omega⟩

def negMat {m n : Nat} (A : IntMat m n) : IntMat m n :=
  fun i j => -(A i j)

def goethalsSeidelMat (m : Nat) (a b c d : Fin m → Int) : IntMat (4 * m) (4 * m) :=
  let A := circMat m a
  let B := circMat m b
  let C := circMat m c
  let D := circMat m d
  let BR := mulBackRev m B
  let CR := mulBackRev m C
  let DR := mulBackRev m D
  let BtR := mulBackRev m (transpose B)
  let CtR := mulBackRev m (transpose C)
  let DtR := mulBackRev m (transpose D)
  fun i j =>
    have hm : 0 < m := by have := i.isLt; omega
    let bi := i.val / m
    let bj := j.val / m
    let ri : Fin m := ⟨i.val % m, Nat.mod_lt _ hm⟩
    let rj : Fin m := ⟨j.val % m, Nat.mod_lt _ hm⟩
    match bi, bj with
    | 0, 0 => A ri rj
    | 0, 1 => BR ri rj
    | 0, 2 => CR ri rj
    | 0, 3 => DR ri rj
    | 1, 0 => -(BR ri rj)
    | 1, 1 => A ri rj
    | 1, 2 => -(DtR ri rj)
    | 1, 3 => CtR ri rj
    | 2, 0 => -(CR ri rj)
    | 2, 1 => DtR ri rj
    | 2, 2 => A ri rj
    | 2, 3 => -(BtR ri rj)
    | 3, 0 => -(DR ri rj)
    | 3, 1 => -(CtR ri rj)
    | 3, 2 => BtR ri rj
    | _, _ => A ri rj

def gs16_a : Fin 4 → Int
  | ⟨0, _⟩ => -2 | ⟨1, _⟩ => 2 | ⟨2, _⟩ => 2 | ⟨3, _⟩ => 2

def gs16_b : Fin 4 → Int
  | ⟨0, _⟩ => 3 | ⟨1, _⟩ => 2 | ⟨2, _⟩ => 1 | ⟨3, _⟩ => -2

def gs16_c : Fin 4 → Int
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => -2 | ⟨2, _⟩ => 3 | ⟨3, _⟩ => 2

def gs16_d : Fin 4 → Int
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => -3 | ⟨2, _⟩ => -1 | ⟨3, _⟩ => -1

def GS_n16_E2M1_low : IntMat 16 16 :=
  goethalsSeidelMat 4 gs16_a gs16_b gs16_c gs16_d

def gs32_a : Fin 8 → Int
  | ⟨0, _⟩ => -1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => -3 | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 3  | ⟨5, _⟩ => 1 | ⟨6, _⟩ => 1  | ⟨7, _⟩ => 1

def gs32_b : Fin 8 → Int
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => -1 | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1 | ⟨5, _⟩ => 1 | ⟨6, _⟩ => -1 | ⟨7, _⟩ => 1

def gs32_c : Fin 8 → Int
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1  | ⟨2, _⟩ => -1 | ⟨3, _⟩ => -1
  | ⟨4, _⟩ => 1 | ⟨5, _⟩ => -1 | ⟨6, _⟩ => -1 | ⟨7, _⟩ => -3

def gs32_d : Fin 8 → Int
  | ⟨0, _⟩ => -1 | ⟨1, _⟩ => -1 | ⟨2, _⟩ => -3 | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => -1 | ⟨5, _⟩ => 1  | ⟨6, _⟩ => 1  | ⟨7, _⟩ => -1

def GS_n32_E2M1_pm13 : IntMat 32 32 :=
  goethalsSeidelMat 8 gs32_a gs32_b gs32_c gs32_d

/-- Entry `x` is representable with zero quantization error in OCP `E2M1` (at E8M0 scale `1/4`),
    `E3M2`, and `E2M3` simultaneously. -/
def inAllThreeOCPGrids (x : Rat) : Prop :=
  absRat (4 * x) ∈ e2m1Levels ∧
  absRat x ∈ e3m2Levels ∧
  absRat x ∈ e2m3Levels ∧
  e2m1Quant (4 * x) = 4 * x ∧
  e3m2Quant x = x ∧
  e2m3Quant x = x

/-! ### 6. Universal Hamilton 4:8-Sparse Quaternion Blocks & Multi-Stage Factorizations -/

/-- Exact `4 × 4` Hamilton quaternion matrix with `Q^T Q = (a^2 + b^2 + c^2 + d^2) I_4`. -/
def quatMat (a b c d : Int) : IntMat 4 4 :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => a  | 0, 1 => -b | 0, 2 => -c | 0, 3 => -d
    | 1, 0 => b  | 1, 1 => a  | 1, 2 => -d | 1, 3 => c
    | 2, 0 => c  | 2, 1 => d  | 2, 2 => a  | 2, 3 => -b
    | 3, 0 => d  | 3, 1 => -c | 3, 2 => b  | _, _ => a

/-- Block-diagonal lift of `m` independent `4 × 4` Hamilton quaternion blocks to `4m × 4m`. -/
def blockDiagQuat (m : Nat) (params : Fin m → Int × Int × Int × Int) : IntMat (4 * m) (4 * m) :=
  fun i j =>
    if h : i.val / 4 = j.val / 4 then
      let b : Fin m := ⟨i.val / 4, by omega⟩
      let (a, b1, c, d) := params b
      quatMat a b1 c d ⟨i.val % 4, by omega⟩ ⟨j.val % 4, by omega⟩
    else 0

/-- Permutation matrix `P_σ` with `(P_σ)_{i,j} = 1` iff `σ i = j`. -/
def permMat (n : Nat) (σ : Fin n → Fin n) : IntMat n n :=
  fun i j => if σ i = j then 1 else 0

/-- Bijection predicate on `Fin n`. -/
def isBijection {n : Nat} (σ : Fin n → Fin n) : Prop :=
  ∃ inv : Fin n → Fin n, (∀ i, inv (σ i) = i) ∧ (∀ j, σ (inv j) = j)

/-- Count of nonzero entries in a `Fin n → Int` vector. -/
def countNonzero : (n : Nat) → (Fin n → Int) → Nat
  | 0, _ => 0
  | n + 1, f => countNonzero n (fun i => f i.castSucc) + if f (Fin.last n) ≠ 0 then 1 else 0

/-- A `4m × 4m` matrix is row-4-sparse (hence 4:8-sparse in every 8-tuple) if every row has
    at most 4 nonzero entries. -/
def isRow4Sparse {n : Nat} (M : IntMat n n) : Prop :=
  ∀ i : Fin n, countNonzero n (fun j => M i j) ≤ 4

/-- A single permutation-coupled 4:8-sparse quaternion stage: `P_σ * blockDiagQuat m params`. -/
def quatStage (m : Nat) (params : Fin m → Int × Int × Int × Int)
    (σ : Fin (4 * m) → Fin (4 * m)) : IntMat (4 * m) (4 * m) :=
  matMul (permMat (4 * m) σ) (blockDiagQuat m params)

end Mxfp6Ef21Rotations
