/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`bit-slice-hankel-difference-ldu`)

Bitwise Hankel and Automatic-Sequence LDU Factorization Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace BitwiseHankelLDU


/-! ## Part 1: Finite Sums, Signs, and Exact Laplace Determinant -/

abbrev Matrix (n : Nat) := Fin n → Fin n → Int

/-- Finite sum over `Fin n`. -/
def finSum : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | _ + 1, f => f 0 + finSum (fun i => f i.succ)

/-- Finite product over `Fin n`. -/
def finProd : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 1
  | _ + 1, f => f 0 * finProd (fun i => f i.succ)

/-- Exact alternating sign `(-1)^k`. -/
def altSign (k : Nat) : Int :=
  if k % 2 == 0 then 1 else -1

@[simp] theorem altSign_zero : altSign 0 = 1 := rfl
@[simp] theorem altSign_one : altSign 1 = -1 := rfl

theorem altSign_succ (k : Nat) : altSign (k + 1) = -altSign k := by
  unfold altSign
  by_cases h : k % 2 = 0
  · have h1 : (k + 1) % 2 = 1 := by omega
    simp [h, h1]
  · have h0 : k % 2 = 1 := by omega
    have h1 : (k + 1) % 2 = 0 := by omega
    simp [h0, h1]

/-- Swap adjacent indices `k` and `k+1` in `Fin (n + 1)`. -/
def adjSwapFin {n : Nat} (k : Fin n) (i : Fin (n + 1)) : Fin (n + 1) :=
  if i.val = k.val then ⟨k.val + 1, by omega⟩
  else if i.val = k.val + 1 then ⟨k.val, by omega⟩
  else i

/-- Skip index `p` in `Fin (n + 1)`. -/
def skipIdx {n : Nat} (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if i.val < p.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- Minor obtained by deleting row 0 and column `col`. -/
def minor {n : Nat} (M : Matrix (n + 1)) (col : Fin (n + 1)) : Matrix n :=
  fun i j => M i.succ (skipIdx col j)

/-- Exact integer determinant via Laplace expansion along row 0. -/
def det : {n : Nat} → Matrix n → Int
  | 0, _ => 1
  | _ + 1, M => finSum (fun j => altSign j.val * M 0 j * det (minor M j))

/-! ### Verification of `det` on small dimensions -/

def setRow {n : Nat} (M : Matrix n) (r : Fin n) (v : Fin n → Int) : Matrix n :=
  fun i j => if i = r then v j else M i j

def setCol {n : Nat} (M : Matrix n) (c : Fin n) (v : Fin n → Int) : Matrix n :=
  fun i j => if j = c then v i else M i j

/-- Swap two indices `p` and `q` in `Fin n`. -/
def swapFin {n : Nat} (p q : Fin n) (i : Fin n) : Fin n :=
  if i = p then q else if i = q then p else i

/-- Exact integer matrix multiplication. -/
def matMul {n : Nat} (A B : Matrix n) : Matrix n :=
  fun i j => finSum (fun k => A i k * B k j)

/-- Diagonal matrix. -/
def diagMat {n : Nat} (d : Fin n → Int) : Matrix n :=
  fun i j => if i = j then d i else 0

/-- Unit lower-triangular predicate. -/
def IsUnitLower {n : Nat} (L : Matrix n) : Prop :=
  (∀ i : Fin n, L i i = 1) ∧ (∀ i j : Fin n, i.val < j.val → L i j = 0)

/-- Unit upper-triangular predicate. -/
def IsUnitUpper {n : Nat} (U : Matrix n) : Prop :=
  (∀ i : Fin n, U i i = 1) ∧ (∀ i j : Fin n, j.val < i.val → U i j = 0)

/-- Matrix transpose. -/
def matTrans {n : Nat} (A : Matrix n) : Matrix n := fun i j => A j i

/-- Exact integer exponentiation `x^n`. -/
def intPow (x : Int) : Nat → Int
  | 0 => 1
  | n + 1 => x * intPow x n

@[simp] theorem intPow_zero (x : Int) : intPow x 0 = 1 := rfl
@[simp] theorem intPow_one (x : Int) : intPow x 1 = x := by simp [intPow]
theorem intPow_succ (x : Int) (n : Nat) : intPow x (n + 1) = x * intPow x n := rfl

/-- The `n × n` Hankel matrix `H_n(a)` with entries `a(i + j)`. -/
def hankel (a : Nat → Int) (n : Nat) : Matrix n :=
  fun i j => a (i.val + j.val)

/-- Sequence operators: shift, `q`-difference, first difference `Δ`, second difference `Δ²`. -/
def shiftSeq (a : Nat → Int) : Nat → Int := fun k => a (k + 1)

def qDiff (q : Int) (a : Nat → Int) : Nat → Int := fun k => a (k + 1) - q * a k

def diff1 (a : Nat → Int) : Nat → Int := fun k => a (k + 1) - a k

def diff2 (a : Nat → Int) : Nat → Int := diff1 (diff1 a)

/-- Unit lower-triangular `q`-difference matrix `(D_q)_{i,i} = 1`, `(D_q)_{i, i-1} = -q`. -/
def qDiffMat (q : Int) (n : Nat) : Matrix n :=
  fun i j => if i = j then 1 else if j.val + 1 = i.val then -q else 0

/-- LSB Even-Odd permutation on `Fin n`: maps `0..(n+1)/2-1` to even indices `0, 2, ...`
    and `(n+1)/2..n-1` to odd indices `1, 3, ...`. -/
def eoPerm (n : Nat) (i : Fin n) : Fin n :=
  if h : i.val < (n + 1) / 2 then ⟨2 * i.val, by omega⟩
  else ⟨2 * (i.val - (n + 1) / 2) + 1, by have := i.isLt; omega⟩

/-- Inverse of `eoPerm`. -/
def eoPermInv (n : Nat) (k : Fin n) : Fin n :=
  if h : k.val % 2 = 0 then ⟨k.val / 2, by have := k.isLt; omega⟩
  else ⟨(n + 1) / 2 + k.val / 2, by have := k.isLt; omega⟩

/-- Block-diagonal unit lower-triangular matrix `diag(L1, L2)` on `(p + q) × (p + q)`. -/
def blockDiag {p q : Nat} (L1 : Matrix p) (L2 : Matrix q) : Matrix (p + q) :=
  fun i j =>
    if hi : i.val < p then
      if hj : j.val < p then L1 ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
    else
      if hj : j.val < p then 0 else L2 ⟨i.val - p, by have := i.isLt; omega⟩ ⟨j.val - p, by have := j.isLt; omega⟩

/-- Unit lower-triangular block shear `[[I_{m0}, 0], [s * [I_{m1} | 0], I_{m1}]]` on `Fin n` (with `m0 = (n+1)/2`). -/
def blockShearMat (n : Nat) (s : Int) : Matrix n :=
  fun i j =>
    if i = j then 1
    else if (n + 1) / 2 ≤ i.val ∧ j.val = i.val - (n + 1) / 2 then s
    else 0

/-- Exact 2-adic valuation of positive natural numbers (`v2 0 = 0`). -/
def v2 : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 1 + v2 ((n + 1) / 2) else 0
termination_by n => n
decreasing_by omega

/-- Exact binary popcount (`popcount n` = number of 1-bits of `n`). -/
def popcount (n : Nat) : Nat :=
  if h : n = 0 then 0 else (n % 2) + popcount (n / 2)
termination_by n
decreasing_by omega

/-- The 3-parameter even-constant / odd-affine 2-automatic sequence family over `Int`:
    `a(2k) = c`, `a(2k+1) = α * a(k) + β`.
    Unifies period-doubling `(1,-1,1)`, ruler `v2(n+1)` `(0,1,1)`, shifted ruler `1+v2(n+1)` `(1,1,1)`,
    signed ruler `(-1)^{v2(n+1)}` `(1,-1,0)`, and exponential ruler `r^{v2(n+1)}` `(1,r,0)`. -/
def ecSeq (c α β : Int) (n : Nat) : Int :=
  if _ : n = 0 then c
  else if n % 2 = 0 then c
  else α * ecSeq c α β (n / 2) + β
termination_by n
decreasing_by omega

abbrev hankelA (c α β : Int) (n : Nat) : Int := det (hankel (ecSeq c α β) n)

abbrev hankelB (c α β : Int) (n : Nat) : Int := det (hankel (diff1 (ecSeq c α β)) n)

abbrev hankelC (c α β : Int) (n : Nat) : Int := det (hankel (diff2 (ecSeq c α β)) n)

/-- Exact period-8 mod-8 residue pattern for any odd triple `(c, α, β)`. -/
def mod8Pattern (c α β : Int) (r : Nat) : Int :=
  match r with
  | 1 | 5 => c % 8
  | 3 | 7 => (-c) % 8
  | 2 | 6 => if (c * α * β) % 4 = 1 then 5 else 1
  | 4     => 5
  | _     => 1

/-- The `r`-weighted popcount family `u(n) = r^{popcount(n)}`:
    `r = -1` is Thue-Morse `(-1)^{s_2(n)}`, `r = 2` is Gould's sequence `2^{s_2(n)}`. -/
def popPow (r : Int) (n : Nat) : Int := intPow r (popcount n)

/-- Shifted paperfolding sequence: `pf(2k) = (-1)^k`, `pf(2k+1) = pf(k)`. -/
def shiftedPaperfolding (n : Nat) : Int :=
  if h : n = 0 then 1
  else if n % 2 = 0 then altSign (n / 2)
  else shiftedPaperfolding (n / 2)
termination_by n
decreasing_by omega

/-- Sparse lacunary `2^k - 1` family with arbitrary odd-slice `b`: `a(0) = c`, `a(2k) = 0` (`k ≥ 1`), `a(2k+1) = b(k)`. -/
def sparsePow2m1 (c : Int) (b : Nat → Int) (n : Nat) : Int :=
  if n = 0 then c
  else if n % 2 = 0 then 0
  else b (n / 2)

end BitwiseHankelLDU
