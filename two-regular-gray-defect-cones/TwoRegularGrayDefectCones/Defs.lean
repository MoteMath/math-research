/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`two-regular-gray-defect-cones`)

All definitions needed to state the headline theorems (zero `sorry`, pure `Init`).
-/

namespace LinRepEngine

-- ============================================================================
-- Section 1: Exact Core Integer Linear Algebra (Fin d → Int)
-- ============================================================================

abbrev Vec (d : Nat) := Fin d → Int
abbrev Mat (m n : Nat) := Fin m → Fin n → Int

/-- Structural finite sum over `Fin n` from the right so `a + (b + 1)` and `a * (b + 1)`
    unfold definitionally without dependent casts. -/
def sumFin : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFin (fun i : Fin n => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

-- Vector and matrix operations
def dot {d : Nat} (u v : Vec d) : Int :=
  sumFin (fun i => u i * v i)

def matVec {m n : Nat} (M : Mat m n) (v : Vec n) : Vec m :=
  fun i => sumFin (fun j => M i j * v j)

def matMul {m k n : Nat} (A : Mat m k) (B : Mat k n) : Mat m n :=
  fun i j => sumFin (fun t => A i t * B t j)

def matT {m n : Nat} (M : Mat m n) : Mat n m :=
  fun j i => M i j

def vecScale {d : Nat} (c : Int) (v : Vec d) : Vec d :=
  fun i => c * v i

def matScale {m n : Nat} (c : Int) (M : Mat m n) : Mat m n :=
  fun i j => c * M i j

-- Decidable finite relational predicates
def VecEq {d : Nat} (u v : Vec d) : Prop := ∀ i : Fin d, u i = v i
def MatEq {m n : Nat} (A B : Mat m n) : Prop := ∀ i : Fin m, ∀ j : Fin n, A i j = B i j
def VecNonneg {d : Nat} (v : Vec d) : Prop := ∀ i : Fin d, 0 ≤ v i
def MatNonneg {m n : Nat} (M : Mat m n) : Prop := ∀ i : Fin m, ∀ j : Fin n, 0 ≤ M i j
def VecModZero {d : Nat} (m : Int) (v : Vec d) : Prop := ∀ i : Fin d, v i % m = 0
def VecModEq {d : Nat} (m : Int) (u v : Vec d) : Prop := ∀ i : Fin d, (u i - v i) % m = 0
def MatModEq {r c : Nat} (m : Int) (A B : Mat r c) : Prop := ∀ i : Fin r, ∀ j : Fin c, (A i j - B i j) % m = 0

instance {d : Nat} (u v : Vec d) : Decidable (VecEq u v) :=
  inferInstanceAs (Decidable (∀ i : Fin d, u i = v i))
instance {m n : Nat} (A B : Mat m n) : Decidable (MatEq A B) :=
  inferInstanceAs (Decidable (∀ i : Fin m, ∀ j : Fin n, A i j = B i j))
instance {d : Nat} (v : Vec d) : Decidable (VecNonneg v) :=
  inferInstanceAs (Decidable (∀ i : Fin d, 0 ≤ v i))
instance {m n : Nat} (M : Mat m n) : Decidable (MatNonneg M) :=
  inferInstanceAs (Decidable (∀ i : Fin m, ∀ j : Fin n, 0 ≤ M i j))
instance {d : Nat} (m : Int) (v : Vec d) : Decidable (VecModZero m v) :=
  inferInstanceAs (Decidable (∀ i : Fin d, v i % m = 0))
instance {d : Nat} (m : Int) (u v : Vec d) : Decidable (VecModEq m u v) :=
  inferInstanceAs (Decidable (∀ i : Fin d, (u i - v i) % m = 0))
instance {r c : Nat} (m : Int) (A B : Mat r c) : Decidable (MatModEq m A B) :=
  inferInstanceAs (Decidable (∀ i : Fin r, ∀ j : Fin c, (A i j - B i j) % m = 0))

-- ============================================================================
-- Section 2: 2-Regular Linear Representations & Bit-String Semantics
-- ============================================================================

/-- A 2-regular linear representation of dimension `d` over `Int`,
    with leading-zero stability `M0 * v = v`. -/
structure LinRep (d : Nat) where
  u      : Vec d
  M0     : Mat d d
  M1     : Mat d d
  v      : Vec d
  stable : VecEq (matVec M0 v) v

/-- State vector `v(n) = M_{b_0} * ... * M_{b_k} * v` evaluated directly on `Nat`. -/
def evalVec {d : Nat} (R : LinRep d) (n : Nat) : Vec d :=
  if h : n = 0 then R.v
  else matVec (if n % 2 == 1 then R.M1 else R.M0) (evalVec R (n / 2))
termination_by n
decreasing_by omega

/-- Scalar value `f(n) = u^T * M_{b_0} * ... * M_{b_k} * v`. -/
def evalRep {d : Nat} (R : LinRep d) (n : Nat) : Int :=
  dot R.u (evalVec R n)

-- ============================================================================
-- Section 3: Universal 2-Regular Algebra Compiler (Closed Ring + Shift + Sum)
-- ============================================================================

/-- Prefix sum `sumRange f n = ∑_{k=0}^{n-1} f(k)`. -/
def sumRange (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumRange f n + f n

-- ============================================================================
-- Section 4b: Pure-Data Executable Certificate Checkers (Zero Prop Fields)
-- ============================================================================

/-- Pure-data polyhedral cone certificate for `n ≥ 1` (zero `Prop` fields). -/
structure ConePosCertData (d r : Nat) where
  P     : Mat r d
  C0    : Mat r r
  C1    : Mat r r
  c     : Vec r
  alpha : Int
  beta  : Int

/-- Executable Boolean verifier for `ConePosCertData`. -/
def checkConePosCert {d r : Nat} (R : LinRep d) (D : ConePosCertData d r) : Bool :=
  decide (0 < D.alpha) &&
  decide (0 < D.beta) &&
  decide (MatNonneg D.C0) &&
  decide (MatNonneg D.C1) &&
  decide (VecNonneg D.c) &&
  decide (VecNonneg (matVec D.P (matVec R.M1 R.v))) &&
  decide (MatEq (matScale D.beta (matMul D.P R.M0)) (matMul D.C0 D.P)) &&
  decide (MatEq (matScale D.beta (matMul D.P R.M1)) (matMul D.C1 D.P)) &&
  decide (VecEq (vecScale D.alpha R.u) (matVec (matT D.P) D.c))

-- ============================================================================
-- Section 5: Native Pure-Silicon Bitwise Definitions & Semantic Bridges
-- ============================================================================

/-- Binary reflected Gray code: `G(n) = n ^^^ (n >>> 1) = n ^^^ (n / 2)`. -/
def gray (n : Nat) : Nat := n ^^^ (n / 2)

/-- Exact Hamming weight (population count) of a natural number. -/
def popcount (n : Nat) : Nat :=
  if _ : n = 0 then 0
  else n % 2 + popcount (n / 2)
termination_by n
decreasing_by omega

/-- Highest power of 2 not exceeding `n` (`0` for `n = 0`, `2^{⌊log_2 n⌋}` for `n ≥ 1`). -/
def highBit (n : Nat) : Nat :=
  if _ : n = 0 then 0
  else if _ : n = 1 then 1
  else 2 * highBit (n / 2)
termination_by n
decreasing_by omega

/-- Base-`q` Gray-vs-Binary bitwise defect: `d_q(n) = ∑_{i ≥ 0} (g_i - b_i) * q^i`. -/
def dq (q : Int) (n : Nat) : Int :=
  if _ : n = 0 then 0
  else q * dq q (n / 2) + (if n % 2 = 0 then ((n / 2) % 2 : Int) else -((n / 2) % 2 : Int))
termination_by n
decreasing_by omega

/-- Cumulative base-`q` Gray-defect prefix sum: `S_q(q, n) = ∑_{k=0}^{n-1} d_q(k)`. -/
def S_q (q : Int) (n : Nat) : Int := sumRange (dq q) n

/-- Cumulative Gray-code switching-weight excess:
    `W_G(n) = ∑_{k=0}^{n-1} (popcount(G(k)) - popcount(k))`. -/
def W_G (n : Nat) : Int :=
  sumRange (fun k => (popcount (gray k) : Int) - (popcount k : Int)) n

/-- Cumulative Gray-code value excess:
    `E_G(n) = ∑_{k=0}^{n-1} (G(k) - k)`. -/
def E_G (n : Nat) : Int :=
  sumRange (fun k => (gray k : Int) - (k : Int)) n

/-- Dyadic parabolic envelope: `Q_dyadic(n) = (n - highBit(n)) * (2 * highBit(n) - n)`. -/
def Q_dyadic (n : Nat) : Int :=
  ((n : Int) - (highBit n : Int)) * (2 * (highBit n : Int) - (n : Int))

/-- Infinite extremal sequence for Theorem 2:
    `b_0 = 2`, `b_{k+1} = 8*b_k + 6` (`2, 22, 182, 1462, ...`, binary `10110...110`),
    and `extremalA k = b_k + 1` (`3, 23, 183, 1463, ...`, binary `10110...111`). -/
def extremalB : Nat → Nat
  | 0 => 2
  | k + 1 => 8 * extremalB k + 6

def extremalA (k : Nat) : Nat := extremalB k + 1

-- ----------------------------------------------------------------------------
-- Exhaustive Axiom Audit (`#print axioms`) on All Engine & Domain Theorems
-- ----------------------------------------------------------------------------


end LinRepEngine
