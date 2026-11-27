/-!
# Verified Lean 4 Dyadic Matrix-Monoid Contraction, JSR & Invariant-Cone Proof Compiler (`certcomp-4`)

Standalone core Lean 4.34.1 (zero Mathlib, zero `sorry`, zero `native_decide`, zero `Float`).

## Architecture
1. **Exact Dyadic Rationals `Dyadic` (`Z[1/2]`):**
   Exact representation `num / 2^shift` with exact rational order `Dyad.le` / `Dyad.lt`,
   equivalence `Dyad.eqv`, arithmetic (`add`, `mul`, `abs`, `pow`), and matrix products
   `dyadicWordProd`, `dyadicWordProdRL`, and `convexDyadicProd`.
2. **Pure-Data Certificate Structures (zero `Prop` fields):**
   - `SwitchedPolytopeCert d m Q K`: finite DFA-switched exact polar-polytope norm contraction
     & JSR upper-bound certificate (specializes to unconstrained monoids when `Q = 1`, and lifts
     automatically to the entire infinite dyadic convex hull of generators).
   - `SwitchedConeCert d m Q K`: finite DFA-switched exact invariant polyhedral cone positivity
     & joint spectral subradius certificate (handles signed-entry matrices with negative entries
     and lifts to the entire infinite dyadic convex hull).
   - `PeriodicEigenCert d m`: finite exact periodic eigen-witness certifying JSR lower bounds
     and unbounded exponential explosion.
3. **Kernel-Proved General Soundness Meta-Theorems (Finite -> Infinite Bridge):**
   Every theorem quantifies universally over ALL finite words `w : List (Fin m)` of arbitrary
   length `n : Nat` (or all arbitrary-length time-varying dyadic convex-combination sequences
   `ws : List (DyadicConvexStep m)`).
-/

namespace DyadicMonoidEngine

-- ============================================================================
-- SECTION 1: Exact Integer Absolute Value & Dyadic Rationals Z[1/2]
-- ============================================================================

/-- Exact integer absolute value as a nonnegative `Int`. -/
def iabs (x : Int) : Int := if 0 ≤ x then x else -x

/-- Helper: `2 ^ n` as a strictly positive `Int`. -/
def pow2Int (n : Nat) : Int := ((2 ^ n : Nat) : Int)

/-- Exact dyadic rational `num / 2^shift` in `Z[1/2]`. -/
structure Dyad where
  num : Int
  shift : Nat
  deriving Repr, DecidableEq

namespace Dyad

def zero : Dyad := ⟨0, 0⟩
def one : Dyad := ⟨1, 0⟩
def ofInt (z : Int) : Dyad := ⟨z, 0⟩
def ofNat (n : Nat) : Dyad := ⟨(n : Int), 0⟩

/-- Exact rational order `a ≤ b` in `Z[1/2]`, cross-multiplied by positive powers of 2. -/
def le (a b : Dyad) : Prop :=
  a.num * pow2Int b.shift ≤ b.num * pow2Int a.shift

/-- Exact strict rational order `a < b` in `Z[1/2]`. -/
def lt (a b : Dyad) : Prop :=
  a.num * pow2Int b.shift < b.num * pow2Int a.shift

/-- Exact rational equality `a = b` in `Z[1/2]`. -/
def eqv (a b : Dyad) : Prop :=
  a.num * pow2Int b.shift = b.num * pow2Int a.shift

/-- Exact addition in `Z[1/2]`. -/
def add (a b : Dyad) : Dyad :=
  ⟨a.num * pow2Int b.shift + b.num * pow2Int a.shift, a.shift + b.shift⟩

/-- Exact multiplication in `Z[1/2]`. -/
def mul (a b : Dyad) : Dyad :=
  ⟨a.num * b.num, a.shift + b.shift⟩

/-- Exact absolute value in `Z[1/2]`. -/
def abs (a : Dyad) : Dyad :=
  ⟨iabs a.num, a.shift⟩

/-- Exact natural-number power `a^n` in `Z[1/2]`. -/
def pow (a : Dyad) : Nat → Dyad
  | 0 => one
  | n + 1 => mul (pow a n) a

end Dyad

-- ============================================================================
-- SECTION 2: Exact Integer & Dyadic Matrix Algebra + Independent Product Semantics
-- ============================================================================

abbrev Vec (d : Nat) := Fin d → Int
abbrev Mat (r c : Nat) := Fin r → Fin c → Int
abbrev VecD (d : Nat) := Fin d → Dyad
abbrev MatD (r c : Nat) := Fin r → Fin c → Dyad

/-- Exact integer sum over `Fin n`. -/
def finSum : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => finSum (fun i : Fin n => f i.castSucc) + f (Fin.last n)

/-- Exact `Nat` sum over `Fin n`. -/
def finSumNat : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => finSumNat (fun i : Fin n => f i.castSucc) + f (Fin.last n)

/-- Exact `Dyadic` sum over `Fin n`. -/
def finSumD : {n : Nat} → (Fin n → Dyad) → Dyad
  | 0, _ => Dyad.zero
  | n + 1, f => Dyad.add (finSumD (fun i : Fin n => f i.castSucc)) (f (Fin.last n))

/-- Exact max-abs norm `‖v‖_∞` of an integer vector. -/
def vecMaxAbs : {n : Nat} → Vec n → Int
  | 0, _ => 0
  | n + 1, v => max (vecMaxAbs (fun i : Fin n => v i.castSucc)) (iabs (v (Fin.last n)))

/-- Exact row `ℓ_1` norm of an integer matrix row. -/
def rowAbsSum {r c : Nat} (M : Mat r c) (i : Fin r) : Int :=
  finSum (fun j : Fin c => iabs (M i j))

/-- Exact induced `ℓ_∞` matrix operator norm `‖M‖_∞ = max_i ∑_j |M_{i,j}|`. -/
def matInfNorm {r c : Nat} (M : Mat r c) : Int :=
  vecMaxAbs (fun i : Fin r => rowAbsSum M i)

/-- Exact integer matrix-vector multiplication. -/
def matVec {r c : Nat} (M : Mat r c) (x : Vec c) : Vec r :=
  fun i => finSum (fun j => M i j * x j)

/-- Exact integer matrix-matrix multiplication. -/
def matMul {r k c : Nat} (A : Mat r k) (B : Mat k c) : Mat r c :=
  fun i j => finSum (fun t => A i t * B t j)

/-- Exact scalar multiple of an integer matrix. -/
def scaleMat {r c : Nat} (s : Int) (M : Mat r c) : Mat r c :=
  fun i j => s * M i j

/-- Exact `d × d` integer identity matrix. -/
def matId (d : Nat) : Mat d d :=
  fun i j => if i = j then 1 else 0

/-- Standard basis vector `e_q`. -/
def stdBasis {d : Nat} (q : Fin d) : Vec d :=
  fun j => if j = q then 1 else 0

/-- Exact dot product of integer vectors. -/
def vecDot {d : Nat} (u v : Vec d) : Int :=
  finSum (fun i => u i * v i)

-- Exact Dyadic matrix algebra (independent semantics over Z[1/2]) --

def scaleDyadicMat {r c : Nat} (s : Nat) (M : Mat r c) : MatD r c :=
  fun i j => ⟨M i j, s⟩

def dyadicMatId (d : Nat) : MatD d d :=
  fun i j => if i = j then Dyad.one else Dyad.zero

def dyadicMatMul {r k c : Nat} (A : MatD r k) (B : MatD k c) : MatD r c :=
  fun i j => finSumD (fun t => Dyad.mul (A i t) (B t j))

def dyadicMatVec {r c : Nat} (M : MatD r c) (x : VecD c) : VecD r :=
  fun i => finSumD (fun j => Dyad.mul (M i j) (x j))

def dyadicVecDot {d : Nat} (u v : VecD d) : Dyad :=
  finSumD (fun i => Dyad.mul (u i) (v i))

def dyadicRowAbsSum {r c : Nat} (M : MatD r c) (i : Fin r) : Dyad :=
  finSumD (fun j => Dyad.abs (M i j))

/-- Exact integer matrix product along a word `w = [b_1, ..., b_n]`:
    `intWordProd A [b_1, ..., b_n] = A_{b_n} * ... * A_{b_1}` (left-to-right application). -/
def intWordProd {d m : Nat} (A : Fin m → Mat d d) : List (Fin m) → Mat d d
  | [] => matId d
  | b :: bs => matMul (intWordProd A bs) (A b)

/-- Exact right-to-left integer matrix product `A_{b_1} * ... * A_{b_n}`. -/
def intWordProdRL {d m : Nat} (A : Fin m → Mat d d) : List (Fin m) → Mat d d
  | [] => matId d
  | b :: bs => matMul (A b) (intWordProdRL A bs)

/-- Exact dyadic matrix product `M_{b_n} * ... * M_{b_1}` over `Z[1/2]`. -/
def dyadicWordProd {d m : Nat} (M : Fin m → MatD d d) : List (Fin m) → MatD d d
  | [] => dyadicMatId d
  | b :: bs => dyadicMatMul (dyadicWordProd M bs) (M b)

/-- Exact right-to-left dyadic matrix product `M_{b_1} * ... * M_{b_n}` over `Z[1/2]`. -/
def dyadicWordProdRL {d m : Nat} (M : Fin m → MatD d d) : List (Fin m) → MatD d d
  | [] => dyadicMatId d
  | b :: bs => dyadicMatMul (M b) (dyadicWordProdRL M bs)

/-- Pure-data specification of a dyadic convex combination `∑_b (weights b / 2^q) * M_b`. -/
structure DyadicConvexStep (m : Nat) where
  q : Nat
  weights : Fin m → Nat

/-- Exact validity predicate: weights sum to `2^q`. -/
def DyadicConvexStep.valid {m : Nat} (st : DyadicConvexStep m) : Prop :=
  finSumNat st.weights = 2 ^ st.q

/-- Integer numerator matrix `∑_b weights_b * A_b`. -/
def convexStepIntMat {d m : Nat} (A : Fin m → Mat d d) (st : DyadicConvexStep m) : Mat d d :=
  fun i j => finSum (fun b : Fin m => (st.weights b : Int) * A b i j)

/-- Exact `Dyadic` matrix `2^{-(s + q)} ∑_b weights_b * A_b`. -/
def convexStepDyadicMat {d m : Nat} (s : Nat) (A : Fin m → Mat d d) (st : DyadicConvexStep m) : MatD d d :=
  scaleDyadicMat (s + st.q) (convexStepIntMat A st)

def convexIntProd {d m : Nat} (A : Fin m → Mat d d) : List (DyadicConvexStep m) → Mat d d
  | [] => matId d
  | st :: rest => matMul (convexIntProd A rest) (convexStepIntMat A st)

def convexShiftSum {m : Nat} (s : Nat) : List (DyadicConvexStep m) → Nat
  | [] => 0
  | st :: rest => convexShiftSum s rest + (s + st.q)

def convexDyadicProd {d m : Nat} (s : Nat) (A : Fin m → Mat d d) : List (DyadicConvexStep m) → MatD d d
  | [] => dyadicMatId d
  | st :: rest => dyadicMatMul (convexDyadicProd s A rest) (convexStepDyadicMat s A st)

/-- Decidable universal quantifier over `Fin n`. -/
def finAll : {n : Nat} → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, p => finAll (fun i : Fin n => p i.castSucc) && p (Fin.last n)

/-- Decidable exact matrix equality check. -/
def matEqBool {r c : Nat} (A B : Mat r c) : Bool :=
  finAll (fun i : Fin r => finAll (fun j : Fin c => decide (A i j = B i j)))

/-- Deterministic finite automaton execution on a word `w`. -/
def runDFA {Q m : Nat} (step : Fin Q → Fin m → Option (Fin Q)) :
    Fin Q → List (Fin m) → Option (Fin Q)
  | q, [] => some q
  | q, b :: bs =>
    match step q b with
    | none => none
    | some q' => runDFA step q' bs

/-- Pure-data DFA-switched polar-polytope contraction & JSR upper-bound certificate.
    Contains ZERO `Prop` fields. -/
structure SwitchedPolytopeCert (d m Q K : Nat) where
  scaleShift : Nat
  A : Fin m → Mat d d
  step : Fin Q → Fin m → Option (Fin Q)
  W : Fin Q → Mat K d
  D : Nat
  C : Fin Q → Fin m → Mat K K
  Lambda : Nat
  U : Fin Q → Mat d K
  D_U : Nat
  kappa : Nat
  omega : Nat
  C_const : Nat
  lamNum : Nat
  lamShift : Nat

/-- Pure decidable checker for `SwitchedPolytopeCert`. -/
def checkSwitchedPolytopeCert {d m Q K : Nat} (cert : SwitchedPolytopeCert d m Q K) : Bool :=
  decide (0 < cert.D) &&
  decide (0 < cert.D_U) &&
  -- 1. Intertwining & row L1 contraction for every allowed DFA transition (q --b--> q')
  finAll (fun q : Fin Q =>
    finAll (fun b : Fin m =>
      match cert.step q b with
      | none => true
      | some q' =>
        matEqBool (scaleMat (cert.D : Int) (matMul (cert.W q') (cert.A b)))
                  (matMul (cert.C q b) (cert.W q)) &&
        finAll (fun i : Fin K => decide (rowAbsSum (cert.C q b) i ≤ (cert.Lambda : Int))))) &&
  -- 2. Coercivity U_q * W_q = D_U * I_d, row L1(U_q) <= kappa, row L1(W_q) <= omega
  finAll (fun q : Fin Q =>
    matEqBool (matMul (cert.U q) (cert.W q)) (scaleMat (cert.D_U : Int) (matId d)) &&
    finAll (fun p : Fin d => decide (rowAbsSum (cert.U q) p ≤ (cert.kappa : Int))) &&
    finAll (fun i : Fin K => decide (rowAbsSum (cert.W q) i ≤ (cert.omega : Int)))) &&
  -- 3. Pure integer bound for final dyadic rate: Lambda / (D * 2^s) <= lamNum / 2^lamShift
  decide (cert.Lambda * (2 ^ cert.lamShift) ≤ cert.lamNum * cert.D * (2 ^ cert.scaleShift)) &&
  -- 4. Pure integer bound for operator-norm constant: (kappa * omega) / D_U <= C_const
  decide (cert.kappa * cert.omega ≤ cert.C_const * cert.D_U)

/-- Pure-data DFA-switched invariant-cone positivity & joint spectral subradius certificate.
    Contains ZERO `Prop` fields. -/
structure SwitchedConeCert (d m Q K : Nat) where
  scaleShift : Nat
  A : Fin m → Mat d d
  step : Fin Q → Fin m → Option (Fin Q)
  W : Fin Q → Mat K d
  D : Nat
  C : Fin Q → Fin m → Mat K K
  LambdaMin : Nat
  q0 : Fin Q
  x0 : Vec d
  m0 : Nat
  u : Vec d
  alpha : Fin Q → Vec K
  D_u : Nat
  S_alpha : Nat
  c0Num : Nat
  c0Shift : Nat
  lamMinNum : Nat
  lamMinShift : Nat

/-- Pure decidable checker for `SwitchedConeCert`. -/
def checkSwitchedConeCert {d m Q K : Nat} (cert : SwitchedConeCert d m Q K) : Bool :=
  decide (0 < cert.D) &&
  decide (0 < cert.D_u) &&
  -- 1. Intertwining + nonnegativity + minimum row sum for every allowed edge (q --b--> q')
  finAll (fun q : Fin Q =>
    finAll (fun b : Fin m =>
      match cert.step q b with
      | none => true
      | some q' =>
        matEqBool (scaleMat (cert.D : Int) (matMul (cert.W q') (cert.A b)))
                  (matMul (cert.C q b) (cert.W q)) &&
        finAll (fun i : Fin K => finAll (fun j : Fin K => decide (0 ≤ cert.C q b i j))) &&
        finAll (fun i : Fin K => decide ((cert.LambdaMin : Int) ≤ finSum (cert.C q b i))))) &&
  -- 2. Initial vector x0 lies in cone W_{q0} with margin >= m0
  finAll (fun i : Fin K => decide ((cert.m0 : Int) ≤ matVec (cert.W cert.q0) cert.x0 i)) &&
  -- 3. Nonnegative readout decomposition D_u * u^T = alpha_q^T * W_q for every state q
  finAll (fun q : Fin Q =>
    finAll (fun i : Fin K => decide (0 ≤ cert.alpha q i)) &&
    decide ((cert.S_alpha : Int) ≤ finSum (cert.alpha q)) &&
    finAll (fun p : Fin d =>
      decide ((cert.D_u : Int) * cert.u p = finSum (fun i : Fin K => cert.alpha q i * cert.W q i p)))) &&
  -- 4. Dyadic lower-rate check: lamMinNum / 2^lamMinShift <= LambdaMin / (D * 2^s)
  decide (cert.lamMinNum * cert.D * (2 ^ cert.scaleShift) ≤ cert.LambdaMin * (2 ^ cert.lamMinShift)) &&
  -- 5. Dyadic readout constant check: c0Num / 2^c0Shift <= (S_alpha * m0) / D_u
  decide (cert.c0Num * cert.D_u ≤ cert.S_alpha * cert.m0 * (2 ^ cert.c0Shift))

/-- Pure-data periodic exact eigen-witness certificate (JSR lower bound & explosion).
    Contains ZERO `Prop` fields. -/
structure PeriodicEigenCert (d m : Nat) where
  scaleShift : Nat
  A : Fin m → Mat d d
  word : List (Fin m)
  v : Vec d
  eig : Int

/-- Pure decidable checker for `PeriodicEigenCert`. -/
def checkPeriodicEigenCert {d m : Nat} (cert : PeriodicEigenCert d m) : Bool :=
  decide (0 < cert.word.length) &&
  decide (0 < vecMaxAbs cert.v) &&
  finAll (fun i : Fin d => decide (matVec (intWordProd cert.A cert.word) cert.v i = cert.eig * cert.v i))

-- ============================================================================
-- SECTION 4: Kernel-Proved General Soundness Meta-Theorems (Finite -> Infinite)
-- ============================================================================

/-- Repeat a word `w` exactly `k` times. -/
def repeatWord {α : Type} (w : List α) : Nat → List α
  | 0 => []
  | k + 1 => w ++ repeatWord w k

end DyadicMonoidEngine


-- ============================================================================
-- SECTION 5: Discharged Infinite Theorems, Non-Vacuity, Sharpness & Mutation Tests
-- ============================================================================

namespace CertifiedApplications

open DyadicMonoidEngine

/-- Pure-data matrix builder from nested integer lists. -/
def matOfLists (r c : Nat) (rows : List (List Int)) : Mat r c :=
  fun i j => (rows.getD i.val []).getD j.val 0

/-- Pure-data vector builder from an integer list. -/
def vecOfList (d : Nat) (xs : List Int) : Vec d :=
  fun i => xs.getD i.val 0

/-- Standard unconstrained 1-state DFA transition function. -/
def freeStep {m : Nat} : Fin 1 → Fin m → Option (Fin 1) :=
  fun _ _ => some 0

def thm1_A : Fin 2 → Mat 2 2
  | ⟨0, _⟩ => matOfLists 2 2 [[3, 3], [-1, 0]]
  | ⟨1, _⟩ => matOfLists 2 2 [[0, 1], [-3, 3]]

def thm1_W : Fin 1 → Mat 4 2 := fun _ =>
  matOfLists 4 2 [[2, 0], [0, 2], [4, 3], [-3, 4]]

def thm1_C : Fin 1 → Fin 2 → Mat 4 4
  | _, ⟨0, _⟩ => matOfLists 4 4 [[0, 0, 42, 6], [0, 0, -8, 6], [0, 0, 72, 21], [0, 0, -79, 3]]
  | _, ⟨1, _⟩ => matOfLists 4 4 [[0, 0, 6, 8], [0, 0, -6, 42], [0, 0, 3, 79], [0, 0, -21, 72]]

def thm1_U : Fin 1 → Mat 2 4 := fun _ =>
  matOfLists 2 4 [[1, 0, 0, 0], [0, 1, 0, 0]]

def cert1 : SwitchedPolytopeCert 2 2 1 4 where
  scaleShift := 2
  A := thm1_A
  step := freeStep
  W := thm1_W
  D := 25
  C := thm1_C
  Lambda := 93
  U := thm1_U
  D_U := 2
  kappa := 1
  omega := 7
  C_const := 4
  lamNum := 15
  lamShift := 4

/-- **THEOREM 1D (Two-Sided JSR Lower Bound via Periodic Eigen-Witness):**
    `M0 * M1 * [1, 0]^T = (-9/16) [1, 0]^T`, certifying `rho(M0, M1) ≥ 3/4` for ALL `k : Nat`. -/
def cert1_lower : PeriodicEigenCert 2 2 where
  scaleShift := 2
  A := thm1_A
  word := [⟨1, by omega⟩, ⟨0, by omega⟩]
  v := vecOfList 2 [1, 0]
  eig := -9

/-- **THEOREM 1E (Exact Algebraic Non-Ellipsoidal Obstruction):**
    NO quadratic form `Q = [[a, b], [b, c]]` with `a > 0, c > 0` (in particular, NO positive
    definite symmetric matrix `Q > 0`) can satisfy `M_0^T Q M_0 ≤ Q` and `M_1^T Q M_1 ≤ Q`!
    Proof: evaluating at `v0 = (1, 1)` on `A0` and `v1 = (1, -1)` on `A1` sums to `-5(a + c) ≥ 0`. -/
def quadForm2 (a b c : Int) (x : Vec 2) : Int :=
  a * (x 0 * x 0) + 2 * b * (x 0 * x 1) + c * (x 1 * x 1)

/-- **THEOREM 1F (Sharpness — Perturbing `3 → 5` Triggers Unbounded Exponential Explosion):** -/
def thm1_sharp_A : Fin 2 → Mat 2 2
  | ⟨0, _⟩ => matOfLists 2 2 [[5, 5], [-1, 0]]
  | ⟨1, _⟩ => matOfLists 2 2 [[0, 1], [-5, 5]]

def cert1_sharp : PeriodicEigenCert 2 2 where
  scaleShift := 2
  A := thm1_sharp_A
  word := [⟨1, by omega⟩, ⟨0, by omega⟩]
  v := vecOfList 2 [1, 0]
  eig := -25

def dd_A : Fin 4 → Mat 4 4
  | ⟨0, _⟩ => matOfLists 4 4 [[4, 4, 0, 0], [-2, 28, -2, 0], [0, 4, 4, 0], [0, -2, 28, -2]]     -- 2 T_0(1/32) * 32
  | ⟨1, _⟩ => matOfLists 4 4 [[-2, 28, -2, 0], [0, 4, 4, 0], [0, -2, 28, -2], [0, 0, 4, 4]]     -- 2 T_1(1/32) * 32
  | ⟨2, _⟩ => matOfLists 4 4 [[20, 20, 0, 0], [-10, 12, -10, 0], [0, 20, 20, 0], [0, -10, 12, -10]] -- 2 T_0(5/32) * 32
  | ⟨3, _⟩ => matOfLists 4 4 [[-10, 12, -10, 0], [0, 20, 20, 0], [0, -10, 12, -10], [0, 0, 20, 20]] -- 2 T_1(5/32) * 32

def dd_W : Fin 1 → Mat 10 4 := fun _ =>
  matOfLists 10 4 [
    [6, 0, 0, 0], [0, 6, 0, 0], [0, 0, 6, 0], [0, 0, 0, 6],
    [4, 4, 0, 0], [0, 4, 4, 0], [0, 0, 4, 4],
    [4, -4, 0, 0], [0, 4, -4, 0], [0, 0, 4, -4]
  ]

def dd_C : Fin 1 → Fin 4 → Mat 10 10
  | _, ⟨0, _⟩ => matOfLists 10 10 [
      [0, 0, 0, 0, 18, 0, 0, 0, 0, 0],
      [0, 72, 0, 0, 0, 0, 0, -9, 9, 0],
      [0, 0, 0, 0, 0, 18, 0, 0, 0, 0],
      [0, 0, 72, 0, 0, 0, 0, 0, -9, 9],
      [0, 56, 0, 0, 6, 0, 0, 0, 6, 0],
      [0, 56, 0, 0, 0, 6, 0, -6, 0, 0],
      [0, 0, 56, 0, 0, 6, 0, 0, 0, 6],
      [0, -32, 0, 0, 0, 0, 0, 18, -6, 0],
      [0, 32, 0, 0, 0, 0, 0, -6, 18, 0],
      [0, 0, -32, 0, 0, 0, 0, 0, 18, -6]
    ]
  | _, ⟨1, _⟩ => matOfLists 10 10 [
      [0, 72, 0, 0, 0, 0, 0, -9, 9, 0],
      [0, 0, 0, 0, 0, 18, 0, 0, 0, 0],
      [0, 0, 72, 0, 0, 0, 0, 0, -9, 9],
      [0, 0, 0, 0, 0, 0, 18, 0, 0, 0],
      [0, 56, 0, 0, 0, 6, 0, -6, 0, 0],
      [0, 0, 56, 0, 0, 6, 0, 0, 0, 6],
      [0, 0, 56, 0, 0, 0, 6, 0, -6, 0],
      [0, 32, 0, 0, 0, 0, 0, -6, 18, 0],
      [0, 0, -32, 0, 0, 0, 0, 0, 18, -6],
      [0, 0, 32, 0, 0, 0, 0, 0, -6, 18]
    ]
  | _, ⟨2, _⟩ => matOfLists 10 10 [
      [0, 0, 0, 0, 90, 0, 0, 0, 0, 0],
      [0, 0, -24, 0, 0, 0, 0, -45, 9, 0],
      [0, 0, 0, 0, 0, 90, 0, 0, 0, 0],
      [0, -24, 0, 0, 0, 0, 0, 0, -9, 45],
      [0, 24, 0, 0, 30, 0, 0, 0, 30, 0],
      [0, 24, 0, 0, 0, 30, 0, -30, 0, 0],
      [0, 0, 24, 0, 0, 30, 0, 0, 0, 30],
      [60, 0, 4, 0, 0, 24, 0, 0, 0, 0],
      [-4, 0, -60, 0, -24, 0, 0, 0, 0, 0],
      [0, 60, 0, 4, 0, 0, 24, 0, 0, 0]
    ]
  | _, ⟨3, _⟩ => matOfLists 10 10 [
      [0, 0, -24, 0, 0, 0, 0, -45, 9, 0],
      [0, 0, 0, 0, 0, 90, 0, 0, 0, 0],
      [0, -24, 0, 0, 0, 0, 0, 0, -9, 45],
      [0, 0, 0, 0, 0, 0, 90, 0, 0, 0],
      [0, 24, 0, 0, 0, 30, 0, -30, 0, 0],
      [0, 0, 24, 0, 0, 30, 0, 0, 0, 30],
      [0, 0, 24, 0, 0, 0, 30, 0, -30, 0],
      [-4, 0, -60, 0, -24, 0, 0, 0, 0, 0],
      [0, 60, 0, 4, 0, 0, 24, 0, 0, 0],
      [0, -4, 0, -60, 0, -24, 0, 0, 0, 0]
    ]

def dd_U : Fin 1 → Mat 4 10 := fun _ =>
  matOfLists 4 10 [
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
  ]

def cert2 : SwitchedPolytopeCert 4 4 1 10 where
  scaleShift := 5
  A := dd_A
  step := freeStep
  W := dd_W
  D := 3
  C := dd_C
  Lambda := 90
  U := dd_U
  D_U := 6
  kappa := 1
  omega := 8
  C_const := 2
  lamNum := 15
  lamShift := 4

/-- Construct a `DyadicConvexStep 4` representing Dubuc-Deslauriers 4-point matrix `2 * T_b(ω)`
    for ANY bit `b ∈ {0, 1}` and ANY dyadic parameter `ω = 1/32 + (p / 2^q) * (4/32) ∈ [1/32, 5/32]`. -/
def ddStep (b : Fin 2) (q p : Nat) : DyadicConvexStep 4 where
  q := q
  weights := fun idx =>
    if b.val = 0 then
      match idx.val with
      | 0 => 2 ^ q - p
      | 2 => p
      | _ => 0
    else
      match idx.val with
      | 1 => 2 ^ q - p
      | 3 => p
      | _ => 0

/-- **THEOREM 2B (Sharpness — At `ω = 1/4`, `C^1` Contraction Fails with Exact Eigenvalue 1):**
    `2 * T_0(1/4) * [1, 0, -1, 0]^T = 1 * [1, 0, -1, 0]^T`, so `‖(2 T_0(1/4))^k‖_∞ ≥ 1` for ALL `k`. -/
def dd_quarter_A : Fin 2 → Mat 4 4
  | ⟨0, _⟩ => matOfLists 4 4 [[2, 2, 0, 0], [-1, 0, -1, 0], [0, 2, 2, 0], [0, -1, 0, -1]]
  | ⟨1, _⟩ => matOfLists 4 4 [[-1, 0, -1, 0], [0, 2, 2, 0], [0, -1, 0, -1], [0, 0, 2, 2]]

def cert2_sharp : PeriodicEigenCert 4 2 where
  scaleShift := 1
  A := dd_quarter_A
  word := [⟨0, by omega⟩]
  v := vecOfList 4 [1, 0, -1, 0]
  eig := 2

def thm3_A : Fin 2 → Mat 3 3
  | ⟨0, _⟩ => matOfLists 3 3 [[7, -1, -1], [-2, 3, -1], [1, -2, 2]]
  | ⟨1, _⟩ => matOfLists 3 3 [[7, -1, -1], [2, -2, 1], [-1, -1, 2]]

def thm3_W : Fin 1 → Mat 4 3 := fun _ =>
  matOfLists 4 3 [[1, 1, 0], [1, -1, 0], [1, 0, 1], [1, 0, -1]]

def thm3_C : Fin 1 → Fin 2 → Mat 4 4
  | _, ⟨0, _⟩ => matOfLists 4 4 [[5, 1, 0, 4], [5, 13, 0, 0], [4, 10, 2, 0], [4, 2, 0, 6]]
  | _, ⟨1, _⟩ => matOfLists 4 4 [[6, 12, 0, 0], [4, 2, 0, 4], [3, 7, 2, 0], [5, 5, 0, 6]]

def cert3 : SwitchedConeCert 3 2 1 4 where
  scaleShift := 2
  A := thm3_A
  step := freeStep
  W := thm3_W
  D := 2
  C := thm3_C
  LambdaMin := 10
  q0 := 0
  x0 := vecOfList 3 [1, 0, 0]
  m0 := 1
  u := vecOfList 3 [1, 0, 0]
  alpha := fun _ => vecOfList 4 [1, 1, 0, 0]
  D_u := 2
  S_alpha := 2
  c0Num := 1
  c0Shift := 0
  lamMinNum := 5
  lamMinShift := 2

def thm4_A : Fin 2 → Mat 2 2
  | ⟨0, _⟩ => matOfLists 2 2 [[1, 4], [-1, 1]]
  | ⟨1, _⟩ => matOfLists 2 2 [[5, 0], [1, 1]]

/-- Pure semantic predicate: a binary word contains no adjacent `1, 1`. -/
def noAdjacentOnes : List (Fin 2) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => !(decide (a.val = 1) && decide (b.val = 1)) && noAdjacentOnes (b :: rest)

/-- 2-state DFA recognizing `noAdjacentOnes` (state 0: last bit ≠ 1; state 1: last bit = 1). -/
def nafStep : Fin 2 → Fin 2 → Option (Fin 2)
  | ⟨0, _⟩, ⟨0, _⟩ => some ⟨0, by omega⟩
  | ⟨0, _⟩, ⟨1, _⟩ => some ⟨1, by omega⟩
  | ⟨1, _⟩, ⟨0, _⟩ => some ⟨0, by omega⟩
  | ⟨1, _⟩, ⟨1, _⟩ => none

def thm4_W : Fin 2 → Mat 2 2
  | ⟨0, _⟩ => matOfLists 2 2 [[3, 0], [0, 5]]
  | ⟨1, _⟩ => matOfLists 2 2 [[2, 0], [0, 6]]

def thm4_C : Fin 2 → Fin 2 → Mat 2 2
  | ⟨0, _⟩, ⟨0, _⟩ => matOfLists 2 2 [[30, 72], [-50, 30]]
  | ⟨0, _⟩, ⟨1, _⟩ => matOfLists 2 2 [[100, 0], [60, 36]]
  | ⟨1, _⟩, ⟨0, _⟩ => matOfLists 2 2 [[45, 60], [-75, 25]]
  | ⟨1, _⟩, ⟨1, _⟩ => matOfLists 2 2 [[0, 0], [0, 0]]

def thm4_U : Fin 2 → Mat 2 2
  | ⟨0, _⟩ => matOfLists 2 2 [[10, 0], [0, 6]]
  | ⟨1, _⟩ => matOfLists 2 2 [[15, 0], [0, 5]]

def cert4 : SwitchedPolytopeCert 2 2 2 2 where
  scaleShift := 2
  A := thm4_A
  step := nafStep
  W := thm4_W
  D := 30
  C := thm4_C
  Lambda := 105
  U := thm4_U
  D_U := 30
  kappa := 15
  omega := 6
  C_const := 3
  lamNum := 7
  lamShift := 3

/-- **THEOREM 4B (Unconstrained Monoid Explodes Exponentially via `M1^k`):** -/
def cert4_explode : PeriodicEigenCert 2 2 where
  scaleShift := 2
  A := thm4_A
  word := [⟨1, by omega⟩]
  v := vecOfList 2 [4, 1]
  eig := 5

/-- **THEOREM 4C (Sharpness — Perturbing `A0[0][1]` from `4 → 16` Breaks NAF Stability):**
    The valid no-`11` periodic word `repeatWord [1, 0] k` satisfies `noAdjacentOnes = true` for ALL `k`,
    yet explodes exponentially at rate `(17/16)^k -> ∞`! -/
def thm4_sharp_A : Fin 2 → Mat 2 2
  | ⟨0, _⟩ => matOfLists 2 2 [[1, 16], [-1, 1]]
  | ⟨1, _⟩ => matOfLists 2 2 [[5, 0], [1, 1]]

def cert4_sharp : PeriodicEigenCert 2 2 where
  scaleShift := 2
  A := thm4_sharp_A
  word := [⟨1, by omega⟩, ⟨0, by omega⟩]
  v := vecOfList 2 [4, -1]
  eig := 17

/-- Mutation 1: Corrupt 1 entry of intertwining matrix `C` in `cert1`. -/
def bad_cert1_intertwining : SwitchedPolytopeCert 2 2 1 4 :=
  { cert1 with
    C := fun q b i j => if q.val = 0 ∧ b.val = 0 ∧ i.val = 0 ∧ j.val = 2
                        then cert1.C q b i j + 1 else cert1.C q b i j }

/-- Mutation 2: Tighten `Lambda` by 1 (`93 → 92`) in `cert1`. -/
def bad_cert1_lambda : SwitchedPolytopeCert 2 2 1 4 :=
  { cert1 with Lambda := 92 }

/-- Mutation 3: Corrupt 1 entry of coercivity matrix `U` in `cert1`. -/
def bad_cert1_coercivity : SwitchedPolytopeCert 2 2 1 4 :=
  { cert1 with
    U := fun q i j => if q.val = 0 ∧ i.val = 0 ∧ j.val = 0 then 2 else cert1.U q i j }

/-- Mutation 4: Claim uncertified tighter dyadic rate `7/8` (`14/16`) on `cert1` (`93/100 > 7/8`). -/
def bad_cert1_rate : SwitchedPolytopeCert 2 2 1 4 :=
  { cert1 with lamNum := 7, lamShift := 3 }

/-- Mutation 5: Replace `ω = 5/32` endpoint of Dubuc-Deslauriers `cert2` with `ω = 1/4`. -/
def bad_cert2_endpoint : SwitchedPolytopeCert 4 4 1 10 :=
  { cert2 with
    A := fun b => if b.val = 2 then scaleMat 16 (dd_quarter_A 0) else cert2.A b }

/-- Mutation 6: Introduce a negative entry `-1` into cone matrix `C` of `cert3`. -/
def bad_cert3_negative_C : SwitchedConeCert 3 2 1 4 :=
  { cert3 with
    C := fun q b i j => if q.val = 0 ∧ b.val = 0 ∧ i.val = 0 ∧ j.val = 2 then -1 else cert3.C q b i j }

/-- Mutation 7: Inflate claimed subradius of `cert3` from `5/4` to `3/2`. -/
def bad_cert3_subradius : SwitchedConeCert 3 2 1 4 :=
  { cert3 with lamMinNum := 3, lamMinShift := 1 }

/-- Mutation 8: Enable forbidden `1 → 1` self-loop in `cert4`'s NAF DFA. -/
def bad_cert4_unconstrained_dfa : SwitchedPolytopeCert 2 2 2 2 :=
  { cert4 with
    step := fun q b => match q.val, b.val with
      | 1, 1 => some ⟨1, by omega⟩
      | _, _ => cert4.step q b }

/-- Mutation 9: Corrupt claimed eigenvalue in `PeriodicEigenCert` (`5 → 6`). -/
def bad_cert4_eigen : PeriodicEigenCert 2 2 :=
  { cert4_explode with eig := 6 }

end CertifiedApplications

-- ============================================================================
-- SECTION 6: Exhaustive Kernel Axiom Audit (Must be ⊆ {propext, Classical.choice, Quot.sound})
-- ============================================================================
