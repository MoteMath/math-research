/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Definitions (`walsh-mobius-runs-dihedral-spectra`)

Walsh-Hadamard and Boolean-Lattice Mobius Diagonalization Engine: definitions and sorry-free helper lemmas (pure Lean 4 `Init`, zero Mathlib).
-/

namespace SpecMat2

def listSum {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldr (fun x acc => f x + acc) 0

def listProd {α : Type} (l : List α) (f : α → Int) : Int :=
  l.foldr (fun x acc => f x * acc) 1

def finList (n : Nat) : List (Fin n) := List.finRange n

def sumFin (n : Nat) (f : Fin n → Int) : Int := listSum (finList n) f

def prodFin (n : Nat) (f : Fin n → Int) : Int := listProd (finList n) f

def snocFunc {m n : Nat} (g : Fin m → Fin n) (y : Fin n) : Fin (m + 1) → Fin n :=
  fun i => if h : i.val < m then g ⟨i.val, h⟩ else y

def initFunc {m n : Nat} (f : Fin (m + 1) → Fin n) : Fin m → Fin n :=
  fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

def lastFunc {m n : Nat} (f : Fin (m + 1) → Fin n) : Fin n :=
  f ⟨m, Nat.lt_succ_self m⟩

def allFuncs (n : Nat) : (m : Nat) → List (Fin m → Fin n)
  | 0 => [Fin.elim0]
  | m + 1 => (finList n).flatMap fun y => (allFuncs n m).map fun g => snocFunc g y

def finInv {n : Nat} (g : Fin n → Fin n) (y : Fin n) : Fin n :=
  match (finList n).find? (fun x => decide (g x = y)) with
  | some x => x
  | none => y

def cmpSign (a b : Nat) : Int :=
  if a < b then 1 else if b < a then -1 else 0

def orderedPairs (n : Nat) : List (Fin n × Fin n) :=
  (finList n).flatMap fun i =>
    ((finList n).filter fun j => decide (i.val < j.val)).map fun j => (i, j)

def permSign {n : Nat} (f : Fin n → Fin n) : Int :=
  listProd (orderedPairs n) (fun p => cmpSign (f p.1).val (f p.2).val)

def swapFin {n : Nat} (a b : Fin n) (i : Fin n) : Fin n :=
  if i = a then b else if i = b then a else i

abbrev Mat (n : Nat) := Fin n → Fin n → Int

def matId (n : Nat) : Mat n := fun i j => if i = j then 1 else 0

def matDiag {n : Nat} (d : Fin n → Int) : Mat n := fun i j => if i = j then d i else 0

def matMul {n : Nat} (A B : Mat n) : Mat n := fun i j => sumFin n (fun k => A i k * B k j)

def matTranspose {n : Nat} (A : Mat n) : Mat n := fun i j => A j i

def matScale {n : Nat} (c : Int) (A : Mat n) : Mat n := fun i j => c * A i j

def matSub {n : Nat} (A B : Mat n) : Mat n := fun i j => A i j - B i j

def det {n : Nat} (A : Mat n) : Int :=
  listSum (allFuncs n n) (fun f => permSign f * prodFin n (fun i => A i (f i)))

def popcount : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)

/-- `(-1)^n : Int`. -/
def signPow (n : Nat) : Int := if n % 2 = 0 then 1 else -1

theorem nat_xor_lt_pow2 {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    x ^^^ y < 2 ^ k := Nat.xor_lt_two_pow hx hy

def finEven {k : Nat} (q : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨2 * q.val, by have := q.isLt; rw [Nat.pow_succ]; omega⟩

def finOdd {k : Nat} (q : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨2 * q.val + 1, by have := q.isLt; rw [Nat.pow_succ]; omega⟩

def hadamardMat (k : Nat) : Mat (2 ^ k) :=
  fun u v => signPow (popcount (u.val &&& v.val))

def xorConvMat (k : Nat) (f : Nat → Int) : Mat (2 ^ k) :=
  fun x y => f (x.val ^^^ y.val)

def wht (k : Nat) (f : Nat → Int) (u : Nat) : Int :=
  sumFin (2 ^ k) (fun z => signPow (popcount (u &&& z.val)) * f z.val)

def zetaMat (k : Nat) : Mat (2 ^ k) :=
  fun x y => if (x.val &&& y.val) = y.val then 1 else 0

def mobiusMat (k : Nat) : Mat (2 ^ k) :=
  fun x y => if (x.val &&& y.val) = y.val then signPow (popcount (x.val ^^^ y.val)) else 0

def andLatticeMat (k : Nat) (g : Nat → Int) : Mat (2 ^ k) :=
  fun x y => g (x.val &&& y.val)

def orLatticeMat (k : Nat) (g : Nat → Int) : Mat (2 ^ k) :=
  fun x y => g (x.val ||| y.val)

def mobiusDown (k : Nat) (g : Nat → Int) (z : Nat) : Int :=
  sumFin (2 ^ k) (fun w => if (z &&& w.val) = w.val then signPow (popcount (z ^^^ w.val)) * g w.val else 0)

def mobiusUp (k : Nat) (g : Nat → Int) (z : Nat) : Int :=
  sumFin (2 ^ k) (fun w => if (w.val &&& z) = z then signPow (popcount (w.val ^^^ z)) * g w.val else 0)

def quadForm {n : Nat} (A : Mat n) (v : Fin n → Int) : Int :=
  sumFin n (fun x => sumFin n (fun y => v x * A x y * v y))

/-- Exact OR-lattice Möbius inversion & determinant via bit-complement duality `x ↦ (2^k - 1) ^^^ x`. -/
def bitComp (k : Nat) (x : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨(2 ^ k - 1) ^^^ x.val, nat_xor_lt_pow2 (by have := Nat.two_pow_pos k; omega) x.isLt⟩

def matAdd {n : Nat} (A B : Mat n) : Mat n := fun i j => A i j + B i j

/-- Bilinear contraction `αᵀ M β` for a `d × d` integer matrix `M`. -/
def contract {d : Nat} (α : Fin d → Int) (M : Mat d) (β : Fin d → Int) : Int :=
  sumFin d (fun i => sumFin d (fun j => α i * M i j * β j))

/-- A finite `d`-state bit-slice weighted automaton `(α, T₀, T₁, β)`. -/
structure BitAutomaton (d : Nat) where
  α : Fin d → Int
  T0 : Mat d
  T1 : Mat d
  β : Fin d → Int

/-- Exact `k`-bit MSB-to-LSB transfer product `T_{z_{k-1}} ⋯ T_{z_0}` defined by LSB recursion. -/
def evalWord {d : Nat} (T0 T1 : Mat d) : Nat → Nat → Mat d
  | 0, _ => matId d
  | k + 1, z => matMul (evalWord T0 T1 k (z / 2)) (if z % 2 = 0 then T0 else T1)

/-- Kernel evaluated by a `d`-state bit-slice automaton on `k`-bit integer `z`. -/
def evalAuto {d : Nat} (A : BitAutomaton d) (k : Nat) (z : Nat) : Int :=
  contract A.α (evalWord A.T0 A.T1 k z) A.β

/-- Compiled Walsh-Hadamard automaton: `(T₀ + T₁, T₀ - T₁)`. -/
def whtAuto {d : Nat} (A : BitAutomaton d) : BitAutomaton d :=
  { α := A.α, T0 := matAdd A.T0 A.T1, T1 := matSub A.T0 A.T1, β := A.β }

/-- Compiled downward Boolean Möbius automaton (AND-lattice): `(T₀, T₁ - T₀)`. -/
def mobiusDownAuto {d : Nat} (A : BitAutomaton d) : BitAutomaton d :=
  { α := A.α, T0 := A.T0, T1 := matSub A.T1 A.T0, β := A.β }

/-- Compiled upward Boolean Möbius automaton (OR-lattice): `(T₀ - T₁, T₁)`. -/
def mobiusUpAuto {d : Nat} (A : BitAutomaton d) : BitAutomaton d :=
  { α := A.α, T0 := matSub A.T0 A.T1, T1 := A.T1, β := A.β }

/-- Exact matrix power `M^n` over `Mat d`. -/
def matPow {d : Nat} (M : Mat d) : Nat → Mat d
  | 0 => matId d
  | n + 1 => matMul (matPow M n) M

/-- A finite `d × d` **Scaled-Dihedral Certificate** `(A, Abar, S, c)`:
    zero-division ring equations verifiable on finite `d × d` matrices, which automatically collapse
    ALL `k`-bit transfer words `evalWord A S k u` (for all `k ∈ Nat`, all `u < 2^k`) to a single closed-form
    function of the inverse Gray code Hamming weight `popcount (invGray u)`! -/
structure ScaledDihedralCert (d : Nat) where
  A : Mat d
  Abar : Mat d
  S : Mat d
  c : Int
  hS2 : matMul S S = matScale c (matId d)
  hAAbar : matMul A Abar = matScale c (matId d)
  hAbarA : matMul Abar A = matScale c (matId d)
  hSA : matMul S A = matMul Abar S

/-- Inverse Gray code `G⁻¹(u)` defined by LSB recursion:
    `invGray (2q + b) = 2 * invGray q + ((invGray q % 2) ^^^ b)`. -/
def invGray : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let g := invGray ((n + 1) / 2)
    2 * g + ((g % 2) ^^^ ((n + 1) % 2))

/-- Gray code `gray(w) = w ^^^ (w / 2)` is the exact two-sided inverse of `invGray`! -/
def grayCode (w : Nat) : Nat := w ^^^ (w / 2)

/-- Signed power `P(e) = A^e` if `e ≥ 0`, else `Abar^(-e)`. -/
def signedPow {d : Nat} (A Abar : Mat d) (e : Int) : Mat d :=
  if e ≥ 0 then matPow A e.toNat else matPow Abar (-e).toNat

theorem sumFin_two (F : Fin 2 → Int) : sumFin 2 F = F ⟨0, by omega⟩ + F ⟨1, by omega⟩ := by
  unfold sumFin finList listSum
  simp [List.finRange]

theorem fin2_cases (i : Fin 2) : i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ := by
  cases i with
  | mk v hv =>
    have h : v = 0 ∨ v = 1 := by omega
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Number of maximal `1`-bit runs (equivalently `0 -> 1` bit-rises) in binary representation of `z`. -/
def runs : Nat → Nat
  | 0 => 0
  | n + 1 =>
    runs ((n + 1) / 2) + (if (n + 1) % 2 = 1 ∧ ((n + 1) / 2) % 2 = 0 then 1 else 0)

def falls (z : Nat) : Nat := runs z - z % 2

def transKernel (q s : Int) (z : Nat) : Int :=
  q ^ (runs z) * s ^ (falls z)

def runsKernel (q : Int) (z : Nat) : Int := q ^ (runs z)

def transAuto (q s : Int) : BitAutomaton 2 where
  α := fun i => if i.val = 0 then 1 else 0
  T0 := fun i j => if j.val = 0 then (if i.val = 0 then 1 else s) else 0
  T1 := fun i j => if j.val = 1 then (if i.val = 0 then q else 1) else 0
  β := fun _ => 1

def pellQ (q : Int) : Nat → Int
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * pellQ q (n + 1) + (q - 1) * pellQ q n

def transDihedralCert (q s : Int) : ScaledDihedralCert 2 where
  A := matAdd (transAuto q s).T0 (transAuto q s).T1
  Abar := fun i j =>
    if i.val = 0 then (if j.val = 0 then 1 else -q)
    else (if j.val = 0 then -s else 1)
  S := matSub (transAuto q s).T0 (transAuto q s).T1
  c := 1 - q * s
  hS2 := by
    funext i j; unfold matMul matSub matScale matId transAuto
    rw [sumFin_two]
    rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
      (simp [Int.neg_mul, Int.mul_neg]; (try rw [Int.mul_comm s q]); omega)
  hAAbar := by
    funext i j; unfold matMul matAdd matScale matId transAuto
    rw [sumFin_two]
    rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
      (simp [Int.mul_neg]; (try rw [Int.mul_comm s q]); omega)
  hAbarA := by
    funext i j; unfold matMul matAdd matScale matId transAuto
    rw [sumFin_two]
    rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;>
      (simp [Int.neg_mul]; (try rw [Int.mul_comm s q]); omega)
  hSA := by
    funext i j; unfold matMul matAdd matSub transAuto
    rw [sumFin_two, sumFin_two]
    rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl
    · simp [Int.neg_mul]
    · simp [Int.mul_neg]; omega
    · simp [Int.neg_mul]; omega
    · simp [Int.neg_mul, Int.mul_neg]

def mobiusRay (q s : Int) : Nat → Nat → Int × Bool
  | 0, _ => (1, false)
  | k + 1, z =>
    let st := mobiusRay q s k (z / 2)
    if z % 2 = 0 then
      if st.2 then (st.1 * (q * s - 1), false) else (st.1, false)
    else
      if st.2 then (st.1 * (1 - q * s), false) else (st.1, true)

def oddTrail : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, z => if z % 2 = 0 then false else !(oddTrail k (z / 2))

def jacobsthal : Nat → Nat
  | 0 => 0
  | k + 1 => 2 ^ k - jacobsthal k

def countOddTrail (k : Nat) : Nat :=
  (finList (2 ^ k)).foldr (fun z acc => (if oddTrail k z.val then 1 else 0) + acc) 0

def transExp : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * transExp k + 2 * jacobsthal k

def brokenKernel (z : Nat) : Int := (2 : Int) ^ (popcount z) * (2 : Int) ^ (runs z)

end SpecMat2
