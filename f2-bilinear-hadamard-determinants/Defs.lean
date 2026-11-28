import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Basic

namespace F2BilinearHadamard

/-- Binary popcount (Hamming weight) of a natural number. -/
def popcount (n : ℕ) : ℕ :=
  if _ : n = 0 then 0 else (n % 2) + popcount (n / 2)
termination_by n
decreasing_by omega

/-- Parity XOR sum `⨁_{r ∈ bits(n)} f r` over the set bits of `n`. -/
def bitXorSum (f : ℕ → Bool) (n : ℕ) : Bool :=
  bitXorSumAux f 0 n
where
  bitXorSumAux (f : ℕ → Bool) (r n : ℕ) : Bool :=
    if _ : n = 0 then false
    else xor (if n % 2 = 1 then f r else false) (bitXorSumAux f (r + 1) (n / 2))
  termination_by n
  decreasing_by omega

/-- The `𝔽₂`-bilinear form `B_A(i, j) = iᵀ A j ∈ 𝔽₂` induced by any infinite bit-matrix
`A : ℕ → ℕ → Bool`. -/
def f2Bilin (A : ℕ → ℕ → Bool) (i j : ℕ) : Bool :=
  bitXorSum (fun r => bitXorSum (fun s => A r s) j) i

/-- Exact sign `∏_{r ∈ bits(k)} (-1)^{A r r} ∈ {+1, -1}` in any ring `R`. -/
def diagSign {R : Type*} [Ring R] (A : ℕ → ℕ → Bool) (k : ℕ) : R :=
  if bitXorSum (fun r => A r r) k then -1 else 1

/-- Two-parameter `(a, b)` binary-value matrix `M_n(A; a, b)_{i, j} = if B_A(i, j) then b else a`. -/
def bilinCharMat {R : Type*} (A : ℕ → ℕ → Bool) (a b : R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if f2Bilin A i.1 j.1 then b else a

/-- Standard `±1` Walsh-Hadamard character matrix `W_n(A)_{i, j} = (-1)^{B_A(i, j)}`. -/
def walshCharMat {R : Type*} [Ring R] (A : ℕ → ℕ → Bool) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  bilinCharMat A (1 : R) (-1 : R) n

/-- Identity bit-matrix `I_{r, s} = δ_{r, s}` (standard Walsh-Hadamard form `popcount(i & j) mod 2`). -/
def stdBitMat (r s : ℕ) : Bool :=
  decide (r = s)

/-- Sierpinski-Lucas-Pascal bit-matrix `P_{r, s} = C(r + s, r) mod 2 = 1_{(r &&& s) = 0}`. -/
def sierpinskiBitMat (r s : ℕ) : Bool :=
  decide ((r &&& s) = 0)

/-- Exact `𝔽₂`-Cholesky pivot `p_d = ∑_{r < d, (r &&& d) = r} 2^r` for `sierpinskiBitMat`. -/
def sierpinskiPivot (d : ℕ) : ℕ :=
  (Finset.range d).sum fun r => if (r &&& d) = r then 2 ^ r else 0

/-- Structurally recursive Conway nimber multiplication at Fermat tower level `k`
(exact nimber multiplication on the field `𝔽_{2^(2^k)} = [0, 2^(2^k))`). -/
def nimMulLevel : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => (a % 2) * (b % 2)
  | k + 1, a, b =>
    let half := 2 ^ k
    let base := 2 ^ half
    let a0 := a % base
    let a1 := a / base
    let b0 := b % base
    let b1 := b / base
    let p0 := nimMulLevel k a0 b0
    let p1 := nimMulLevel k a1 b1
    let p2 := nimMulLevel k (a0 ^^^ a1) (b0 ^^^ b1)
    let lo := p0 ^^^ nimMulLevel k p1 (2 ^ (half - 1))
    let hi := p2 ^^^ p0
    (hi * base) ^^^ lo

/-- Conway nimber multiplication on `𝔽_{2^8} = [0, 256)` (`k = 3`). -/
def nimMul (a b : ℕ) : ℕ :=
  nimMulLevel 3 a b

/-- Conway nimber `𝔽₂`-popcount Gram matrix `G_{r, s} = popcount(2^r ⊗ 2^s) mod 2` on `𝔽_{2^8}`. -/
def nimBitMat (r s : ℕ) : Bool :=
  decide (popcount (nimMul (2 ^ r) (2 ^ s)) % 2 = 1)

/-- All-ones carryless `𝔽₂[X]`-multiplication Gram matrix (`popcount(2^r ⊗_cl 2^s) = 1`). -/
def clmulBitMat (_r _s : ℕ) : Bool :=
  true

end F2BilinearHadamard
