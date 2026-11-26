/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Public Definitions (`paley32-mxfp4-outliers`)

Pure Lean 4 `Init` (zero Mathlib) definitions for:
1. Finite sums and integer / rational matrix algebra (`IntMat`, `RatMat`, `isOrthogonal`, `isOrthogonalRat`).
2. Sparse signed vectors (`isSignedSparse`), `ℓ_2^2` and `ℓ_4^4` moments, and peak-multiplicity counters (`maxC4`, `countAbsEq`).
3. Explicit Hadamard matrices: Sylvester (`sylvester16`, `sylvester32`), Paley-32 (`paley32`), and all five Hall (1961) equivalence classes (`hall16_I` .. `hall16_V`).
4. The 4-variable bent diagonal twist (`bentDiag16`, `diagTwist`) and affine 2-planes in `𝔽_2^4`.
5. OCP MXFP4 / MXFP6 block bit budgets (`mxfp4HybridBits`, `mxfp6BlockBits`).
-/

namespace Paley32Mxfp4

/-! ### 1. Finite Sums and Basic Matrix Algebra -/

def sumFinRat : (n : Nat) → (Fin n → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => sumFinRat n (fun i => f i.castSucc) + f (Fin.last n)

def sumFinInt : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFinInt n (fun i => f i.castSucc) + f (Fin.last n)

def sumFinNat : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumFinNat n (fun i => f i.castSucc) + f (Fin.last n)

abbrev RatMat (m n : Nat) := Fin m → Fin n → Rat
abbrev IntMat (m n : Nat) := Fin m → Fin n → Int

def transposeRat {m n : Nat} (A : RatMat m n) : RatMat n m :=
  fun i j => A j i

def idMatRat (n : Nat) : RatMat n n :=
  fun i j => if i = j then 1 else 0

def scaleMatRat {m n : Nat} (c : Rat) (A : RatMat m n) : RatMat m n :=
  fun i j => c * A i j

def matMulRat {m k n : Nat} (A : RatMat m k) (B : RatMat k n) : RatMat m n :=
  fun i j => sumFinRat k (fun t => A i t * B t j)

def isOrthogonalRat {n : Nat} (U : RatMat n n) (c : Rat) : Prop :=
  matMulRat (transposeRat U) U = scaleMatRat c (idMatRat n)

def matVecRat {m n : Nat} (A : RatMat m n) (x : Fin n → Rat) : Fin m → Rat :=
  fun i => sumFinRat n (fun j => A i j * x j)

def sumSqRat {n : Nat} (v : Fin n → Rat) : Rat :=
  sumFinRat n (fun i => v i * v i)

def transpose {m n : Nat} (A : IntMat m n) : IntMat n m :=
  fun i j => A j i

def idMat (n : Nat) : IntMat n n :=
  fun i j => if i = j then 1 else 0

def scaleMat {m n : Nat} (c : Int) (A : IntMat m n) : IntMat m n :=
  fun i j => c * A i j

def matMul {m k n : Nat} (A : IntMat m k) (B : IntMat k n) : IntMat m n :=
  fun i j => sumFinInt k (fun t => A i t * B t j)

def isOrthogonal {n : Nat} (H : IntMat n n) (c : Int) : Prop :=
  matMul (transpose H) H = scaleMat c (idMat n)

def matVec {m n : Nat} (A : IntMat m n) (x : Fin n → Int) : Fin m → Int :=
  fun i => sumFinInt n (fun j => A i j * x j)

def sumSqInt {n : Nat} (v : Fin n → Int) : Int :=
  sumFinInt n (fun i => v i * v i)

def sumFourthInt {n : Nat} (v : Fin n → Int) : Int :=
  sumFinInt n (fun i => v i * v i * v i * v i)

/-! ### 2. Sparse Supports, Signed Vectors, and Peak Multiplicities -/

def isInjective {k n : Nat} (S : Fin k → Fin n) : Prop :=
  ∀ a b : Fin k, S a = S b → a = b

def isSignedSparse {n : Nat} (k : Nat) (x : Fin n → Int) : Prop :=
  (∀ j : Fin n, x j = -1 ∨ x j = 0 ∨ x j = 1) ∧
  sumFinNat n (fun j => if x j = 0 then 0 else 1) = k

def supportVec {n : Nat} (S : List Nat) : Fin n → Int :=
  fun j => if j.val ∈ S then 1 else 0

def countAbsEq {n : Nat} (v : Fin n → Int) (t : Nat) : Nat :=
  sumFinNat n (fun i => if (v i).natAbs = t then 1 else 0)

/-- Number of rows `r` achieving `|H[r,c0] + s1*H[r,c1] + s2*H[r,c2] + s3*H[r,c3]| = 4`. -/
def c4ForSigns {n : Nat} (H : IntMat n n) (c0 c1 c2 c3 : Fin n) (s1 s2 s3 : Int) : Nat :=
  sumFinNat n (fun r =>
    if (H r c0 + s1 * H r c1 + s2 * H r c2 + s3 * H r c3).natAbs = 4 then 1 else 0)

/-- Maximum peak-4 multiplicity over all 8 sign patterns `(1, s1, s2, s3) ∈ {±1}^4` on `{c0,c1,c2,c3}`. -/
def maxC4 {n : Nat} (H : IntMat n n) (c0 c1 c2 c3 : Fin n) : Nat :=
  let m0 := c4ForSigns H c0 c1 c2 c3 1 1 1
  let m1 := c4ForSigns H c0 c1 c2 c3 (-1) 1 1
  let m2 := c4ForSigns H c0 c1 c2 c3 1 (-1) 1
  let m3 := c4ForSigns H c0 c1 c2 c3 (-1) (-1) 1
  let m4 := c4ForSigns H c0 c1 c2 c3 1 1 (-1)
  let m5 := c4ForSigns H c0 c1 c2 c3 (-1) 1 (-1)
  let m6 := c4ForSigns H c0 c1 c2 c3 1 (-1) (-1)
  let m7 := c4ForSigns H c0 c1 c2 c3 (-1) (-1) (-1)
  max (max (max m0 m1) (max m2 m3)) (max (max m4 m5) (max m6 m7))

/-! ### 3. Explicit Hadamard Matrices: Sylvester, Paley-32, Hall-16 (Classes I–V) -/

/-- Popcount of the low 6 bits of a natural number (exact for all `x < 64`). -/
def popcount6 (x : Nat) : Nat :=
  (x &&& 1) + ((x >>> 1) &&& 1) + ((x >>> 2) &&& 1) +
  ((x >>> 3) &&& 1) + ((x >>> 4) &&& 1) + ((x >>> 5) &&& 1)

def sylvesterMat (n : Nat) : IntMat n n :=
  fun i j => if popcount6 (i.val &&& j.val) % 2 = 0 then 1 else -1

def sylvester16 : IntMat 16 16 := sylvesterMat 16
def sylvester32 : IntMat 32 32 := sylvesterMat 32

/-- Nonzero quadratic residues modulo `31`. -/
def isQR31 (d : Nat) : Bool :=
  match d % 31 with
  | 1 | 2 | 4 | 5 | 7 | 8 | 9 | 10 | 14 | 16 | 18 | 19 | 20 | 25 | 28 => true
  | _ => false

/-- Paley Type I `32 × 32` Hadamard matrix (`p = 31 ≡ 3 (mod 4)`). -/
def paley32 : IntMat 32 32 := fun i j =>
  if i.val = 0 then 1
  else if j.val = 0 then -1
  else
    let d := ((i.val - 1) + 31 - (j.val - 1)) % 31
    if d = 0 then 1
    else if isQR31 d then 1
    else -1

/-- Decode a `16 × 16` `±1` matrix from 16 column bitmasks (bit `r` = 1 iff `H[r, c] = -1`). -/
def matFromColMasks16 (masks : Array Nat) : IntMat 16 16 :=
  fun r c => if ((masks.getD c.val 0) >>> r.val) &&& 1 = 1 then -1 else 1

def hall16_I_masks : Array Nat :=
  #[0, 43690, 52428, 26214, 61680, 23130, 15420, 38550,
    65280, 21930, 13260, 39270, 4080, 42330, 49980, 27030]

def hall16_II_masks : Array Nat :=
  #[26112, 4010, 23244, 13158, 65520, 38490, 43580, 15510,
    39168, 61610, 42444, 52326, 240, 26970, 21820, 50070]

def hall16_III_masks : Array Nat :=
  #[15360, 170, 21964, 52326, 4080, 42330, 39228, 27030,
    49920, 65450, 43724, 13158, 61680, 23130, 26172, 38550]

def hall16_IV_masks : Array Nat :=
  #[65280, 50090, 27084, 52326, 61680, 42330, 21820, 26262,
    0, 15530, 38604, 13158, 4080, 23130, 43580, 39318]

def hall16_V_masks : Array Nat :=
  #[0, 43690, 52428, 26214, 61680, 23130, 15420, 38550,
    39015, 31875, 5865, 61965, 44625, 19125, 8415, 50235]

def hall16_I   : IntMat 16 16 := matFromColMasks16 hall16_I_masks
def hall16_II  : IntMat 16 16 := matFromColMasks16 hall16_II_masks
def hall16_III : IntMat 16 16 := matFromColMasks16 hall16_III_masks
def hall16_IV  : IntMat 16 16 := matFromColMasks16 hall16_IV_masks
def hall16_V   : IntMat 16 16 := matFromColMasks16 hall16_V_masks

/-- Structural fold over `0, 1, ..., n - 1` (kernel-reducible for `decide`). -/
def foldRange {α : Type} : (n : Nat) → (Nat → α → α) → α → α
  | 0, _, acc => acc
  | k + 1, f, acc => foldRange k f (f k acc)

/-- Structural fold over `Fin n` (kernel-reducible for `decide`). -/
def foldFin {α : Type} : (n : Nat) → (Fin n → α → α) → α → α
  | 0, _, acc => acc
  | k + 1, f, acc => foldFin k (fun i a => f i.castSucc a) (f (Fin.last k) acc)

/-- Count of closed column quadruples (`0 ≤ c0 < c1 < c2 < c3 < 16` with `maxC4 H c0 c1 c2 c3 = 4`). -/
def countClosedQuads16 (H : IntMat 16 16) : Nat :=
  foldFin 16 (fun c0 acc0 =>
    foldFin 16 (fun c1 acc1 =>
      if c0.val < c1.val then
        foldFin 16 (fun c2 acc2 =>
          if c1.val < c2.val then
            foldFin 16 (fun c3 acc3 =>
              if c2.val < c3.val then
                acc3 + (if maxC4 H c0 c1 c2 c3 = 4 then 1 else 0)
              else acc3) acc2
          else acc2) acc1
      else acc1) acc0) 0

/-- 16-bit bitmask of columns where rows `r1` and `r2` agree (`H[r1, j] = H[r2, j]`). -/
def rowPairAgreeMask16 (H : IntMat 16 16) (r1 r2 : Fin 16) : Nat :=
  foldFin 16 (fun j acc =>
    if H r1 j = H r2 j then acc ||| (1 <<< j.val) else acc) 0

/-- Deduplicated list of all column-subset bitmasks arising as agreement or disagreement
    sets of distinct row pairs `(r1, r2)` (`0 ≤ r1 < r2 < 16`). -/
def rowPairMasks16 (H : IntMat 16 16) : List Nat :=
  foldFin 16 (fun r1 acc1 =>
    foldFin 16 (fun r2 acc2 =>
      if r1.val < r2.val then
        let m := rowPairAgreeMask16 H r1 r2
        let mc := 65535 ^^^ m
        let acc2' := if m ∈ acc2 then acc2 else m :: acc2
        if mc ∈ acc2' then acc2' else mc :: acc2'
      else acc2) acc1) []

/-- Exact count of 8-subsets of `Fin 16` admitting a double peak-8 collapse (`c_8 ≥ 2`). -/
def countDoublePeak8Subsets16 (H : IntMat 16 16) : Nat :=
  (rowPairMasks16 H).length

/-- Predicate that a 16-bit mask `m` corresponds to an 8-subset of `Fin 16` admitting a
    signed 8-sparse vector `x` with at least 2 entries of `|H x|` equal to 8. -/
def hasDoublePeak8Mask16 (H : IntMat 16 16) (m : Nat) : Prop :=
  m < 65536 ∧
  ∃ x : Fin 16 → Int,
    isSignedSparse 8 x ∧
    (∀ j : Fin 16, x j ≠ 0 ↔ ((m >>> j.val) &&& 1 = 1)) ∧
    2 ≤ countAbsEq (matVec H x) 8

/-! ### 4. Bent Diagonal Anti-Resonance on `𝔽_2^4` (`n = 16`) -/

/-- Explicit 4-variable Boolean bent function diagonal (`mask = 0x356`). -/
def bentDiag16 : Fin 16 → Int :=
  fun j => if (0x356 >>> j.val) &&& 1 = 1 then -1 else 1

/-- Right-multiplication of `H` by a `±1` diagonal matrix `D = diag(d)`. -/
def diagTwist {n : Nat} (H : IntMat n n) (d : Fin n → Int) : IntMat n n :=
  fun r c => H r c * d c

/-- All ordered affine 2-planes `(c0, c1, c2, c3)` in `𝔽_2^4` (`c0 < c1 < c2 < c3`, `c0 ⊕ c1 ⊕ c2 ⊕ c3 = 0`). -/
def affinePlanes16 : List (Fin 16 × Fin 16 × Fin 16 × Fin 16) :=
  foldFin 16 (fun c0 acc0 =>
    foldFin 16 (fun c1 acc1 =>
      if c0.val < c1.val then
        foldFin 16 (fun c2 acc2 =>
          if c1.val < c2.val then
            let c3 := c0.val ^^^ c1.val ^^^ c2.val
            if h3 : c2.val < c3 ∧ c3 < 16 then
              (c0, c1, c2, ⟨c3, h3.2⟩) :: acc2
            else acc2
          else acc2) acc1
      else acc1) acc0) []

/-- Number of affine 2-planes in `𝔽_2^4` flattened to exact PAPR = 1 (`|y_r| = 2` for all `r`)
    under the positive 4-sparse indicator vector on the plane. -/
def countFlatAffinePlanes16 (H : IntMat 16 16) : Nat :=
  (affinePlanes16.filter (fun p =>
    let (c0, c1, c2, c3) := p
    countAbsEq (matVec H (supportVec [c0.val, c1.val, c2.val, c3.val])) 2 == 16)).length

/-- Number of affine 2-planes in `𝔽_2^5` (`0 ≤ c0 < c1 < c2 < c3 < 32`, `c0 ⊕ c1 ⊕ c2 ⊕ c3 = 0`). -/
def countAffinePlanes32 : Nat :=
  foldRange 32 (fun c2 acc2 =>
    foldRange c2 (fun c1 acc1 =>
      foldRange c1 (fun c0 acc0 =>
        let c3 := c0 ^^^ c1 ^^^ c2
        if c2 < c3 ∧ c3 < 32 then acc0 + 1 else acc0) acc1) acc2) 0

/-! ### 5. OCP MXFP4 / MXFP6 Block Bit Budgets -/

/-- Total bits per block for Hybrid `k`-Split MXFP4 (FP16 outlier values + `b`-bit indices + E8M0 scale + 4-bit bulk). -/
def mxfp4HybridBits (B k b : Nat) : Nat :=
  4 * B + 8 + k * (16 + b)

/-- Total bits per block for OCP MXFP6 (6-bit elements + 8-bit E8M0 scale). -/
def mxfp6BlockBits (B : Nat) : Nat :=
  6 * B + 8

end Paley32Mxfp4
