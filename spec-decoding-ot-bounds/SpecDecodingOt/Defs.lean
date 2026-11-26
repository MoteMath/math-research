/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Shared Definitions for `spec-decoding-ot-bounds`

Pure-`Init` (zero Mathlib) definitions for:
- Finite rational sums `sumRat`, rational powers `ratPow`, and probability distributions `isProbDist`
- Single-draft `alpha1`, correlated multi-draft `alphaCorr`, i.i.d. Strassen objective `strassenObj`,
  and exact exhaustive i.i.d. optimal transport acceptance `alphaIID`
- Exact 1-PRNG Cyclic Madow (`K = 2`) hit probability `madowHit2` and acceptance `alphaMadow2`
- Rational Softmax `softmaxRat` for quantized-draft acceptance loss bounds
- Arbitrary-depth modular `BitVec b` reversible Feistel coupling `fwdPass` / `revPass`
- Exact `2 × 2` symplectic floating-point reversible transfer matrix `symplecticM` and its powers
-/

namespace SpecDecodingOt

/-- Sum of a `Rat`-valued function over `Fin n`. -/
def sumRat : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | _ + 1, f => sumRat (fun i => f i.castSucc) + f (Fin.last _)

/-- Exact natural-number power of a rational number. -/
def ratPow (x : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => ratPow x n * x

/-- Discrete probability distribution on `Fin V` over `Rat`. -/
def isProbDist {V : Nat} (p : Fin V → Rat) : Prop :=
  (∀ i, 0 ≤ p i) ∧ sumRat p = 1

/-- Exact single-draft speculative decoding acceptance probability `∑ min(p_i, q_i)`. -/
def alpha1 {V : Nat} (p q : Fin V → Rat) : Rat :=
  sumRat (fun i => min (p i) (q i))

/-- Exact global correlated `K`-draft optimal transport ceiling `∑ min(p_i, K * q_i)`. -/
def alphaCorr (K : Nat) {V : Nat} (p q : Fin V → Rat) : Rat :=
  sumRat (fun i => min (p i) ((K : Rat) * q i))

/-- Exact i.i.d. `K`-draft Strassen/Hall upper functional for subset `S : Fin V → Bool`:
    `p(S^c) + 1 - (1 - q(S))^K`. -/
def strassenObj (K : Nat) {V : Nat} (p q : Fin V → Rat) (S : Fin V → Bool) : Rat :=
  sumRat (fun i => if S i then 0 else p i) +
    (1 - ratPow (1 - sumRat (fun i => if S i then q i else 0)) K)

/-- Decode a bitmask `mask : Nat` into a subset predicate `Fin V → Bool`. -/
def maskToSet {V : Nat} (mask : Nat) : Fin V → Bool :=
  fun i => ((mask >>> i.val) &&& 1) == 1

/-- Minimum of a `Rat`-valued function over masks `0, 1, ..., m - 1` (initialized at `1`). -/
def minOverMasksAux {V : Nat} (f : (Fin V → Bool) → Rat) : Nat → Rat
  | 0 => 1
  | m + 1 => min (minOverMasksAux f m) (f (maskToSet m))

/-- Minimum of a `Rat`-valued function over all `2^V` subsets of `Fin V`. -/
def minOverMasks {V : Nat} (f : (Fin V → Bool) → Rat) : Rat :=
  minOverMasksAux f (2 ^ V)

/-- Exact i.i.d. `K`-draft optimal transport acceptance `min_{S ⊆ [V]} strassenObj K p q S`. -/
def alphaIID (K : Nat) {V : Nat} (p q : Fin V → Rat) : Rat :=
  minOverMasks (strassenObj K p q)

/-- Exact rational CDF `F_i = ∑_{j < i} q_j`. -/
def cdfRat {V : Nat} (q : Fin V → Rat) (i : Fin V) : Rat :=
  sumRat (fun j : Fin V => if j.val < i.val then q j else 0)

/-- Fractional part on `[0, 2)`: maps `x` to `x - 1` if `1 ≤ x` else `x`. -/
def fracPart2 (x : Rat) : Rat :=
  if 1 ≤ x then x - 1 else x

/-- Insert an interval `(lo, hi)` into a list sorted by `lo`. -/
def insertInterval (iv : Rat × Rat) : List (Rat × Rat) → List (Rat × Rat)
  | [] => [iv]
  | hd :: tl => if iv.1 ≤ hd.1 then iv :: hd :: tl else hd :: insertInterval iv tl

/-- Insertion sort for a list of intervals by left endpoint. -/
def sortIntervals : List (Rat × Rat) → List (Rat × Rat)
  | [] => []
  | hd :: tl => insertInterval hd (sortIntervals tl)

/-- Total Lebesgue measure of a sorted list of intervals, tracking the current merged span. -/
def measureSortedIntervals (curLo curHi : Rat) : List (Rat × Rat) → Rat
  | [] => curHi - curLo
  | (lo, hi) :: tl =>
    if lo ≤ curHi then
      measureSortedIntervals curLo (max curHi hi) tl
    else
      (curHi - curLo) + measureSortedIntervals lo hi tl

/-- Total Lebesgue measure of an arbitrary list of intervals in `[0, 1]`. -/
def unionMeasure (ivs : List (Rat × Rat)) : Rat :=
  match sortIntervals ivs with
  | [] => 0
  | (lo, hi) :: tl => min 1 (measureSortedIntervals lo hi tl)

/-- Collect the folded modulo-`1/2` intervals (rescaled by `2` to `[0, 1]`) for subset `S`. -/
def madowIntervals2Aux {V : Nat} (q : Fin V → Rat) (S : Fin V → Bool) :
    (k : Nat) → k ≤ V → List (Rat × Rat)
  | 0, _ => []
  | k + 1, hk =>
    let rest := madowIntervals2Aux q S k (Nat.le_of_succ_le hk)
    let i : Fin V := ⟨k, hk⟩
    if S i then
      let len := 2 * q i
      if len ≤ 0 then rest
      else if 1 ≤ len then (0, 1) :: rest
      else
        let s := fracPart2 (2 * cdfRat q i)
        let e := s + len
        if e ≤ 1 then (s, e) :: rest
        else (s, 1) :: (0, e - 1) :: rest
    else rest

/-- Exact `K = 2` Cyclic Madow hit probability `2 * Leb(π_2(⋃_{i ∈ S} I_i))`. -/
def madowHit2 {V : Nat} (q : Fin V → Rat) (S : Fin V → Bool) : Rat :=
  unionMeasure (madowIntervals2Aux q S V (Nat.le_refl V))

/-- Exact `K = 2` Cyclic Madow Strassen objective for subset `S`. -/
def madowObj2 {V : Nat} (p q : Fin V → Rat) (S : Fin V → Bool) : Rat :=
  sumRat (fun i => if S i then 0 else p i) + madowHit2 q S

/-- Exact `K = 2` fixed-order Cyclic Madow acceptance probability. -/
def alphaMadow2 {V : Nat} (p q : Fin V → Rat) : Rat :=
  minOverMasks (madowObj2 p q)

/-- Exact rational Softmax of positive weight vector `w : Fin V → Rat`. -/
def softmaxRat {V : Nat} (w : Fin V → Rat) : Fin V → Rat :=
  fun i => w i / sumRat w

/-- Single-layer modular `BitVec b` reversible Feistel coupling forward map. -/
def revLayerFwd {b : Nat} (f g : BitVec b → BitVec b) (s : BitVec b × BitVec b) :
    BitVec b × BitVec b :=
  let x' := s.1 + f s.2
  (x', s.2 + g x')

/-- Single-layer modular `BitVec b` reversible Feistel coupling inverse map. -/
def revLayerInv {b : Nat} (f g : BitVec b → BitVec b) (s : BitVec b × BitVec b) :
    BitVec b × BitVec b :=
  let y := s.2 - g s.1
  (s.1 - f y, y)

/-- `L`-layer modular `BitVec b` reversible Transformer forward pass. -/
def fwdPass {b : Nat} :
    (L : Nat) → (Fin L → BitVec b → BitVec b) → (Fin L → BitVec b → BitVec b) →
    BitVec b × BitVec b → BitVec b × BitVec b
  | 0, _, _, s => s
  | L + 1, F, G, s =>
    revLayerFwd (F (Fin.last L)) (G (Fin.last L))
      (fwdPass L (fun i => F i.castSucc) (fun i => G i.castSucc) s)

/-- `L`-layer modular `BitVec b` reversible Transformer reverse pass. -/
def revPass {b : Nat} :
    (L : Nat) → (Fin L → BitVec b → BitVec b) → (Fin L → BitVec b → BitVec b) →
    BitVec b × BitVec b → BitVec b × BitVec b
  | 0, _, _, s => s
  | L + 1, F, G, s =>
    revPass L (fun i => F i.castSucc) (fun i => G i.castSucc)
      (revLayerInv (F (Fin.last L)) (G (Fin.last L)) s)

/-- Exact `2 × 2` matrix over `Rat`. -/
structure Mat2 where
  a00 : Rat
  a01 : Rat
  a10 : Rat
  a11 : Rat
  deriving DecidableEq

/-- `2 × 2` identity matrix over `Rat`. -/
def mat2Id : Mat2 := ⟨1, 0, 0, 1⟩

/-- `2 × 2` matrix multiplication over `Rat`. -/
def mat2Mul (A B : Mat2) : Mat2 :=
  ⟨A.a00 * B.a00 + A.a01 * B.a10,
   A.a00 * B.a01 + A.a01 * B.a11,
   A.a10 * B.a00 + A.a11 * B.a10,
   A.a10 * B.a01 + A.a11 * B.a11⟩

/-- Natural-number power of a `2 × 2` rational matrix. -/
def mat2Pow (A : Mat2) : Nat → Mat2
  | 0 => mat2Id
  | n + 1 => mat2Mul (mat2Pow A n) A

/-- Determinant of a `2 × 2` rational matrix. -/
def mat2Det (A : Mat2) : Rat :=
  A.a00 * A.a11 - A.a01 * A.a10

/-- Trace of a `2 × 2` rational matrix. -/
def mat2Trace (A : Mat2) : Rat :=
  A.a00 + A.a11

/-- Symplectic floating-point reversible coupling Jacobian `M(γ) = [[1 + γ², γ], [γ, 1]]`. -/
def symplecticM (γ : Rat) : Mat2 :=
  ⟨1 + γ * γ, γ, γ, 1⟩

/-- Counterexample 1 (default order, `K = 2, V = 4`): `p = (1/2, 0, 1/2, 0)`. -/
def madowCE1P : Fin 4 → Rat
  | ⟨0, _⟩ => (1 : Rat) / 2
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => (1 : Rat) / 2
  | ⟨3, _⟩ => 0

/-- Counterexample 1 (default order, `K = 2, V = 4`): `q = (1/4, 1/4, 1/4, 1/4)`. -/
def madowCE1Q : Fin 4 → Rat := fun _ => (1 : Rat) / 4

/-- Counterexample 2 (oracle descending-`p/q`-sorted, `K = 2, V = 4`):
    `p = (3/10, 9/20, 1/4, 0)`. -/
def madowCE2P : Fin 4 → Rat
  | ⟨0, _⟩ => (3 : Rat) / 10
  | ⟨1, _⟩ => (9 : Rat) / 20
  | ⟨2, _⟩ => (1 : Rat) / 4
  | ⟨3, _⟩ => 0

/-- Counterexample 2 (oracle descending-`p/q`-sorted, `K = 2, V = 4`):
    `q = (1/5, 3/10, 1/5, 3/10)`, giving ratios `p_i / q_i = (3/2, 3/2, 5/4, 0)`. -/
def madowCE2Q : Fin 4 → Rat
  | ⟨0, _⟩ => (1 : Rat) / 5
  | ⟨1, _⟩ => (3 : Rat) / 10
  | ⟨2, _⟩ => (1 : Rat) / 5
  | ⟨3, _⟩ => (3 : Rat) / 10

end SpecDecodingOt
