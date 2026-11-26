/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for Pure-`Init` Block-Sparse Attention (`NSA` / `MoBA`) Bounds

Zero Mathlib, zero floating-point types. Every vector, block summary, radius,
AABB enclosure, 3-branch convex gate, and 2-bitplane POPCNT summary is defined
directly over `Nat`, `Int`, `Rat`, and `Bool`.
-/

namespace NsaBallBoundMoba

/-! ### Exact Integer Vector Operations -/

/-- Exact finite sum of `Int` values indexed by `Fin n`. -/
def intFinSumAux : (k : Nat) → (Fin k → Int) → Int
  | 0, _ => 0
  | k + 1, f => intFinSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
                f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum of `f : Fin n → Int`. -/
def intFinSum {n : Nat} (f : Fin n → Int) : Int :=
  intFinSumAux n f

/-- Exact integer inner product `u^T v` in `ℤ^d`. -/
def dotInt {d : Nat} (u v : Fin d → Int) : Int :=
  intFinSum (fun c => u c * v c)

/-- Exact squared Euclidean norm `‖v‖_2^2` in `ℤ^d`. -/
def normSqInt {d : Nat} (v : Fin d → Int) : Int :=
  dotInt v v

/-- Exact unnormalized block key sum `S_b = ∑_{j ∈ b} k_j` in `ℤ^d`. -/
def blockSum {d B : Nat} (ks : Fin B → Fin d → Int) : Fin d → Int :=
  fun c => intFinSum (fun j => ks j c)

/-- Exact non-negative finite maximum of `f : Fin n → Int` (with floor `0`). -/
def intFinMaxNonnegAux : (k : Nat) → (Fin k → Int) → Int
  | 0, _ => 0
  | k + 1, f => max (intFinMaxNonnegAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
                    (f ⟨k, Nat.lt_succ_self k⟩)

/-- Exact non-negative finite maximum of `f : Fin n → Int`. -/
def intFinMaxNonneg {n : Nat} (f : Fin n → Int) : Int :=
  intFinMaxNonnegAux n f

/-- Exact squared scaled block radius `R_b^2 = max_{j ∈ b} ‖B k_j - S_b‖_2^2`. -/
def blockSqRadius {d B : Nat} (ks : Fin B → Fin d → Int) : Int :=
  let S := blockSum ks
  intFinMaxNonneg (fun j => normSqInt (fun c => (B : Int) * ks j c - S c))

/-- Zero-sqrt exact integer Ball-Bound candidate predicate:
    `B * T ≤ q^T S_b ∨ (B * T - q^T S_b)^2 ≤ ‖q‖_2^2 * R_b^2`. -/
def ballBoundPass {d : Nat} (B : Nat) (q S : Fin d → Int) (R2 T : Int) : Prop :=
  (B : Int) * T ≤ dotInt q S ∨
  ((B : Int) * T - dotInt q S) * ((B : Int) * T - dotInt q S) ≤ normSqInt q * R2

/-! ### Adversarial Blindspot Blocks (`MoBA` / `NSA` Mean-Key) -/

/-- Antipodal-pair adversarial block of size `B` for query `q`:
    `k_0 = +2q`, `k_1 = -2q`, and `k_j = 0` for `j ≥ 2`. -/
def antipodalBlock {d : Nat} (B : Nat) (q : Fin d → Int) : Fin B → Fin d → Int :=
  fun j c =>
    if j.val = 0 then 2 * q c
    else if j.val = 1 then -(2 * q c)
    else 0

/-- Buried-needle adversarial block of size `B` for query `q`:
    `k_0 = +2q` and `k_j = -q` for all `j ≥ 1`. -/
def buriedNeedleBlock {d : Nat} (B : Nat) (q : Fin d → Int) : Fin B → Fin d → Int :=
  fun j c =>
    if j.val = 0 then 2 * q c
    else -(q c)

/-! ### Quest-AABB Upper Bound and All-`d` Rotated-Sphere Witness -/

/-- Exact Quest-AABB inner-product upper bound `∑_c max(q_c * kMin_c, q_c * kMax_c)`. -/
def aabbUpper {d : Nat} (q kMin kMax : Fin d → Int) : Int :=
  intFinSum (fun c => max (q c * kMin c) (q c * kMax c))

/-- All-ones diagonal query vector `(1, 1, ..., 1) ∈ ℤ^d`. -/
def allOnesVec (d : Nat) : Fin d → Int :=
  fun _ => 1

/-- Explicit all-`d` (`d = m^2`) integer sphere witness block of size `B = 2 m^2 + 2`:
    `k_0 = +1⃗`, `k_1 = -1⃗`, and `k_{2 + 2i} = +m e_i`, `k_{2 + 2i + 1} = -m e_i`.
    Every vector lies on the exact integer sphere `‖k_j‖_2^2 = m^2 = d`, with sum `0`,
    exact max inner product `d = m^2`, exact `0`-slack Ball-Bound `d`, and exact
    Quest-AABB over-estimate `m * d = m^3` (`√d ×` larger). -/
def sphereWitnessBlock (m : Nat) : Fin (2 * (m * m) + 2) → Fin (m * m) → Int :=
  fun j c =>
    if j.val = 0 then 1
    else if j.val = 1 then -1
    else
      let idx := (j.val - 2) / 2
      if c.val = idx then
        if (j.val - 2) % 2 = 0 then (m : Int) else -(m : Int)
      else 0

/-! ### Exact Rational Operations & NSA 3-Branch Convex Gate -/

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if 0 ≤ x then x else -x

/-- Exact finite sum of `Rat` values indexed by `Fin n`. -/
def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f => finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
                f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum of `f : Fin n → Rat`. -/
def finSum {n : Nat} (f : Fin n → Rat) : Rat :=
  finSumAux n f

/-- Exact rational inner product in `ℚ^d`. -/
def dotRat {d : Nat} (u v : Fin d → Rat) : Rat :=
  finSum (fun c => u c * v c)

/-- Exact squared Euclidean norm in `ℚ^d`. -/
def normSqRat {d : Nat} (v : Fin d → Rat) : Rat :=
  dotRat v v

/-- Pointwise vector subtraction in `ℚ^d`. -/
def vecSubRat {d : Nat} (u v : Fin d → Rat) : Fin d → Rat :=
  fun c => u c - v c

/-- NSA 3-branch convex gate `O_NSA = g_1 O_cmp + g_2 O_slc + g_3 O_win`. -/
def nsaGate {d : Nat} (g1 g2 g3 : Rat) (oCmp oSlc oWin : Fin d → Rat) : Fin d → Rat :=
  fun c => g1 * oCmp c + g2 * oSlc c + g3 * oWin c

/-- Standard 2-simplex membership `g ∈ Δ_2`: `g_1, g_2, g_3 ≥ 0` and `g_1 + g_2 + g_3 = 1`. -/
def isSimplex3 (g1 g2 g3 : Rat) : Prop :=
  (0 : Rat) ≤ g1 ∧ (0 : Rat) ≤ g2 ∧ (0 : Rat) ≤ g3 ∧ g1 + g2 + g3 = 1

/-! ### 2-Bitplane POPCNT Summary Encoding -/

/-- Symmetric 2-bitplane decoder mapping `(sign, mag) ∈ Bool × Bool` onto `{-3, -1, +1, +3}`:
    `sign = true` is `+`, `false` is `-`; `mag = true` is `3`, `false` is `1`. -/
def decodeTwoPlane (s m : Bool) : Int :=
  (if s then 1 else -1) * (if m then 3 else 1)

/-- Exact bitplane population count `popcnt(p)` over `Fin d`. -/
def boolCount {d : Nat} (p : Fin d → Bool) : Int :=
  intFinSum (fun i => if p i then 1 else 0)

/-- Exact zero-multiplier 2-bitplane POPCNT dot product (matching `k_bench_2bit_popcnt` in
    `nsa_block_sparse.hip`): partitions coordinates into high-high (`9`), high-low (`3`),
    and low-low (`1`) magnitude buckets and combines their same-sign popcounts. -/
def twoPlaneDotPopcnt {d : Nat} (sq mq sk mk : Fin d → Bool) : Int :=
  let eq := fun i => sq i == sk i
  let hh := fun i => mq i && mk i
  let hl := fun i => xor (mq i) (mk i)
  let ll := fun i => !(mq i || mk i)
  9 * (2 * boolCount (fun i => hh i && eq i) - boolCount hh) +
  3 * (2 * boolCount (fun i => hl i && eq i) - boolCount hl) +
  1 * (2 * boolCount (fun i => ll i && eq i) - boolCount ll)

/-- Exact bit count per block summary vector of dimension `d`: `2d` bits for 2-bitplane. -/
def twoPlaneBits (d : Nat) : Nat := 2 * d

/-- Exact bit count per block summary vector of dimension `d`: `8d` bits for `INT8`. -/
def int8Bits (d : Nat) : Nat := 8 * d

/-- Exact bit count per block summary vector of dimension `d`: `16d` bits for `FP16`. -/
def fp16Bits (d : Nat) : Nat := 16 * d

end NsaBallBoundMoba
