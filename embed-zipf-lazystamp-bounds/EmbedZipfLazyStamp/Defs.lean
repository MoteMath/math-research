/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Pure-`Init` Definitions (`embed-zipf-lazystamp-bounds`)

Zero Mathlib, zero `native_decide`, zero floating-point approximations.
All objects are exact over `Nat`, `Int`, and `Rat`.
-/

namespace EmbedZipfLazyStamp

/-! ### Rational Arithmetic, Sums, Products, and Exact Powers -/

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if 0 ≤ x then x else -x

/-- Recursive prefix sum over `Fin k → Rat`. -/
def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f => finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
      f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum `∑_{j : Fin n} f j` over `Rat`. -/
def finSum {n : Nat} (f : Fin n → Rat) : Rat :=
  finSumAux n f

/-- Recursive prefix sum over `Fin k → Int`. -/
def finSumIntAux : (k : Nat) → (Fin k → Int) → Int
  | 0, _ => 0
  | k + 1, f => finSumIntAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
      f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite sum `∑_{j : Fin n} f j` over `Int`. -/
def finSumInt {n : Nat} (f : Fin n → Int) : Int :=
  finSumIntAux n f

/-- Recursive prefix product over `Fin k → Rat`. -/
def finProdAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 1
  | k + 1, f => finProdAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) *
      f ⟨k, Nat.lt_succ_self k⟩

/-- Exact finite product `∏_{j : Fin n} f j` over `Rat`. -/
def finProd {n : Nat} (f : Fin n → Rat) : Rat :=
  finProdAux n f

/-- Exact natural-exponent power `x ^ n` over `Rat`. -/
def ratPow (x : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => x * ratPow x n

/-- Exact `O(log n)` binary-exponentiation power over `Rat`. -/
def ratPowFast (x : Rat) (n : Nat) : Rat :=
  if n = 0 then 1
  else
    let half := ratPowFast x (n / 2)
    if n % 2 = 0 then half * half else x * half * half
termination_by n

/-- Exact integer power of `2` as a rational number: `2^e` for `e : Int`. -/
def pow2Int (e : Int) : Rat :=
  if 0 ≤ e then ((2 ^ e.toNat : Nat) : Rat)
  else (1 : Rat) / ((2 ^ (-e).toNat : Nat) : Rat)

/-- Exact integer power of `4` as a rational number: `4^e = 2^(2*e)` for `e : Int`. -/
def pow4Int (e : Int) : Rat :=
  pow2Int (2 * e)

/-! ### Pillar 1: Tied Embedding / Unembedding Gradients (`W_emb = W_lm^T`) -/

/-- Sparse input-embedding gradient: nonzero only on the active input token `x`. -/
def gInSparse {V d : Nat} (x : Fin V) (g_x : Fin d → Rat) (v : Fin V) (j : Fin d) : Rat :=
  if v = x then g_x j else 0

/-- Dense unembedding (LM-head) cross-entropy gradient `(p_v - 1_{v=y}) h_j`. -/
def gOutDense {V d : Nat} (p : Fin V → Rat) (y : Fin V) (h : Fin d → Rat)
    (v : Fin V) (j : Fin d) : Rat :=
  (p v - if v = y then 1 else 0) * h j

/-- Batch-averaged dense unembedding gradient across `B` token positions. -/
def gOutBatch {B V d : Nat} (pB : Fin B → Fin V → Rat) (yB : Fin B → Fin V)
    (hB : Fin B → Fin d → Rat) (v : Fin V) (j : Fin d) : Rat :=
  ((1 : Rat) / (B : Rat)) * finSum (fun b => gOutDense (pB b) (yB b) (hB b) v j)

/-! ### Pillar 1 & 2: IEEE-754 / OCP Round-to-Nearest-Even (RNE) Arithmetic -/

/-- Exact IEEE-754 Round-to-Nearest-Even (ties to even) from `Rat` to `Int`. -/
def rneInt (r : Rat) : Int :=
  let d : Int := (r.den : Int)
  let q : Int := r.num / d
  let rem : Int := r.num % d
  if 2 * rem < d then q
  else if 2 * rem > d then q + 1
  else if q % 2 == 0 then q else q + 1

/-- Exact RNE rounding of `x : Rat` onto the uniform grid `u * Z` (`u > 0`). -/
def rneGrid (u x : Rat) : Rat :=
  (rneInt (x / u) : Rat) * u

/-- Binade ULP `ulp_F(w) = 2^(e_w - M)` for mantissa width `M` and exponent `e_w`. -/
def ulpBinade (e_w : Int) (M : Nat) : Rat :=
  pow2Int (e_w - (M : Int))

/-- Half-ULP flush threshold `2^(e_w - M - 1)`. -/
def halfUlpBinade (e_w : Int) (M : Nat) : Rat :=
  pow2Int (e_w - (M : Int) - 1)

/-- Minimum positive subnormal of `FP8-E4M3FN` (`2^-9 = 1/512`). -/
def fp8E4M3MinSubnormal : Rat := pow2Int (-9)

/-- Half minimum subnormal of `FP8-E4M3FN` (`2^-10 = 1/1024`). -/
def fp8E4M3HalfSubnormal : Rat := pow2Int (-10)

/-- Minimum positive subnormal of `FP8-E5M2` (`2^-16 = 1/65536`). -/
def fp8E5M2MinSubnormal : Rat := pow2Int (-16)

/-- Half minimum subnormal of `FP8-E5M2` (`2^-17 = 1/131072`). -/
def fp8E5M2HalfSubnormal : Rat := pow2Int (-17)

/-- Exact positive normal floating-point value `(2^p + m) * 2^(e - p)` for `m < 2^p`. -/
def normalFloat (p : Nat) (e : Int) (m : Nat) : Rat :=
  ((2 ^ p + m : Nat) : Rat) * pow2Int (e - (p : Int))

/-- Exact RNE rounding of a value `x ≤ normalFloat p e m` in a `p`-mantissa-bit float format.
    When `m = 0` (`v = 2^e`), values strictly below `2^e` lie in binade `e - 1` with ULP `2^(e - 1 - p)`;
    when `m > 0`, values just below `v` lie in binade `e` with ULP `2^(e - p)`. -/
def rneFloatBelow (p : Nat) (e : Int) (m : Nat) (x : Rat) : Rat :=
  if m = 0 then rneGrid (pow2Int (e - 1 - (p : Int))) x
  else rneGrid (pow2Int (e - (p : Int))) x

/-- `K`-step iterated `BF16`/float absent-row second-moment EMA `v_{t+1} = fl(β_2 * v_t)`. -/
def iterFloatDecay (p : Nat) (e : Int) (m : Nat) (β : Rat) : Nat → Rat → Rat
  | 0, v => v
  | k + 1, v => iterFloatDecay p e m β k (rneFloatBelow p e m (β * v))

/-! ### Pillar 2: Exact Rational Dense vs Lazy-Stamp AdamW -/

/-- Exact rational per-coordinate AdamW optimizer state `(w, m, v)`. -/
structure AdamWState where
  w : Rat
  m : Rat
  v : Rat
  deriving DecidableEq, Repr

/-- Single absent-token (`g = 0`) dense decoupled AdamW update. -/
def denseAbsentStep (β1 β2 η lam : Rat) (s : AdamWState) : AdamWState :=
  { w := (1 - η * lam) * s.w
    m := β1 * s.m
    v := β2 * s.v }

/-- `Δ` consecutive absent-token dense decoupled AdamW updates. -/
def denseAbsentSteps (β1 β2 η lam : Rat) : Nat → AdamWState → AdamWState
  | 0, s => s
  | k + 1, s => denseAbsentSteps β1 β2 η lam k (denseAbsentStep β1 β2 η lam s)

/-- Single `O(1)` / `O(log Δ)` Lazy-Stamp AdamW jump across an absent gap of `Δ` steps. -/
def lazyStampJump (β1 β2 η lam : Rat) (Δ : Nat) (s : AdamWState) : AdamWState :=
  { w := ratPow (1 - η * lam) Δ * s.w
    m := ratPow β1 Δ * s.m
    v := ratPow β2 Δ * s.v }

/-- Binary-exponentiation `O(log Δ)` Lazy-Stamp AdamW jump. -/
def lazyStampJumpFast (β1 β2 η lam : Rat) (Δ : Nat) (s : AdamWState) : AdamWState :=
  { w := ratPowFast (1 - η * lam) Δ * s.w
    m := ratPowFast β1 Δ * s.m
    v := ratPowFast β2 Δ * s.v }

/-! ### Pillar 2: Memory-Traffic & FLOP Work Complexity -/

/-- Dense AdamW bytes touched per step across all `V` rows of width `d`. -/
def denseBytes (V d bRow : Nat) : Nat := V * d * bRow

/-- Lazy-Stamp AdamW bytes touched per step across `U` unique active rows of width `d`. -/
def lazyBytes (U d bRow : Nat) : Nat := U * d * bRow

/-- Dense AdamW FLOPs per step across all `V` rows of width `d`. -/
def denseFlops (V d fRow : Nat) : Nat := V * d * fRow

/-- Lazy-Stamp AdamW FLOPs per step across `U` unique active rows of width `d`. -/
def lazyFlops (U d fRow : Nat) : Nat := U * d * fRow

/-! ### Pillar 3: Zipf Mixed-Precision Embedding Allocation -/

/-- Frequency-weighted quantization MSE `∑_r p_r * c * 4^(-b_r)`. -/
def weightedQuantMse {V : Nat} (p : Fin V → Rat) (c : Rat) (b : Fin V → Int) : Rat :=
  finSum (fun r => p r * c * pow4Int (-b r))

/-- Three-tier average bits per parameter for `(V1, V2, V3)` with widths `(b1, b2, b3)`. -/
def tieredAvgBits (V1 V2 V3 : Nat) (b1 b2 b3 : Rat) : Rat :=
  ((V1 : Rat) * b1 + (V2 : Rat) * b2 + (V3 : Rat) * b3) / ((V1 + V2 + V3 : Nat) : Rat)

/-- Three-tier frequency-weighted logit MSE `P1 * e1 + P2 * e2 + P3 * e3`. -/
def tieredWeightedMse (P1 P2 P3 e1 e2 e3 : Rat) : Rat :=
  P1 * e1 + P2 * e2 + P3 * e3

end EmbedZipfLazyStamp
