/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Public Definitions (`loftq-cycles-rank1-ef21`)

Pure Lean 4 `Init` (zero Mathlib) definitions for:
1. Matrix Frobenius norms, rank-1 1-bit sign and ternary vectors over `Rat` and `Int`.
2. Exact quadratic field `QSqrt2 = ℚ(√2)` with decidable total order and exact constants
   `(2 + √2)/8`, `(9 + 4√2)/49`, `(2 + √2)/16`, and the exact `2 × 2` rotation `R(π/8)` witness.
3. GPU-discovered coupled integer/orthogonal matrices `W_3x3_coupled` and `W_4x4_coupled`
   beating uncoupled block-diagonal `I_k ⊗ R(π/8)`.
4. LoftQ alternating projection (Euclidean best-approximation, spiked diagonal separation,
   and `4M^2` saturation law).
5. Exact `Q16.16` 3×3 symmetric LoftQ operator (`loftqStepQ16`, `loftqIterQ16`) and the
   GPU-discovered permanent 2-cycle (`W_cyc2`) and 3-cycle (`W_cyc3`) witnesses.
-/

namespace LoftqCyclesRank1

/-! ### 1. Basic `Rat` and `Int` Matrix Helpers -/

def absRat (x : Rat) : Rat :=
  if x < 0 then -x else x

def sumFinRat : (n : Nat) → (Fin n → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => sumFinRat n (fun i => f i.castSucc) + f (Fin.last n)

def sumFinInt : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFinInt n (fun i => f i.castSucc) + f (Fin.last n)

abbrev RatMat (m n : Nat) := Fin m → Fin n → Rat
abbrev IntMat (m n : Nat) := Fin m → Fin n → Int

def matAdd {m n : Nat} (A B : RatMat m n) : RatMat m n :=
  fun i j => A i j + B i j

def matSub {m n : Nat} (A B : RatMat m n) : RatMat m n :=
  fun i j => A i j - B i j

def frobSq {m n : Nat} (W : RatMat m n) : Rat :=
  sumFinRat m (fun i => sumFinRat n (fun j => W i j * W i j))

def frobSqErr {m n : Nat} (W A : RatMat m n) : Rat :=
  frobSq (matSub W A)

def frobSqInt {m n : Nat} (W : IntMat m n) : Int :=
  sumFinInt m (fun i => sumFinInt n (fun j => W i j * W i j))

def rank1Mat {m n : Nat} (γ : Rat) (u : Fin m → Int) (v : Fin n → Int) : RatMat m n :=
  fun i j => γ * (u i : Rat) * (v j : Rat)

def quadFormRat {m n : Nat} (W : RatMat m n) (u : Fin m → Int) (v : Fin n → Int) : Rat :=
  sumFinRat m (fun i => (u i : Rat) * sumFinRat n (fun j => W i j * (v j : Rat)))

def quadFormInt {m n : Nat} (W : IntMat m n) (u : Fin m → Int) (v : Fin n → Int) : Int :=
  sumFinInt m (fun i => u i * sumFinInt n (fun j => W i j * v j))

def vecSqNormInt {n : Nat} (u : Fin n → Int) : Int :=
  sumFinInt n (fun i => u i * u i)

def isSignVec {n : Nat} (u : Fin n → Int) : Prop :=
  ∀ i : Fin n, u i = 1 ∨ u i = -1

def isTernVec {n : Nat} (u : Fin n → Int) : Prop :=
  (∀ i : Fin n, u i = -1 ∨ u i = 0 ∨ u i = 1) ∧ ∃ i : Fin n, u i ≠ 0

def isOrthogonalInt {n : Nat} (W : IntMat n n) (c : Int) : Prop :=
  ∀ i j : Fin n,
    sumFinInt n (fun k => W k i * W k j) = if i = j then c else 0

/-! ### 2. Exact Quadratic Field `QSqrt2 = ℚ(√2)` -/

/-- Exact element `a + b * √2` of `ℚ(√2)`. -/
structure QSqrt2 where
  a : Rat
  b : Rat
  deriving DecidableEq, Repr

namespace QSqrt2

def ofRat (r : Rat) : QSqrt2 := ⟨r, 0⟩
def ofInt (z : Int) : QSqrt2 := ⟨(z : Rat), 0⟩
def zero : QSqrt2 := ⟨0, 0⟩
def one : QSqrt2 := ⟨1, 0⟩
def sqrt2 : QSqrt2 := ⟨0, 1⟩

def add (x y : QSqrt2) : QSqrt2 := ⟨x.a + y.a, x.b + y.b⟩
def neg (x : QSqrt2) : QSqrt2 := ⟨-x.a, -x.b⟩
def sub (x y : QSqrt2) : QSqrt2 := ⟨x.a - y.a, x.b - y.b⟩
def mul (x y : QSqrt2) : QSqrt2 := ⟨x.a * y.a + 2 * x.b * y.b, x.a * y.b + x.b * y.a⟩

instance : Zero QSqrt2 := ⟨zero⟩
instance : One QSqrt2 := ⟨one⟩
instance : Add QSqrt2 := ⟨add⟩
instance : Neg QSqrt2 := ⟨neg⟩
instance : Sub QSqrt2 := ⟨sub⟩
instance : Mul QSqrt2 := ⟨mul⟩

/-- Exact nonnegativity predicate `a + b√2 ≥ 0`. -/
def nonneg (x : QSqrt2) : Prop :=
  (0 ≤ x.a ∧ 0 ≤ x.b) ∨
  (0 ≤ x.a ∧ x.b < 0 ∧ 2 * x.b * x.b ≤ x.a * x.a) ∨
  (x.a < 0 ∧ 0 ≤ x.b ∧ x.a * x.a ≤ 2 * x.b * x.b)

instance (x : QSqrt2) : Decidable (nonneg x) := by
  unfold nonneg
  infer_instance

def le (x y : QSqrt2) : Prop := nonneg (y - x)
def lt (x y : QSqrt2) : Prop := nonneg (y - x) ∧ x ≠ y

instance : LE QSqrt2 := ⟨le⟩
instance : LT QSqrt2 := ⟨lt⟩

instance (x y : QSqrt2) : Decidable (x ≤ y) := by
  show Decidable (nonneg (y - x))
  infer_instance

instance (x y : QSqrt2) : Decidable (x < y) := by
  show Decidable (nonneg (y - x) ∧ x ≠ y)
  infer_instance

/-- Exact `(2 + √2) / 8`, the `(2, 2)` rank-1 ternary EF21 contraction constant. -/
def alpha2x2 : QSqrt2 := ⟨1 / 4, 1 / 8⟩

/-- Exact `(2 + √2) / (10 + √2) = (9 + 4√2) / 49`, the `3 × 3` block-diagonal `R(π/8)` upper bound. -/
def blockUB3 : QSqrt2 := ⟨9 / 49, 4 / 49⟩

/-- Exact `(2 + √2) / 16`, the `4 × 4` block-diagonal `I_2 ⊗ R(π/8)` upper bound. -/
def blockUB4 : QSqrt2 := ⟨1 / 8, 1 / 16⟩

end QSqrt2

def sumFinQ2 : (n : Nat) → (Fin n → QSqrt2) → QSqrt2
  | 0, _ => QSqrt2.zero
  | n + 1, f => sumFinQ2 n (fun i => f i.castSucc) + f (Fin.last n)

abbrev Q2Mat (m n : Nat) := Fin m → Fin n → QSqrt2

def frobSqQ2 {m n : Nat} (W : Q2Mat m n) : QSqrt2 :=
  sumFinQ2 m (fun i => sumFinQ2 n (fun j => W i j * W i j))

def quadFormQ2 {m n : Nat} (W : Q2Mat m n) (u : Fin m → Int) (v : Fin n → Int) : QSqrt2 :=
  sumFinQ2 m (fun i => QSqrt2.ofInt (u i) * sumFinQ2 n (fun j => W i j * QSqrt2.ofInt (v j)))

/-- Exact `2 × 2` rotation `R(π/8)` up to positive scalar `1 / cos(π/8)`:
    `[[1, √2 - 1], [-(√2 - 1), 1]]`. -/
def W_rot2x2 : Q2Mat 2 2 := fun i j =>
  match i.val, j.val with
  | 0, 0 => ⟨1, 0⟩
  | 0, 1 => ⟨-1, 1⟩
  | 1, 0 => ⟨1, -1⟩
  | _, _ => ⟨1, 0⟩

/-! ### 3. GPU-Discovered Coupled Matrices Beating `I_k ⊗ R(π/8)` -/

/-- Exact `3 × 3` coupled integer witness achieving `2162403 / 7239976 < (9 + 4√2) / 49`. -/
def W_3x3_coupled : IntMat 3 3 := fun i j =>
  match i.val, j.val with
  | 0, 0 => -3602 | 0, 1 =>   127 | 0, 2 => -1492
  | 1, 0 =>  1492 | 1, 1 =>  -127 | 1, 2 => -3602
  | 2, 0 =>  -127 | 2, 1 => -3602 | _, _ =>   127

/-- Exact `4 × 4` coupled orthogonal integer witness (`W^T W = 16680999 · I_4`)
    achieving `28440889 / 133447992 < (2 + √2) / 16`. -/
def W_4x4_coupled : IntMat 4 4 := fun i j =>
  match i.val, j.val with
  | 0, 0 => -1562 | 0, 1 =>  3771 | 0, 2 =>    55 | 0, 3 =>   133
  | 1, 0 =>   -55 | 1, 1 =>   133 | 1, 2 => -1562 | 1, 3 => -3771
  | 2, 0 =>  3771 | 2, 1 =>  1562 | 2, 2 =>   133 | 2, 3 =>   -55
  | 3, 0 =>   133 | 3, 1 =>    55 | 3, 2 => -3771 | _, _ =>  1562

/-! ### 4. LoftQ Alternating Projection, Spiked Separation & `4M^2` Saturation -/

/-- Best Frobenius approximation predicate `P ∈ argmin_{Y ∈ S} ‖X - Y‖_F^2`. -/
def isBestApprox {m n : Nat} (S : RatMat m n → Prop) (X P : RatMat m n) : Prop :=
  S P ∧ ∀ Y : RatMat m n, S Y → frobSqErr X P ≤ frobSqErr X Y

/-- Diagonal `d × d` matrix from a vector. -/
def diagMat {d : Nat} (v : Fin d → Rat) : RatMat d d :=
  fun i j => if i = j then v i else 0

/-- Spiked diagonal matrix `W = diag(2*M*k, k-1, ..., k-1)`. -/
def spikedDiag (d M k : Nat) : RatMat d d :=
  diagMat (fun i => if i.val = 0 then (2 * M * k : Rat) else ((k - 1 : Nat) : Rat))

/-- Exact nearest-integer rounding (ties away from zero) for `x ∈ [0, 1/2)` and integers. -/
def roundHalfUp (x : Rat) : Int :=
  if 0 ≤ x then
    ((2 * x.num + (x.den : Int)) / (2 * (x.den : Int)))
  else
    -(((2 * (-x.num) + (x.den : Int)) / (2 * (x.den : Int))))

/-- Symmetric `M`-level absmax-RTN quantization at explicit scale `s > 0` (clamped to `[-M, M]`). -/
def absmaxQuantAtScale (M : Nat) (s : Rat) (x : Rat) : Rat :=
  if s ≤ 0 then 0
  else
    let q := roundHalfUp (x / s)
    let c := max (-(M : Int)) (min (M : Int) q)
    (c : Rat) * s

/-- Continuous uniform bulk `[-1, 1]` variance ratio `(1/3) / (1/(12 M^2)) = 4 M^2`. -/
def uniformBulkVarianceRatio (M : Nat) : Rat :=
  ((1 : Rat) / 3) / ((1 : Rat) / (12 * (M : Rat) * (M : Rat)))

/-! ### 5. Exact `Q16.16` 3×3 Symmetric LoftQ Operator & Cycle Witnesses -/

/-- Upper-triangular storage of a `3 × 3` symmetric matrix `(a00, a01, a02, a11, a12, a22)`. -/
structure Sym3 where
  a00 : Int
  a01 : Int
  a02 : Int
  a11 : Int
  a12 : Int
  a22 : Int
  deriving DecidableEq, Repr

def zeroSym3 : Sym3 := ⟨0, 0, 0, 0, 0, 0⟩

def sym3Sub (A B : Sym3) : Sym3 :=
  ⟨A.a00 - B.a00, A.a01 - B.a01, A.a02 - B.a02,
   A.a11 - B.a11, A.a12 - B.a12, A.a22 - B.a22⟩

/-- Exact Frobenius squared norm of a `3 × 3` symmetric matrix (weights `1, 2, 2, 1, 2, 1`). -/
def sym3FrobSq (A : Sym3) : Int :=
  A.a00 * A.a00 + 2 * (A.a01 * A.a01) + 2 * (A.a02 * A.a02) +
  A.a11 * A.a11 + 2 * (A.a12 * A.a12) + A.a22 * A.a22

/-- Bit-exact tie-away-from-zero integer division matching `div_round_exact` in the GPU/CPU harness. -/
def divRoundExact (num den : Int) : Int :=
  if den ≤ 0 then 0
  else if 0 ≤ num then (num + den / 2) / den
  else -(((-num) + den / 2) / den)

/-- Structurally recursive exact integer square root `⌊√n⌋` for all `n < 2^80`. -/
def isqrtAux (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc =>
    let cand := acc + (1 <<< k)
    if cand * cand ≤ n then isqrtAux n k cand else isqrtAux n k acc

/-- Exact integer square root for nonnegative `Int` (`n < 2^80`). -/
def isqrtInt (n : Int) : Int :=
  if n ≤ 0 then 0 else (isqrtAux n.toNat 40 0 : Int)

/-- One fixed-point `Q16.16` power-iteration step for a `3 × 3` symmetric matrix. -/
def powerIterStep (A : Sym3) (v : Int × Int × Int) : Int × Int × Int :=
  let (v0, v1, v2) := v
  let w0 := divRoundExact (A.a00 * v0 + A.a01 * v1 + A.a02 * v2) 65536
  let w1 := divRoundExact (A.a01 * v0 + A.a11 * v1 + A.a12 * v2) 65536
  let w2 := divRoundExact (A.a02 * v0 + A.a12 * v1 + A.a22 * v2) 65536
  let wn2 := w0 * w0 + w1 * w1 + w2 * w2
  if wn2 == 0 then v
  else
    let wn := isqrtInt wn2
    if wn == 0 then v
    else
      let sgn : Int :=
        if w0 < 0 || (w0 == 0 && w1 < 0) || (w0 == 0 && w1 == 0 && w2 < 0) then -1 else 1
      (divRoundExact (sgn * w0 * 65536) wn,
       divRoundExact (sgn * w1 * 65536) wn,
       divRoundExact (sgn * w2 * 65536) wn)

def powerIterN (A : Sym3) : Nat → Int × Int × Int → Int × Int × Int
  | 0, v => v
  | k + 1, v => powerIterN A k (powerIterStep A v)

/-- Bit-exact `Q16.16` rank-1 symmetric SVD (`cpu_svd1_sym3x3_exact`). -/
def svd1Sym3Q16 (A : Sym3) : Sym3 :=
  let n0 := A.a00 * A.a00 + A.a01 * A.a01 + A.a02 * A.a02
  let n1 := A.a01 * A.a01 + A.a11 * A.a11 + A.a12 * A.a12
  let n2 := A.a02 * A.a02 + A.a12 * A.a12 + A.a22 * A.a22
  let (bestN2, c0, c1, c2) :=
    if n1 > n0 then
      if n2 > n1 then (n2, A.a02, A.a12, A.a22) else (n1, A.a01, A.a11, A.a12)
    else
      if n2 > n0 then (n2, A.a02, A.a12, A.a22) else (n0, A.a00, A.a01, A.a02)
  if bestN2 == 0 then zeroSym3
  else
    let nrm0 := isqrtInt bestN2
    let nrm := if nrm0 == 0 then 1 else nrm0
    let vInit := (divRoundExact (c0 * 65536) nrm,
                  divRoundExact (c1 * 65536) nrm,
                  divRoundExact (c2 * 65536) nrm)
    let (v0, v1, v2) := powerIterN A 24 vInit
    let av0 := divRoundExact (A.a00 * v0 + A.a01 * v1 + A.a02 * v2) 65536
    let av1 := divRoundExact (A.a01 * v0 + A.a11 * v1 + A.a12 * v2) 65536
    let av2 := divRoundExact (A.a02 * v0 + A.a12 * v1 + A.a22 * v2) 65536
    let vAv := v0 * av0 + v1 * av1 + v2 * av2
    let v2n := v0 * v0 + v1 * v1 + v2 * v2
    if v2n == 0 then zeroSym3
    else
      let lam := divRoundExact vAv (v2n / 65536)
      let s32 : Int := 4294967296
      ⟨divRoundExact (lam * v0 * v0) s32,
       divRoundExact (lam * v0 * v1) s32,
       divRoundExact (lam * v0 * v2) s32,
       divRoundExact (lam * v1 * v1) s32,
       divRoundExact (lam * v1 * v2) s32,
       divRoundExact (lam * v2 * v2) s32⟩

def absInt (x : Int) : Int := if x < 0 then -x else x

/-- Bit-exact `M = 1` absmax ternary quantizer on `Sym3` (`cpu_quant_absmax_sym3x3`). -/
def quantAbsmaxTernSym3 (R : Sym3) : Sym3 :=
  let mx := max (max (absInt R.a00) (absInt R.a01))
                (max (max (absInt R.a02) (absInt R.a11))
                     (max (absInt R.a12) (absInt R.a22)))
  if mx == 0 then zeroSym3
  else
    let q (x : Int) : Int :=
      let c := max (-1) (min 1 (divRoundExact x mx))
      c * mx
    ⟨q R.a00, q R.a01, q R.a02, q R.a11, q R.a12, q R.a22⟩

/-- One LoftQ alternating step `(Q_t -> L_t = SVD_1(W - Q_t) -> Q_{t+1} = Quant_absmax(W - L_t))`. -/
def loftqStepQ16 (W Q : Sym3) : Sym3 :=
  let L := svd1Sym3Q16 (sym3Sub W Q)
  quantAbsmaxTernSym3 (sym3Sub W L)

/-- Squared Frobenius error `‖W - Q_{t+1} - L_t‖_F^2` at step `t`. -/
def loftqStepErrQ16 (W Q : Sym3) : Int :=
  let L := svd1Sym3Q16 (sym3Sub W Q)
  let Qnext := quantAbsmaxTernSym3 (sym3Sub W L)
  sym3FrobSq (sym3Sub (sym3Sub W Qnext) L)

/-- Iterate `loftqStepQ16` `t` times from initial state `Q0`. -/
def loftqIterQ16 (W Q0 : Sym3) : Nat → Sym3
  | 0 => Q0
  | t + 1 => loftqStepQ16 W (loftqIterQ16 W Q0 t)

/-- Scale integer `Sym3` to `Q16.16`. -/
def toQ16Sym3 (W : Sym3) : Sym3 :=
  ⟨W.a00 * 65536, W.a01 * 65536, W.a02 * 65536,
   W.a11 * 65536, W.a12 * 65536, W.a22 * 65536⟩

/-- GPU-discovered `3 × 3` symmetric period-2 LoftQ witness:
    `[[149, 91, 350], [91, 920, 978], [350, 978, 297]]`. -/
def W_cyc2_int : Sym3 := ⟨149, 91, 350, 920, 978, 297⟩
def W_cyc2_q16 : Sym3 := toQ16Sym3 W_cyc2_int

/-- GPU-discovered `3 × 3` symmetric period-3 LoftQ witness:
    `[[-671, -527, 370], [-527, 259, -458], [370, -458, -906]]`. -/
def W_cyc3_int : Sym3 := ⟨-671, -527, 370, 259, -458, -906⟩
def W_cyc3_q16 : Sym3 := toQ16Sym3 W_cyc3_int

end LoftqCyclesRank1
