/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Shared Pure-`Init` Definitions (`octonion-rope-welch-frames`)

All public definitions shared between `Challenge.lean` and `Solution.lean`.
Pure Lean 4 `Init` only — zero Mathlib dependencies.
-/

namespace OctonionRopeWelch

/-- Finite sum of an `Int`-valued function over `Fin n`. -/
def sumInt : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | _ + 1, f => sumInt (fun i => f i.castSucc) + f ⟨_, Nat.lt_succ_self _⟩

/-- Finite sum of a `Rat`-valued function over `Fin n`. -/
def sumRat : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | _ + 1, f => sumRat (fun i => f i.castSucc) + f ⟨_, Nat.lt_succ_self _⟩

/-- An `m × n` integer matrix. -/
abbrev IntMat (m n : Nat) := Fin m → Fin n → Int

/-- An `m × n` rational matrix. -/
abbrev RatMat (m n : Nat) := Fin m → Fin n → Rat

/-- Integer matrix transpose. -/
def transpose {m n : Nat} (A : IntMat m n) : IntMat n m :=
  fun i j => A j i

/-- Integer matrix multiplication. -/
def matMul {m k n : Nat} (A : IntMat m k) (B : IntMat k n) : IntMat m n :=
  fun i j => sumInt (fun t => A i t * B t j)

/-- Integer `n × n` identity matrix. -/
def idMat (n : Nat) : IntMat n n :=
  fun i j => if i = j then 1 else 0

/-- Integer scalar multiplication of a matrix. -/
def scaleMat {m n : Nat} (c : Int) (A : IntMat m n) : IntMat m n :=
  fun i j => c * A i j

/-- Exact integer column-orthogonality `A^T A = c I_n`. -/
def isOrthogonal {m n : Nat} (A : IntMat m n) (c : Int) : Prop :=
  matMul (transpose A) A = scaleMat c (idMat n)

/-- Rational matrix transpose. -/
def ratTranspose {m n : Nat} (A : RatMat m n) : RatMat n m :=
  fun i j => A j i

/-- Rational matrix multiplication. -/
def ratMatMul {m k n : Nat} (A : RatMat m k) (B : RatMat k n) : RatMat m n :=
  fun i j => sumRat (fun t => A i t * B t j)

/-- Rational `n × n` identity matrix. -/
def ratIdMat (n : Nat) : RatMat n n :=
  fun i j => if i = j then 1 else 0

/-- Exact rational column-orthogonality `A^T A = I_n`. -/
def isRatOrthogonal {m n : Nat} (A : RatMat m n) : Prop :=
  ratMatMul (ratTranspose A) A = ratIdMat n

/-! ## Frontier 1B: 4D Power-of-2 Quaternion Rigidity -/

/-- The 24 integer solutions to `a^2 + b^2 + c^2 + d^2 = 2` (permutations of `(±1, ±1, 0, 0)`). -/
def baseHurwitz2 : List (Int × Int × Int × Int) :=
  [ (1, 1, 0, 0), (1, -1, 0, 0), (-1, 1, 0, 0), (-1, -1, 0, 0),
    (1, 0, 1, 0), (1, 0, -1, 0), (-1, 0, 1, 0), (-1, 0, -1, 0),
    (1, 0, 0, 1), (1, 0, 0, -1), (-1, 0, 0, 1), (-1, 0, 0, -1),
    (0, 1, 1, 0), (0, 1, -1, 0), (0, -1, 1, 0), (0, -1, -1, 0),
    (0, 1, 0, 1), (0, 1, 0, -1), (0, -1, 0, 1), (0, -1, 0, -1),
    (0, 0, 1, 1), (0, 0, 1, -1), (0, 0, -1, 1), (0, 0, -1, -1) ]

/-- The 24 integer solutions to `a^2 + b^2 + c^2 + d^2 = 4`:
    8 permutations of `(±2, 0, 0, 0)` and 16 sign vectors `(±1, ±1, ±1, ±1)`. -/
def baseHurwitz4 : List (Int × Int × Int × Int) :=
  [ (2, 0, 0, 0), (-2, 0, 0, 0), (0, 2, 0, 0), (0, -2, 0, 0),
    (0, 0, 2, 0), (0, 0, -2, 0), (0, 0, 0, 2), (0, 0, 0, -2),
    (1, 1, 1, 1), (1, 1, 1, -1), (1, 1, -1, 1), (1, 1, -1, -1),
    (1, -1, 1, 1), (1, -1, 1, -1), (1, -1, -1, 1), (1, -1, -1, -1),
    (-1, 1, 1, 1), (-1, 1, 1, -1), (-1, 1, -1, 1), (-1, 1, -1, -1),
    (-1, -1, 1, 1), (-1, -1, 1, -1), (-1, -1, -1, 1), (-1, -1, -1, -1) ]

/-! ## Frontier 1A & 1B: 2D Pythagorean, 4D Quaternion, and 8D Octonion RoPE -/

/-- Unnormalized integer 2D Pythagorean RoPE matrix `R_2(a, b)` with `R_2^T R_2 = (a^2 + b^2)^2 I_2`. -/
def pythagoreanRoPE (a b : Int) : IntMat 2 2
  | ⟨0, _⟩, ⟨0, _⟩ => a * a - b * b
  | ⟨0, _⟩, ⟨1, _⟩ => -(2 * a * b)
  | ⟨1, _⟩, ⟨0, _⟩ => 2 * a * b
  | ⟨1, _⟩, ⟨1, _⟩ => a * a - b * b

/-- Normalized rational 2D Pythagorean RoPE matrix `R_2(a, b) / (a^2 + b^2)`. -/
def pythagoreanRoPERat (a b : Int) : RatMat 2 2 :=
  fun i j => ((pythagoreanRoPE a b i j : Int) : Rat) / (((a * a + b * b : Int) : Rat))

/-- 4D Hamilton quaternion left-multiplication matrix `L_H(a, b, c, d)`. -/
def quaternionLeft (a b c d : Int) : IntMat 4 4
  | ⟨0, _⟩, ⟨0, _⟩ => a
  | ⟨0, _⟩, ⟨1, _⟩ => -b
  | ⟨0, _⟩, ⟨2, _⟩ => -c
  | ⟨0, _⟩, ⟨3, _⟩ => -d
  | ⟨1, _⟩, ⟨0, _⟩ => b
  | ⟨1, _⟩, ⟨1, _⟩ => a
  | ⟨1, _⟩, ⟨2, _⟩ => -d
  | ⟨1, _⟩, ⟨3, _⟩ => c
  | ⟨2, _⟩, ⟨0, _⟩ => c
  | ⟨2, _⟩, ⟨1, _⟩ => d
  | ⟨2, _⟩, ⟨2, _⟩ => a
  | ⟨2, _⟩, ⟨3, _⟩ => -b
  | ⟨3, _⟩, ⟨0, _⟩ => d
  | ⟨3, _⟩, ⟨1, _⟩ => -c
  | ⟨3, _⟩, ⟨2, _⟩ => b
  | ⟨3, _⟩, ⟨3, _⟩ => a

/-- 8D Cayley–Dickson octonion left-multiplication matrix `L_O(x)`
    (Fano plane triples: `123, 145, 176, 246, 257, 347, 365`). -/
def octonionLeft (x : Fin 8 → Int) : IntMat 8 8 :=
  let a := x ⟨0, by decide⟩
  let b := x ⟨1, by decide⟩
  let c := x ⟨2, by decide⟩
  let d := x ⟨3, by decide⟩
  let e := x ⟨4, by decide⟩
  let f := x ⟨5, by decide⟩
  let g := x ⟨6, by decide⟩
  let h := x ⟨7, by decide⟩
  fun i j =>
    match i.val with
    | 0 => match j.val with | 0 => a | 1 => -b | 2 => -c | 3 => -d | 4 => -e | 5 => -f | 6 => -g | 7 => -h | _ => 0
    | 1 => match j.val with | 0 => b | 1 => a  | 2 => -d | 3 => c  | 4 => -f | 5 => e  | 6 => h  | 7 => -g | _ => 0
    | 2 => match j.val with | 0 => c | 1 => d  | 2 => a  | 3 => -b | 4 => -g | 5 => -h | 6 => e  | 7 => f  | _ => 0
    | 3 => match j.val with | 0 => d | 1 => -c | 2 => b  | 3 => a  | 4 => -h | 5 => g  | 6 => -f | 7 => e  | _ => 0
    | 4 => match j.val with | 0 => e | 1 => f  | 2 => g  | 3 => h  | 4 => a  | 5 => -b | 6 => -c | 7 => -d | _ => 0
    | 5 => match j.val with | 0 => f | 1 => -e | 2 => h  | 3 => -g | 4 => b  | 5 => a  | 6 => d  | 7 => -c | _ => 0
    | 6 => match j.val with | 0 => g | 1 => -h | 2 => -e | 3 => f  | 4 => c  | 5 => -d | 6 => a  | 7 => b  | _ => 0
    | 7 => match j.val with | 0 => h | 1 => g  | 2 => -f | 3 => -e | 4 => d  | 5 => c  | 6 => -b | 7 => a  | _ => 0
    | _ => 0

/-- Normalized rational 8D octonion RoPE matrix `L_O(x) / M`. -/
def octonionRoPERat (x : Fin 8 → Int) (M : Int) : RatMat 8 8 :=
  fun i j => ((octonionLeft x i j : Int) : Rat) / (M : Rat)

/-- Concrete Llama-2 (`θ_0 = 1.0`) power-of-2 octonion RoPE witness (`>> 16` pure bit-shift,
    only 5 nonzeros, exact norm `2^32 = (2^16)^2`). -/
def llama2Octonion0 : Fin 8 → Int
  | ⟨0, _⟩ => 35409
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 7787
  | ⟨3, _⟩ => 7822
  | ⟨4, _⟩ => 54031
  | ⟨5, _⟩ => 0
  | ⟨6, _⟩ => 0
  | ⟨7, _⟩ => 0

/-! ## Frontier 2: Welch Frobenius Lower Bound & 5 Exact Welch-Tight Sparse Ternary Frames -/

/-- Column inner product `⟨S_{j1}, S_{j2}⟩ = ∑_i S_{i, j1} * S_{i, j2}`. -/
def colInner {m d : Nat} (S : IntMat m d) (j1 j2 : Fin d) : Int :=
  sumInt (fun i => S i j1 * S i j2)

/-- Total off-diagonal squared Gram energy `Φ(S) = ∑_{j1 ≠ j2} ⟨S_{j1}, S_{j2}⟩^2`. -/
def offDiagGramEnergy {m d : Nat} (S : IntMat m d) : Int :=
  sumInt (fun j1 => sumInt (fun j2 => if j1 = j2 then 0 else (colInner S j1 j2) * (colInner S j1 j2)))

/-- Ternary entry predicate `x ∈ {-1, 0, +1}`. -/
def isTernary (x : Int) : Prop :=
  x = -1 ∨ x = 0 ∨ x = 1

/-- Predicate bundling all exact Welch-tight sparse ternary frame properties for an `m × d` matrix:
    ternary entries, exact column squared norm `s`, max off-diagonal inner product `M` (both upper
    bound and attainment), and exact Welch Frobenius equality `m * Φ(S) = d * s^2 * (d - m)`. -/
def isWelchTightSparseTernaryFrame {m d : Nat} (s M : Nat) (S : IntMat m d) : Prop :=
  (∀ i j, isTernary (S i j)) ∧
  (∀ j, colInner S j j = (s : Int)) ∧
  (∀ j1 j2, j1 ≠ j2 → -(M : Int) ≤ colInner S j1 j2 ∧ colInner S j1 j2 ≤ (M : Int)) ∧
  (∃ j1 j2, j1 ≠ j2 ∧ (colInner S j1 j2 = (M : Int) ∨ colInner S j1 j2 = -(M : Int))) ∧
  (m : Int) * offDiagGramEnergy S = (d : Int) * ((s : Int) * (s : Int)) * ((d : Int) - (m : Int))

/-- Decode a column-bitmask sparse ternary matrix from positive/negative bitmasks. -/
def decodeBitmaskFrame (m d : Nat) (pos neg : Fin d → Nat) : IntMat m d :=
  fun i j =>
    if Nat.testBit (pos j) i.val then 1
    else if Nat.testBit (neg j) i.val then -1
    else 0

/-- Helper to index a list of `Nat` by `Fin d` (defaulting to `0`). -/
def listGetNat {d : Nat} (xs : List Nat) (j : Fin d) : Nat :=
  xs.getD j.val 0

/-- GPU-discovered exact Welch-tight sparse ternary frame `(8, 16), s = 3, M = 1, Φ = 144`. -/
def frame_8_16_s3 : IntMat 8 16 :=
  decodeBitmaskFrame 8 16
    (listGetNat [0x11, 0x84, 0x08, 0x02, 0x62, 0x8a, 0x80, 0x50,
                 0x04, 0x14, 0x09, 0xa1, 0x12, 0x18, 0x4c, 0x03])
    (listGetNat [0x02, 0x40, 0x05, 0xc0, 0x00, 0x00, 0x24, 0x20,
                 0x30, 0x01, 0x80, 0x00, 0x08, 0x40, 0x00, 0x20])

/-- GPU-discovered exact Welch-tight sparse ternary frame `(8, 16), s = 4, M = 2, Φ = 256`. -/
def frame_8_16_s4 : IntMat 8 16 :=
  decodeBitmaskFrame 8 16
    (listGetNat [0x20, 0x8a, 0x50, 0x80, 0x00, 0x80, 0x41, 0x12,
                 0x01, 0x10, 0xd0, 0x19, 0x31, 0x02, 0x4a, 0x08])
    (listGetNat [0x16, 0x04, 0x81, 0x26, 0xe2, 0x61, 0x28, 0x48,
                 0xa4, 0x0d, 0x02, 0x40, 0x04, 0x1c, 0x20, 0x85])

/-- GPU-discovered exact Welch-tight sparse ternary frame `(8, 16), s = 5, M = 2, Φ = 400`. -/
def frame_8_16_s5 : IntMat 8 16 :=
  decodeBitmaskFrame 8 16
    (listGetNat [0x42, 0x1d, 0x18, 0x20, 0x02, 0x0f, 0x51, 0x28,
                 0x26, 0xc0, 0x81, 0x00, 0x88, 0x92, 0x21, 0x69])
    (listGetNat [0xb0, 0x40, 0x85, 0xca, 0xe4, 0x10, 0x82, 0x15,
                 0x09, 0x23, 0x2c, 0xf2, 0x52, 0x44, 0x1c, 0x04])

/-- GPU-discovered exact Welch-tight sparse ternary frame `(12, 24), s = 3, M = 1, Φ = 216`. -/
def frame_12_24_s3 : IntMat 12 24 :=
  decodeBitmaskFrame 12 24
    (listGetNat [0x840, 0x020, 0x080, 0x00c, 0x00a, 0x011, 0xa01, 0x001,
                 0x400, 0x400, 0x044, 0x002, 0x412, 0x000, 0x000, 0x022,
                 0x000, 0x440, 0x004, 0x280, 0x900, 0x405, 0x600, 0x100])
    (listGetNat [0x010, 0x102, 0x220, 0x080, 0x100, 0x008, 0x000, 0x810,
                 0x202, 0x050, 0x020, 0x018, 0x000, 0x188, 0x160, 0x200,
                 0x0a4, 0x004, 0x009, 0x800, 0x040, 0x000, 0x001, 0x880])

/-- GPU-discovered exact Welch-tight sparse ternary frame `(12, 24), s = 4, M = 1, Φ = 384`. -/
def frame_12_24_s4 : IntMat 12 24 :=
  decodeBitmaskFrame 12 24
    (listGetNat [0x003, 0x000, 0x010, 0x100, 0x114, 0x820, 0x004, 0x202,
                 0x081, 0x400, 0x4a1, 0x002, 0x008, 0x008, 0x080, 0x010,
                 0x00e, 0x4c0, 0x080, 0xe00, 0xc00, 0x800, 0x801, 0x004])
    (listGetNat [0x210, 0x892, 0x288, 0x054, 0x040, 0x600, 0x02a, 0x180,
                 0x420, 0xa40, 0x000, 0x02c, 0x301, 0x026, 0x441, 0x144,
                 0x020, 0x001, 0x908, 0x040, 0x220, 0x019, 0x102, 0x150])

/-! ## Frontier 3: Rational Softmax Top-K & Quantized-Logit L1 Laws -/

/-- Exact rational softmax distribution `p_i = w_i / (∑_j w_j)`. -/
def softmaxRat {N : Nat} (w : Fin N → Rat) : Fin N → Rat :=
  let Z := sumRat w
  fun i => w i / Z

/-- Exact rational top-`K` truncated softmax distribution (keeping indices `i.val < K`). -/
def topKSoftmaxRat {N : Nat} (K : Nat) (w : Fin N → Rat) : Fin N → Rat :=
  let H := sumRat (fun i : Fin N => if i.val < K then w i else 0)
  fun i => if i.val < K then w i / H else 0

/-- Exact rational `ℓ_1` distance `∑_i |p_i - q_i|`. -/
def l1DistRat {N : Nat} (p q : Fin N → Rat) : Rat :=
  sumRat (fun i => (p i - q i).abs)

end OctonionRopeWelch
