/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`mhc-sinkhorn-fp8-bounds`)

Pure-`Init` (zero Mathlib) definitions for:
1. Rational vectors, matrices, inner products, squared norms, and Sinkhorn normalization.
2. Bit-exact IEEE-754 RNE BF16 and OCP FP8-E4M3FN conversion, sequential Mode-A Sinkhorn,
   and exact-sum Mode-B Sinkhorn.
3. Constructive witnesses: anti-diagonal swamping matrices, support-collapse fixed points
   (`n = 4` GPU witness and general `n ≥ 3` family), Mode-B symmetric overshoot fixed points,
   and zero-division dyadic-orthogonal mixers (`n = 4` Hamilton-Quaternion / Hadamard and
   `n = 8` dyadic Householder).
-/

namespace MhcSinkhornFp8

/-! ### 1. Rational Vectors, Matrices, and Linear Algebra Primitives -/

abbrev RatVec (n : Nat) := Fin n → Rat
abbrev RatMat (n : Nat) := Fin n → Fin n → Rat

/-- Sum of `f : Fin n → Rat` over `0, 1, ..., n - 1`. -/
def sumFinRat : (n : Nat) → (Fin n → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => sumFinRat n (fun i => f i.castSucc) + f (Fin.last n)

/-- Row sum of a rational `n × n` matrix. -/
def rowSum {n : Nat} (A : RatMat n) (i : Fin n) : Rat :=
  sumFinRat n (fun j => A i j)

/-- Column sum of a rational `n × n` matrix. -/
def colSum {n : Nat} (A : RatMat n) (j : Fin n) : Rat :=
  sumFinRat n (fun i => A i j)

/-- Matrix-vector product `(A v)_i = ∑_j A_{ij} v_j`. -/
def matVecMul {n : Nat} (A : RatMat n) (v : RatVec n) : RatVec n :=
  fun i => sumFinRat n (fun j => A i j * v j)

/-- Matrix-matrix product `(A B)_{ij} = ∑_k A_{ik} B_{kj}`. -/
def matMul {n : Nat} (A B : RatMat n) : RatMat n :=
  fun i j => sumFinRat n (fun k => A i k * B k j)

/-- Matrix transpose `(A^T)_{ij} = A_{ji}`. -/
def matTranspose {n : Nat} (A : RatMat n) : RatMat n :=
  fun i j => A j i

/-- Identity matrix `I_n`. -/
def matId (n : Nat) : RatMat n :=
  fun i j => if i = j then 1 else 0

/-- Squared Euclidean norm `‖v‖_2^2 = ∑_i v_i^2`. -/
def normSq {n : Nat} (v : RatVec n) : Rat :=
  sumFinRat n (fun i => v i * v i)

/-- Standard Euclidean inner product `⟨u, v⟩ = ∑_i u_i v_i`. -/
def dotRat {n : Nat} (u v : RatVec n) : Rat :=
  sumFinRat n (fun i => u i * v i)

/-- All-ones vector `(1, ..., 1)`. -/
def onesVec (n : Nat) : RatVec n :=
  fun _ => 1

/-- Natural-number power of a rational number. -/
def ratPow (a : Rat) : Nat → Rat
  | 0 => 1
  | k + 1 => a * ratPow a k

/-- Iterated matrix-vector application `A^L v`. -/
def vecApplyIter {n : Nat} (A : RatMat n) : Nat → RatVec n → RatVec n
  | 0, v => v
  | k + 1, v => matVecMul A (vecApplyIter A k v)

/-- Sequential application of a list of layer matrices `[Q_1, ..., Q_L]` to `v`. -/
def applyLayerList {n : Nat} : List (RatMat n) → RatVec n → RatVec n
  | [], v => v
  | Q :: rest, v => applyLayerList rest (matVecMul Q v)

/-- Exact orthogonality predicate `Q^T Q = I_n`. -/
def isOrthogonalRat {n : Nat} (Q : RatMat n) : Prop :=
  matMul (matTranspose Q) Q = matId n

/-- Doubly-stochastic matrix predicate (`A_{ij} ≥ 0`, all row and column sums `= 1`). -/
def isDoublyStochastic {n : Nat} (A : RatMat n) : Prop :=
  (∀ i j : Fin n, (0 : Rat) ≤ A i j) ∧
  (∀ i : Fin n, rowSum A i = 1) ∧
  (∀ j : Fin n, colSum A j = 1)

/-! ### 2. Exact Rational Sinkhorn–Knopp Operators and Diagonal Scalings -/

/-- Exact rational row normalization `R(A)` (zero rows remain zero). -/
def rowNorm {n : Nat} (A : RatMat n) : RatMat n :=
  fun i j =>
    let s := rowSum A i
    if s = 0 then 0 else A i j / s

/-- Exact rational column normalization `C(A)` (zero columns remain zero). -/
def colNorm {n : Nat} (A : RatMat n) : RatMat n :=
  fun i j =>
    let s := colSum A j
    if s = 0 then 0 else A i j / s

/-- One full exact-rational Sinkhorn–Knopp iteration `C(R(A))`. -/
def sinkhornStep {n : Nat} (A : RatMat n) : RatMat n :=
  colNorm (rowNorm A)

/-- Left diagonal scaling `(diag(d) A)_{ij} = d_i A_{ij}`. -/
def diagScaleLeft {n : Nat} (d : RatVec n) (A : RatMat n) : RatMat n :=
  fun i j => d i * A i j

/-- Right diagonal scaling `(A diag(e))_{ij} = A_{ij} e_j`. -/
def diagScaleRight {n : Nat} (A : RatMat n) (e : RatVec n) : RatMat n :=
  fun i j => A i j * e j

/-! ### 3. Bit-Exact RNE OCP FP8-E4M3FN and IEEE-754 BF16 Arithmetic -/

/-- Exact round-to-nearest-even (RNE) integer quotient of `p / q` (`q > 0`). -/
def rneDiv (p q : Nat) : Nat :=
  let d := p / q
  let r := p % q
  if 2 * r > q ∨ (2 * r = q ∧ d % 2 = 1) then d + 1 else d

/-- Exact `(num, den)` rational representation of an unsigned nonnegative OCP FP8-E4M3FN encoding. -/
def fp8NumDen (bits : Nat) : Nat × Nat :=
  let b := bits % 128
  let e := (b / 8) % 16
  let m := b % 8
  if e = 0 then
    (m, 512)
  else
    ((8 + m) * (2 ^ (e - 1)), 512)

/-- Exact rational value of an unsigned nonnegative OCP FP8-E4M3FN encoding (`0x00..0x7E`). -/
def fp8ToRat (bits : Nat) : Rat :=
  let nd := fp8NumDen bits
  (nd.1 : Rat) / (nd.2 : Rat)

/-- Pure-`Nat` exact RNE encoding of `n / d` (`d > 0`) to OCP FP8-E4M3FN (saturating at `0x7E = 448`). -/
def natDivToFp8 (n d : Nat) : Nat :=
  if n = 0 ∨ d = 0 then 0
  else
    let sn := n * 512
    if sn < 8 * d then
      let q := rneDiv sn d
      if q ≥ 8 then 8 else q
    else
      let q0 := sn / d
      let hb := Nat.log2 q0
      let e := hb - 2
      if e > 15 then 0x7E
      else
        let shift := e - 1
        let sig := rneDiv sn (d * (2 ^ shift))
        if sig = 16 then
          if e + 1 > 15 then 0x7E else (e + 1) * 8
        else if e = 15 ∧ sig ≥ 15 then
          0x7E
        else
          e * 8 + (sig - 8)

/-- Exact RNE encoding of a nonnegative rational `val` to OCP FP8-E4M3FN (saturating at `0x7E = 448`). -/
def ratToFp8 (val : Rat) : Nat :=
  if val ≤ 0 then 0
  else natDivToFp8 val.num.toNat val.den

/-- Native RNE FP8-E4M3FN addition of two nonnegative encodings. -/
def fp8Add (a b : Nat) : Nat :=
  let (n1, d1) := fp8NumDen a
  let (n2, d2) := fp8NumDen b
  natDivToFp8 (n1 * d2 + n2 * d1) (d1 * d2)

/-- Native RNE FP8-E4M3FN division of two nonnegative encodings. -/
def fp8Div (a b : Nat) : Nat :=
  let (n1, d1) := fp8NumDen a
  let (n2, d2) := fp8NumDen b
  if n2 = 0 then 0 else natDivToFp8 (n1 * d2) (d1 * n2)

/-- Exact `(num, den)` rational representation of an unsigned nonnegative IEEE-754 BF16 encoding. -/
def bf16NumDen (bits : Nat) : Nat × Nat :=
  let b := bits % 32768
  let e := (b / 128) % 256
  let m := b % 128
  if e = 0 then
    (m, 2 ^ 133)
  else if e ≥ 134 then
    ((128 + m) * (2 ^ (e - 134)), 1)
  else
    (128 + m, 2 ^ (134 - e))

/-- Exact rational value of an unsigned nonnegative IEEE-754 BF16 encoding (`e < 255`). -/
def bf16ToRat (bits : Nat) : Rat :=
  let nd := bf16NumDen bits
  (nd.1 : Rat) / (nd.2 : Rat)

/-- Pure-`Nat` exact RNE encoding of `n / d` (`d > 0`) to IEEE-754 BF16 (`0x7F80` for `+Inf`). -/
def natDivToBf16 (n d : Nat) : Nat :=
  if n = 0 ∨ d = 0 then 0
  else
    let exp0 : Int := (Nat.log2 n : Int) - (Nat.log2 d : Int)
    let exp : Int :=
      if exp0 ≥ 0 then
        if n < d * (2 ^ exp0.toNat) then exp0 - 1 else exp0
      else
        if n * (2 ^ (-exp0).toNat) < d then exp0 - 1 else exp0
    if exp < -126 then
      let q := rneDiv (n * (2 ^ 133)) d
      if q ≥ 128 then 0x0080 else q
    else if exp > 127 then
      0x7F80
    else
      let shift : Int := 7 - exp
      let sig :=
        if shift ≥ 0 then rneDiv (n * (2 ^ shift.toNat)) d
        else rneDiv n (d * (2 ^ (-shift).toNat))
      if sig = 256 then
        if exp + 1 > 127 then 0x7F80
        else ((exp + 128).toNat) * 128
      else
        ((exp + 127).toNat) * 128 + (sig % 128)

/-- Exact RNE encoding of a nonnegative rational `val` to IEEE-754 BF16 (`0x7F80` for `+Inf`). -/
def ratToBf16 (val : Rat) : Nat :=
  if val ≤ 0 then 0
  else natDivToBf16 val.num.toNat val.den

/-- Native RNE BF16 addition of two nonnegative encodings. -/
def bf16Add (a b : Nat) : Nat :=
  let (n1, d1) := bf16NumDen a
  let (n2, d2) := bf16NumDen b
  natDivToBf16 (n1 * d2 + n2 * d1) (d1 * d2)

/-- Native RNE BF16 division of two nonnegative encodings. -/
def bf16Div (a b : Nat) : Nat :=
  let (n1, d1) := bf16NumDen a
  let (n2, d2) := bf16NumDen b
  if n2 = 0 then 0 else natDivToBf16 (n1 * d2) (d1 * n2)

/-- Hardware precision format descriptor for Sinkhorn–Knopp. -/
structure FloatFormat where
  toRat : Nat → Rat
  fromRat : Rat → Nat
  add : Nat → Nat → Nat
  div : Nat → Nat → Nat
  oneBits : Nat

def fp8Format : FloatFormat :=
  { toRat := fp8ToRat, fromRat := ratToFp8, add := fp8Add, div := fp8Div, oneBits := 0x38 }

def bf16Format : FloatFormat :=
  { toRat := bf16ToRat, fromRat := ratToBf16, add := bf16Add, div := bf16Div, oneBits := 0x3F80 }

/-- Left-to-right sequential floating-point sum `(((0 ⊕ f 0) ⊕ f 1) ⊕ ... ⊕ f (n - 1))`. -/
def seqSumFin (add : Nat → Nat → Nat) : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => add (seqSumFin add n (fun i => f i.castSucc)) (f (Fin.last n))

/-- Sequential hardware row sum of a bit-encoded matrix. -/
def hwRowSum (fmt : FloatFormat) {n : Nat} (H : Fin n → Fin n → Nat) (i : Fin n) : Nat :=
  seqSumFin fmt.add n (fun j => H i j)

/-- Sequential hardware column sum of a bit-encoded matrix. -/
def hwColSum (fmt : FloatFormat) {n : Nat} (H : Fin n → Fin n → Nat) (j : Fin n) : Nat :=
  seqSumFin fmt.add n (fun i => H i j)

/-- Mode-A (native sequential sum & division) row normalization step. -/
def sinkhornModeARow (fmt : FloatFormat) {n : Nat} (H : Fin n → Fin n → Nat) : Fin n → Fin n → Nat :=
  fun i j =>
    let s := hwRowSum fmt H i
    if s = 0 then H i j else fmt.div (H i j) s

/-- Mode-A (native sequential sum & division) column normalization step. -/
def sinkhornModeACol (fmt : FloatFormat) {n : Nat} (H : Fin n → Fin n → Nat) : Fin n → Fin n → Nat :=
  fun i j =>
    let s := hwColSum fmt H j
    if s = 0 then H i j else fmt.div (H i j) s

/-- One full Mode-A (native sequential RNE) Sinkhorn–Knopp iteration. -/
def sinkhornModeAStep (fmt : FloatFormat) {n : Nat} (H : Fin n → Fin n → Nat) : Fin n → Fin n → Nat :=
  sinkhornModeACol fmt (sinkhornModeARow fmt H)

/-- `T` iterations of Mode-A Sinkhorn–Knopp. -/
def sinkhornModeAIter (fmt : FloatFormat) {n : Nat} : Nat → (Fin n → Fin n → Nat) → (Fin n → Fin n → Nat)
  | 0, H => H
  | t + 1, H => sinkhornModeAStep fmt (sinkhornModeAIter fmt t H)

/-- Lift a bit-encoded matrix to its exact rational matrix. -/
def bitsMatToRat (fmt : FloatFormat) {n : Nat} (H : Fin n → Fin n → Nat) : RatMat n :=
  fun i j => fmt.toRat (H i j)

/-- Mode-B (exact rational row sum + RNE cast) row normalization step. -/
def sinkhornModeBRow (fmt : FloatFormat) {n : Nat} (H : Fin n → Fin n → Nat) : Fin n → Fin n → Nat :=
  fun i j =>
    let s := rowSum (bitsMatToRat fmt H) i
    if s = 0 then H i j else fmt.fromRat (fmt.toRat (H i j) / s)

/-- Mode-B (exact rational column sum + RNE cast) column normalization step. -/
def sinkhornModeBCol (fmt : FloatFormat) {n : Nat} (H : Fin n → Fin n → Nat) : Fin n → Fin n → Nat :=
  fun i j =>
    let s := colSum (bitsMatToRat fmt H) j
    if s = 0 then H i j else fmt.fromRat (fmt.toRat (H i j) / s)

/-- One full Mode-B (exact rational sum + native RNE cast) Sinkhorn–Knopp iteration. -/
def sinkhornModeBStep (fmt : FloatFormat) {n : Nat} (H : Fin n → Fin n → Nat) : Fin n → Fin n → Nat :=
  sinkhornModeBCol fmt (sinkhornModeBRow fmt H)

/-- `T` iterations of Mode-B Sinkhorn–Knopp. -/
def sinkhornModeBIter (fmt : FloatFormat) {n : Nat} : Nat → (Fin n → Fin n → Nat) → (Fin n → Fin n → Nat)
  | 0, H => H
  | t + 1, H => sinkhornModeBStep fmt (sinkhornModeBIter fmt t H)

/-! ### 4. Constructive Witnesses -/

/-- Anti-diagonal swamping matrix `H_anti(n, one, u, eps)`:
    `one` on `i + j = n - 1`, `u` below (`i + j > n - 1`), `eps` above (`i + j < n - 1`). -/
def antiDiagBits (n oneBits uBits epsBits : Nat) : Fin n → Fin n → Nat :=
  fun i j =>
    if i.val + j.val = n - 1 then oneBits
    else if i.val + j.val > n - 1 then uBits
    else epsBits

/-- BF16 anti-diagonal swamping matrix (`1.0 = 0x3F80`, `u = 2^-8 = 0x3B80`, `eps = 2^-14 = 0x3880`). -/
def bf16AntiDiag (n : Nat) : Fin n → Fin n → Nat :=
  antiDiagBits n 0x3F80 0x3B80 0x3880

/-- FP8-E4M3FN anti-diagonal swamping matrix (`1.0 = 0x38`, `u = 2^-4 = 0x18`, `eps = 2^-9 = 0x01`). -/
def fp8AntiDiag (n : Nat) : Fin n → Fin n → Nat :=
  antiDiagBits n 0x38 0x18 0x01

/-- GPU-discovered `n = 4` support-collapse fixed-point witness:
    `[[0,0,0,1], [0,1/2,0,0], [0,1/2,0,0], [1,0,1,0]]`. -/
def collapseMat4 : RatMat 4 :=
  fun i j =>
    match i.val, j.val with
    | 0, 3 => 1
    | 1, 1 => (1 : Rat) / 2
    | 2, 1 => (1 : Rat) / 2
    | 3, 0 => 1
    | 3, 2 => 1
    | _, _ => 0

/-- General `n × n` (`n ≥ 3`) support-collapse exact Sinkhorn fixed-point family attaining
    exact spectral norm squared `‖H‖_2^2 = n - 1`:
    row `n - 1` has `1` on columns `j < n - 1` and `0` on `n - 1`;
    rows `i < n - 1` have `1 / (n - 1)` on column `n - 1` and `0` elsewhere. -/
def collapseMatGen (n : Nat) : RatMat n :=
  fun i j =>
    if i.val = n - 1 then
      if j.val = n - 1 then 0 else 1
    else
      if j.val = n - 1 then (1 : Rat) / ((n - 1 : Nat) : Rat) else 0

/-- Symmetric diagonal-dominant matrix `I_n + δ (J_n - I_n)` in bit-encoded format. -/
def symDiagBits (n oneBits deltaBits : Nat) : Fin n → Fin n → Nat :=
  fun i j => if i = j then oneBits else deltaBits

/-- FP8-E4M3FN Mode-B fixed point at `n = 4`: `I_4 + (5/512)(J_4 - I_4)` (`0x38`, `0x05`). -/
def fp8ModeBFixed4 : Fin 4 → Fin 4 → Nat :=
  symDiagBits 4 0x38 0x05

/-- BF16 Mode-B fixed point at `n = 4`: `I_4 + (85/131072)(J_4 - I_4)` (`0x3F80`, `0x3A2A`). -/
def bf16ModeBFixed4 : Fin 4 → Fin 4 → Nat :=
  symDiagBits 4 0x3F80 0x3A2A

/-- `n = 4` Hamilton-Quaternion rational orthogonal mixer `(1/2) L(a, b, c, d)`. -/
def quatMixer4 (a b c d : Rat) : RatMat 4 :=
  fun i j =>
    let raw : Rat :=
      match i.val, j.val with
      | 0, 0 => a  | 0, 1 => -b | 0, 2 => -c | 0, 3 => -d
      | 1, 0 => b  | 1, 1 => a  | 1, 2 => -d | 1, 3 => c
      | 2, 0 => c  | 2, 1 => d  | 2, 2 => a  | 2, 3 => -b
      | 3, 0 => d  | 3, 1 => -c | 3, 2 => b  | 3, 3 => a
      | _, _ => 0
    raw / 2

/-- Zero-division `n = 4` dyadic Hadamard / unit-quaternion mixer (`q = (1, 1, 1, 1)`, entries `±1/2`). -/
def hadamardMixer4 : RatMat 4 :=
  quatMixer4 1 1 1 1

/-- Column-signed `n = 4` dyadic Hadamard mixer `H_4 diag(s)`. -/
def signedHadamard4 (s : Fin 4 → Rat) : RatMat 4 :=
  fun i j => hadamardMixer4 i j * s j

/-- Zero-division `n = 8` dyadic Householder mixer `I_8 - (1/8) v v^T` (exact `>> 3` when `‖v‖_2^2 = 16`). -/
def householder8 (v : RatVec 8) : RatMat 8 :=
  fun i j => (if i = j then 1 else 0) - ((1 : Rat) / 8) * (v i * v j)

end MhcSinkhornFp8
