/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions (`xor-vdc-fp4-dither`)

Pure-`Init` (zero Mathlib) exact rational and bitwise definitions for:
1. Bit-reversal, popcount, Walsh characters, and zero-carry XOR-VDC lane offsets.
2. Discrete `m`-bit stochastic rounding, unbiased expectation, and pairwise covariance.
3. Exact Walsh–Hadamard covariance matrices (`M_xor`, `M_xor_vdc`), eigenvalues, and OCP E2M1 ratios.
4. OCP E2M1 harmonic-mean worst-case relative SR variance bounds.
5. Antithetic paired SR covariance and pair variance.
6. Double-quantized GEMM bias for arbitrary `k`-bit PRNG couplings (`same`, `antithetic`,
   `msb_1bit_xor`, and 0-extra-bit `bitrev_k` Hammersley).
7. Single `2m`-bit (32-bit) split-word XOR-VDC double-quantized GEMM expectation and covariance.
-/

namespace XorVdcFp4Dither

/-! ### 1. Finite Sums and Rational Utilities -/

def absRat (x : Rat) : Rat :=
  if x < 0 then -x else x

def minRat (a b : Rat) : Rat :=
  if a ≤ b then a else b

def sumRange : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

def countRange : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, p => countRange n p + if p n then 1 else 0

/-! ### 2. Bitwise, Dyadic, and Walsh–Hadamard Primitives -/

/-- `b`-bit reversal of `x mod 2^b`. -/
def bitrev : Nat → Nat → Nat
  | 0, _ => 0
  | b + 1, x => (x % 2) * 2 ^ b + bitrev b (x / 2)

/-- Number of `1` bits in the lowest `b` bits of `x`. -/
def popcountBits : Nat → Nat → Nat
  | 0, _ => 0
  | b + 1, x => (x % 2) + popcountBits b (x / 2)

/-- Bit `s` of `x` (`0` or `1`). -/
def bitAt (s x : Nat) : Nat :=
  (x / 2 ^ s) % 2

/-- Dyadic sign `(-1)^(bit_s(x))` as an exact `Rat`. -/
def bitSign (s x : Nat) : Rat :=
  if bitAt s x = 0 then 1 else -1

/-- Walsh–Hadamard character `h_k(i) = (-1)^popcount(k & i)` on `b`-bit indices. -/
def walshSign (b k i : Nat) : Rat :=
  if popcountBits b (k &&& i) % 2 = 0 then 1 else -1

/-- Zero-carry XOR-VDC lane offset `bitrev_b(i) << (m - b)`. -/
def xorVdcOffset (m b i : Nat) : Nat :=
  bitrev b i <<< (m - b)

/-- Zero-carry XOR-VDC lane PRNG value `u_0 ^^^ (bitrev_b(i) << (m - b))`. -/
def xorVdcLane (m b i u0 : Nat) : Nat :=
  u0 ^^^ xorVdcOffset m b i

/-! ### 3. Discrete `m`-Bit Stochastic Rounding -/

/-- Exact stochastic rounding output on `[l, r]` with discrete threshold `p` and PRNG draw `u`. -/
def srVal (l r : Rat) (p u : Nat) : Rat :=
  if u < p then r else l

/-- Exact fractional SR error `1[u < p] - p / M` on unit interval. -/
def srErr (p M u : Nat) : Rat :=
  (if u < p then (1 : Rat) else 0) - (p : Rat) / (M : Rat)

/-- Exact discrete uniform expectation over `u ∈ {0, ..., M - 1}`. -/
def discreteMean (M : Nat) (f : Nat → Rat) : Rat :=
  sumRange M f / (M : Rat)

/-- Exact discrete covariance over `u ∈ {0, ..., M - 1}`. -/
def discreteCov (M : Nat) (f g : Nat → Rat) : Rat :=
  discreteMean M (fun u => (f u - discreteMean M f) * (g u - discreteMean M g))

/-- Exact discrete average SR error covariance over independent uniform `p1, p2 ∈ {0, ..., 2^m - 1}`. -/
def avgDiscreteSrCov (m : Nat) (uA uB : Nat → Nat) : Rat :=
  discreteMean (2 ^ m) (fun p1 =>
    discreteMean (2 ^ m) (fun p2 =>
      discreteCov (2 ^ m)
        (fun u => srErr p1 (2 ^ m) (uA u))
        (fun u => srErr p2 (2 ^ m) (uB u))))

/-- Closed-form dyadic XOR rank covariance term `(1 / (4 B^2)) * ∑_{s<b} 4^s (-1)^{bit_s(d1 ^^^ d2)}`. -/
def xorRankCov (b d1 d2 : Nat) : Rat :=
  sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s (d1 ^^^ d2)) /
    (4 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat))

/-- Exact closed-form discrete `m`-bit average pairwise covariance for offsets `d1, d2 < 2^b`. -/
def xorDiscreteAvgCovFormula (m b d1 d2 : Nat) : Rat :=
  xorRankCov b d1 d2 +
    (((2 ^ (m - b) : Nat) : Rat) * ((2 ^ (m - b) : Nat) : Rat) - 1) /
      (12 * ((2 ^ m : Nat) : Rat) * ((2 ^ m : Nat) : Rat))

/-! ### 4. Walsh–Hadamard Spectral Model and E2M1 Ratios -/

/-- Exact `B × B` average covariance matrix `M^{XOR}` for 1-PRNG dyadic XOR dithering (`B = 2^b`). -/
def xorCovMatrix (b i j : Nat) : Rat :=
  (if i = j then (1 : Rat) / 12 else 0) +
    (1 : Rat) / (12 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat)) +
    xorRankCov b i j

/-- Exact `B × B` average covariance matrix `M^{XOR-VDC}` with bit-reversed lane offsets. -/
def xorVdcCovMatrix (b i j : Nat) : Rat :=
  xorCovMatrix b (bitrev b i) (bitrev b j)

/-- Exact Walsh–Hadamard eigenvalue `λ_k(M^{XOR})` for `B = 2^b` and `k < 2^b`. -/
def xorWalshEig (b k : Nat) : Rat :=
  if k = 0 then
    (1 : Rat) / 12 + (1 : Rat) / (12 * ((2 ^ b : Nat) : Rat))
  else if popcountBits b k = 1 then
    (1 : Rat) / 12 + ((k : Rat) * (k : Rat)) / (4 * ((2 ^ b : Nat) : Rat))
  else
    (1 : Rat) / 12

/-- Exact Walsh–Hadamard eigenvalue `λ_k(M^{XOR-VDC}) = λ_{bitrev_b(k)}(M^{XOR})`. -/
def xorVdcWalshEig (b k : Nat) : Rat :=
  xorWalshEig b (bitrev b k)

/-- Matrix-vector product `(M v)_i` for `B = 2^b`. -/
def matVec (B : Nat) (M : Nat → Nat → Rat) (v : Nat → Rat) (i : Nat) : Rat :=
  sumRange B (fun j => M i j * v j)

/-- OCP E2M1 positive interval widths on `[0, 6]`. -/
def e2m1Widths : List Rat :=
  [1 / 2, 1 / 2, 1 / 2, 1 / 2, 1, 1, 2]

/-- Sum of `f h` over a list of rational widths. -/
def sumListRat (f : Rat → Rat) : List Rat → Rat
  | [] => 0
  | h :: hs => f h + sumListRat f hs

/-- Exact `E[h]` on uniform `[0, 6]` over the 7 OCP E2M1 intervals (`= 7/6`). -/
def e2m1MeanH : Rat :=
  sumListRat (fun h => h * h) e2m1Widths / 6

/-- Exact `E[h^2]` on uniform `[0, 6]` over the 7 OCP E2M1 intervals (`= 7/4`). -/
def e2m1MeanH2 : Rat :=
  sumListRat (fun h => h * h * h) e2m1Widths / 6

/-- Exact uncorrelated positive E2M1 block MSE ratio `1 - ((B - 1) / (2 B)) * (E[h]^2 / E[h^2])`. -/
def e2m1XorMseRatio (B : Nat) : Rat :=
  1 - (((B - 1 : Nat) : Rat) / (2 * (B : Rat))) * ((e2m1MeanH * e2m1MeanH) / e2m1MeanH2)

/-! ### 5. OCP E2M1 Harmonic-Mean Relative SR Variance -/

/-- Absolute SR variance `(x - l)(r - x)` on `[l, r]`. -/
def srVar (l r x : Rat) : Rat :=
  (x - l) * (r - x)

/-- Relative SR variance `(x - l)(r - x) / x^2`. -/
def relSrVar (l r x : Rat) : Rat :=
  srVar l r x / (x * x)

/-- Harmonic mean `2 l r / (l + r)`. -/
def harmonicMean (l r : Rat) : Rat :=
  (2 * l * r) / (l + r)

/-- Universal worst-case relative SR variance `(r - l)^2 / (4 l r)` on `[l, r]`. -/
def maxRelSrVar (l r : Rat) : Rat :=
  ((r - l) * (r - l)) / (4 * l * r)

/-! ### 6. Antithetic Paired SR -/

/-- Exact pairwise covariance `-min(p1 * p2, (1 - p1) * (1 - p2))` of antithetic SR `(u, 1 - u)`. -/
def antiCov (p1 p2 : Rat) : Rat :=
  -minRat (p1 * p2) ((1 - p1) * (1 - p2))

/-- Pair sum variance `Var(e1 + e2)` under antithetic SR `(u, 1 - u)`. -/
def antiPairVar (p1 p2 : Rat) : Rat :=
  p1 * (1 - p1) + p2 * (1 - p2) + 2 * antiCov p1 p2

/-- Pair sum variance `Var(e1 + e2)` under independent SR. -/
def indPairVar (p1 p2 : Rat) : Rat :=
  p1 * (1 - p1) + p2 * (1 - p2)

/-! ### 7. Double-Quantized GEMM Bias & Hammersley Coupling -/

/-- Number of `u ∈ {0, ..., 2^k - 1}` with `u < A` and `pi u < B`. -/
def jointCount (k : Nat) (pi : Nat → Nat) (A B : Nat) : Nat :=
  countRange (2 ^ k) (fun u => decide (u < A ∧ pi u < B))

/-- Exact double-quantized bias `E[1[u < A] 1[pi(u) < B]] - (A/2^k)(B/2^k)`. -/
def doubleQuantBias (k : Nat) (pi : Nat → Nat) (A B : Nat) : Rat :=
  (jointCount k pi A B : Rat) / ((2 ^ k : Nat) : Rat) -
    ((A * B : Nat) : Rat) / (((2 ^ k : Nat) : Rat) * ((2 ^ k : Nat) : Rat))

def samePerm (u : Nat) : Nat := u
def antiPerm (k u : Nat) : Nat := (2 ^ k - 1) - u
def msbXorPerm (k u : Nat) : Nat := u ^^^ 2 ^ (k - 1)
def hammersleyPerm (k u : Nat) : Nat := bitrev k u

/-! ### 8. Split `2m`-Bit Word XOR-VDC Double GEMM -/

def splitLow (m w : Nat) : Nat := w % 2 ^ m
def splitHigh (m w : Nat) : Nat := w / 2 ^ m

/-- Exact expectation of `Q_SR(a; u0_a ^ d_i) * Q_SR(b; u0_b ^ d_j)` over uniform `2m`-bit word `w`. -/
def splitWordXorVdcProdMean (m b i j : Nat) (la ra lb rb : Rat) (pa pb : Nat) : Rat :=
  discreteMean (2 ^ (2 * m)) (fun w =>
    srVal la ra pa (xorVdcLane m b i (splitLow m w)) *
    srVal lb rb pb (xorVdcLane m b j (splitHigh m w)))

/-- Exact intra-block average pairwise covariance of the low `m`-bit half under uniform `2m`-bit word `w`. -/
def splitWordLowSrAvgCov (m b i j : Nat) : Rat :=
  discreteMean (2 ^ m) (fun p1 =>
    discreteMean (2 ^ m) (fun p2 =>
      discreteCov (2 ^ (2 * m))
        (fun w => srErr p1 (2 ^ m) (xorVdcLane m b i (splitLow m w)))
        (fun w => srErr p2 (2 ^ m) (xorVdcLane m b j (splitLow m w)))))

/-- Exact intra-block average pairwise covariance of the high `m`-bit half under uniform `2m`-bit word `w`. -/
def splitWordHighSrAvgCov (m b i j : Nat) : Rat :=
  discreteMean (2 ^ m) (fun p1 =>
    discreteMean (2 ^ m) (fun p2 =>
      discreteCov (2 ^ (2 * m))
        (fun w => srErr p1 (2 ^ m) (xorVdcLane m b i (splitHigh m w)))
        (fun w => srErr p2 (2 ^ m) (xorVdcLane m b j (splitHigh m w)))))

end XorVdcFp4Dither
