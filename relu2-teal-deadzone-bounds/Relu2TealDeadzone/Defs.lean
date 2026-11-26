/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for `relu2-teal-deadzone-bounds`

Pure-`Init` (zero Mathlib) exact rational and natural-number definitions for:
1. Symmetric finite rational distributions, `ReLU` / `ReLU^2` activations, exact kurtosis,
   and `(1 - p)` bulk + `p` `c`-scaled outlier mixtures.
2. Uniform integer quantization (`PRE` vs `POST` squaring) step sizes, zero-underflow
   thresholds, and worst-case error bounds.
3. Floating-point relative-error squaring (`POST` vs `PRE` `4×` MSE inflation).
4. `TEAL` / `CATS` shifted deadzone reclamation for uniform and floating-point quantizers.
5. Quantize-before-prune threshold-tie mask-flip zone vs prune-before-quantize, and
   `uint64_t` bitmask sparse `W4` `down_proj` byte-traffic / speedup crossover.
-/

namespace Relu2TealDeadzone

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if 0 ≤ x then x else -x

/-- Exact rational square `x^2`. -/
def sq (x : Rat) : Rat := x * x

/-- Exact rational fourth power `x^4`. -/
def pow4 (x : Rat) : Rat := sq (sq x)

/-- Exact rational eighth power `x^8`. -/
def pow8 (x : Rat) : Rat := sq (pow4 x)

/-- Exact half-rectified linear unit `ReLU(x) = max(0, x)`. -/
def relu (x : Rat) : Rat :=
  if 0 ≤ x then x else 0

/-- Exact squared rectified linear unit `ReLU^2(x) = (max(0, x))^2`. -/
def relu2 (x : Rat) : Rat :=
  sq (relu x)

/-- Finite sum over `Fin n` in `Rat`. -/
def finSum : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => finSum (fun i : Fin n => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

/-- Paired symmetric finite rational expectation: each index `i` places mass `w i` at `+x i`
    and mass `w i` at `-x i`. -/
def symExpect {n : Nat} (w x : Fin n → Rat) (g : Rat → Rat) : Rat :=
  finSum (fun i => w i * g (x i) + w i * g (-x i))

/-- Exact kurtosis ratio `m4 / m2^2`. -/
def kurtosis (m2 m4 : Rat) : Rat :=
  m4 / sq m2

/-- `(1 - p)` bulk + `p` `c`-scaled outlier mixture expectation of `g` on a symmetric
    finite rational distribution `(w, x)`. -/
def mixSymExpect {n : Nat} (p c : Rat) (w x : Fin n → Rat) (g : Rat → Rat) : Rat :=
  (1 - p) * symExpect w x g + p * symExpect w (fun i => c * x i) g

/-- Uniform `N`-level quantization step on `[0, M]`: `Δ = M / N`. -/
def uniformStep (M N : Rat) : Rat :=
  M / N

/-- Uniform `N`-level `PRE`-square zero-underflow cutoff on `[0, M]`: `M / (2N)`. -/
def preZeroCutoff (M N : Rat) : Rat :=
  M / (2 * N)

/-- Uniform `N`-level `POST`-square squared zero-underflow cutoff on `[0, M^2]`: `M^2 / (2N)`. -/
def postZeroCutoffSq (M N : Rat) : Rat :=
  sq M / (2 * N)

/-- Worst-case `POST`-square absolute error on `x^2` under `N`-level uniform quantization
    on `[0, M^2]`: half a step `M^2 / (2N)`. -/
def postMaxErr (M N : Rat) : Rat :=
  sq M / (2 * N)

/-- Worst-case `PRE`-square absolute error bound on `x^2` when `|û - x| ≤ M / (2N)`:
    `(M * x) / N + M^2 / (4 * N^2)`. -/
def preMaxErr (M N x : Rat) : Rat :=
  (M * x) / N + sq M / (4 * sq N)

/-- Shifted deadzone-reclaimed uniform step size on `[τ, M]` with `N` levels: `(M - τ) / N`. -/
def shiftedStep (M tau N : Rat) : Rat :=
  (M - tau) / N

/-- Standard uniform worst-case half-step error on `[0, M]` with `N` levels: `M / (2N)`. -/
def stdHalfStep (M N : Rat) : Rat :=
  M / (2 * N)

/-- Shifted deadzone-reclaimed worst-case half-step error on `[τ, M]` with `N` levels:
    `(M - τ) / (2N)`. -/
def shiftedHalfStep (M tau N : Rat) : Rat :=
  (M - tau) / (2 * N)

/-- Exact sign-preserving shifted deadzone reconstruction `sign(x) * (τ + q)`. -/
def tealShiftedRecon (tau x q : Rat) : Rat :=
  if 0 ≤ x then tau + q else -(tau + q)

/-- Floating-point local step width at magnitude `y` with relative unit spacing `u`: `u * y`. -/
def fpLocalStep (u y : Rat) : Rat :=
  u * y

/-- Magnitude pruning mask: `true` iff `τ ≤ x`. -/
def pruneMask (tau x : Rat) : Bool :=
  decide (tau ≤ x)

/-- Nearest-grid-point rounding on a uniform grid of step `Δ` within `[g, g + Δ)`:
    rounds down to `g` if `x < g + Δ / 2`, and up to `g + Δ` otherwise. -/
def uniformGridRound (delta g x : Rat) : Rat :=
  if x < g + delta / 2 then g else g + delta

/-- Sparse-to-dense byte-traffic ratio under sparsity `s` and relative bitmask/decode overhead `ov`:
    `(1 - s) * (1 + ov)`. -/
def sparseTrafficRatio (s ov : Rat) : Rat :=
  (1 - s) * (1 + ov)

/-- Sparse-over-dense speedup under sparsity `s` and relative overhead `ov`:
    `1 / ((1 - s) * (1 + ov))`. -/
def sparseSpeedup (s ov : Rat) : Rat :=
  1 / sparseTrafficRatio s ov

/-- Exact break-even sparsity crossover threshold `s* = 1 - 1 / (1 + ov)`. -/
def sparsityCrossover (ov : Rat) : Rat :=
  1 - 1 / (1 + ov)

end Relu2TealDeadzone
