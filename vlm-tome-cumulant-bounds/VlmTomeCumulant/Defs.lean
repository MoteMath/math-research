/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Definitions for `vlm-tome-cumulant-bounds`

Pure-`Init` (zero Mathlib) exact rational, integer, and natural-number definitions for:
- Pillar 1: Unweighted merge TV distortion, proportional-attention (`+ln s`) invariance,
  within-cluster dispersion Jensen underweighting, and Cumulant-2 (`+ln s + σ²/2`) bonus.
- Pillar 2: Recursive orthogonal Walsh-Hadamard transform `H_{2^k}`, channel-outlier
  flattening, and 1-bit SimHash / Walsh-code Hamming distance.
- Pillar 3: Multi-layer Vision Transformer (ViT) token-merging schedules, quadratic
  attention & full ViT FLOPs, and compounding representation drift.
-/

namespace VlmTomeCumulant

/-! ### Basic Rational, Integer, and Natural-Number Helpers -/

/-- Exact rational absolute value. -/
def ratAbs (x : Rat) : Rat :=
  if 0 ≤ x then x else -x

/-- Finite sum over `Fin k` in `Rat` via structural recursion. -/
def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f =>
    finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Finite sum over `Fin n` in `Rat`. -/
def finSum {n : Nat} (f : Fin n → Rat) : Rat :=
  finSumAux n f

/-- Finite sum over `Fin k` in `Int` via structural recursion. -/
def finSumIntAux : (k : Nat) → (Fin k → Int) → Int
  | 0, _ => 0
  | k + 1, f =>
    finSumIntAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Finite sum over `Fin n` in `Int`. -/
def finSumInt {n : Nat} (f : Fin n → Int) : Int :=
  finSumIntAux n f

/-- Finite sum over `Fin k` in `Nat` via structural recursion. -/
def finSumNatAux : (k : Nat) → (Fin k → Nat) → Nat
  | 0, _ => 0
  | k + 1, f =>
    finSumNatAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

/-- Finite sum over `Fin n` in `Nat`. -/
def finSumNat {n : Nat} (f : Fin n → Nat) : Nat :=
  finSumNatAux n f

/-! ### Pillar 1: Proportional Attention, Unweighted TV Distortion, and Cumulant-2 Bonus -/

/-- Pre-merge cluster attention probability when `s` identical tokens each have weight `w`
    and all non-cluster tokens have total weight `W`. -/
def origClusterProb (s : Nat) (w W : Rat) : Rat :=
  (s : Rat) * w / ((s : Rat) * w + W)

/-- Post-unweighted-merge cluster attention probability (without the `+ln s` factor `s`). -/
def unwClusterProb (w W : Rat) : Rat :=
  w / (w + W)

/-- Exact Total Variation distortion of unweighted merging as a function of cluster size `s`
    and post-unweighted-merge cluster probability `p'`. -/
def tvUnweighted (s : Nat) (p' : Rat) : Rat :=
  ((s : Rat) - 1) * p' * (1 - p') / (1 + ((s : Rat) - 1) * p')

/-- Rational-parameterized TV distortion `(S - 1) p' (1 - p') / (1 + (S - 1) p')`. -/
def tvUnweightedRat (S p' : Rat) : Rat :=
  (S - 1) * p' * (1 - p') / (1 + (S - 1) * p')

/-- Exact ceiling function `(r - 1) / (r + 1)` evaluated at `r = √s`. -/
def tvCeilingOfSqrt (r : Rat) : Rat :=
  (r - 1) / (r + 1)

/-- Pre-merge softmax partition sum for `s` identical-weight cluster tokens (`w`)
    and `m` non-cluster tokens (`u`). -/
def origPartition (s : Nat) {m : Nat} (w : Rat) (u : Fin m → Rat) : Rat :=
  finSum (fun _ : Fin s => w) + finSum u

/-- Proportional-attention (`+ln s`) merged partition sum `s * w + ∑ u_i`. -/
def propPartition (s : Nat) {m : Nat} (w : Rat) (u : Fin m → Rat) : Rat :=
  (s : Rat) * w + finSum u

/-- Exact arithmetic mean of `s` cluster values. -/
def meanVal {s : Nat} (v : Fin s → Rat) : Rat :=
  finSum v / (s : Rat)

/-- Pre-merge Value-weighted attention output. -/
def origAttnOutput {s m : Nat} (w : Rat) (vCl : Fin s → Rat) (u vOut : Fin m → Rat) : Rat :=
  (finSum (fun j => w * vCl j) + finSum (fun i => u i * vOut i)) / origPartition s w u

/-- Proportional-attention (`+ln s`) Value-weighted attention output using exact mean cluster value. -/
def propAttnOutput (s : Nat) {m : Nat} (w : Rat) (vCl : Fin s → Rat) (u vOut : Fin m → Rat) : Rat :=
  (((s : Rat) * w) * meanVal vCl + finSum (fun i => u i * vOut i)) / propPartition s w u

/-- Collapsed `(m + 1)`-way Total Variation distance between two distributions
    `(pCl1, p1)` and `(pCl2, p2)`. -/
def collapsedTV {m : Nat} (pCl1 pCl2 : Rat) (p1 p2 : Fin m → Rat) : Rat :=
  (ratAbs (pCl1 - pCl2) + finSum (fun i => ratAbs (p1 i - p2 i))) / 2

/-- Within-cluster logit variance `σ² = (1 / s) ∑ η_j²`. -/
def clusterVar {s : Nat} (η : Fin s → Rat) : Rat :=
  finSum (fun j => η j * η j) / (s : Rat)

/-- Within-cluster 3rd central moment `μ_3 = (1 / s) ∑ η_j³`. -/
def clusterMoment3 {s : Nat} (η : Fin s → Rat) : Rat :=
  finSum (fun j => η j * η j * η j) / (s : Rat)

/-- Within-cluster 4th central moment `μ_4 = (1 / s) ∑ η_j⁴`. -/
def clusterMoment4 {s : Nat} (η : Fin s → Rat) : Rat :=
  finSum (fun j => η j * η j * η j * η j) / (s : Rat)

/-- 2nd-order exponential Taylor polynomial `1 + x + x²/2`. -/
def expTaylor2 (x : Rat) : Rat :=
  1 + x + x * x / 2

/-- 3rd-order exponential Taylor polynomial `1 + x + x²/2 + x³/6`. -/
def expTaylor3 (x : Rat) : Rat :=
  1 + x + x * x / 2 + x * x * x / 6

/-- 4th-order exponential Taylor polynomial `1 + x + x²/2 + x³/6 + x⁴/24`. -/
def expTaylor4 (x : Rat) : Rat :=
  1 + x + x * x / 2 + x * x * x / 6 + x * x * x * x / 24

/-- First-order Cumulant-2 multiplicative weight factor `1 + σ²/2` (from `+σ²/2` logit bonus). -/
def cumulant2Factor1 (σ2 : Rat) : Rat :=
  1 + σ2 / 2

/-- Second-order Cumulant-2 multiplicative weight factor `1 + σ²/2 + (σ²/2)²/2`. -/
def cumulant2Factor2 (σ2 : Rat) : Rat :=
  expTaylor2 (σ2 / 2)

/-! ### Pillar 2: Orthogonal Walsh-Hadamard Transform (`H_{2^k}`) and 1-Bit SimHash -/

/-- Exact integer inner product on `Fin n → Int`. -/
def dotInt {n : Nat} (u v : Fin n → Int) : Int :=
  finSumInt (fun i => u i * v i)

/-- Exact integer squared `L_2` norm on `Fin n → Int`. -/
def normSqInt {n : Nat} (v : Fin n → Int) : Int :=
  dotInt v v

/-- Recursive Sylvester Walsh-Hadamard transform `H_{2^k}` on `Fin (2^k) → Int`.
    Satisfies `H_{2^k}^T H_{2^k} = 2^k I_{2^k}` identically for all `k : Nat`. -/
def wht : (k : Nat) → (Fin (2 ^ k) → Int) → (Fin (2 ^ k) → Int)
  | 0, v => v
  | k + 1, v =>
    let vL : Fin (2 ^ k) → Int := fun i =>
      v ⟨i.val, by
        have h : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
        have hi := i.isLt
        omega⟩
    let vR : Fin (2 ^ k) → Int := fun i =>
      v ⟨i.val + 2 ^ k, by
        have h : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
        have hi := i.isLt
        omega⟩
    let a := wht k vL
    let b := wht k vR
    fun i =>
      if h : i.val < 2 ^ k then
        a ⟨i.val, h⟩ + b ⟨i.val, h⟩
      else
        have hlt : i.val - 2 ^ k < 2 ^ k := by
          have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
          have := i.isLt
          omega
        a ⟨i.val - 2 ^ k, hlt⟩ - b ⟨i.val - 2 ^ k, hlt⟩

/-- Canonical basis vector `e_j` in `Int^{2^k}`. -/
def basisVec (k : Nat) (j : Fin (2 ^ k)) : Fin (2 ^ k) → Int :=
  fun i => if i.val = j.val then 1 else 0

/-- 1-sparse channel outlier vector `M * e_0` in `Int^{2^k}`. -/
def outlierVec (k : Nat) (M : Int) : Fin (2 ^ k) → Int :=
  fun i => if i.val = 0 then M else 0

/-- Channel-outlier plus signal vector `M * e_0 + a * e_1` in `Int^{2^k}` (`k ≥ 1`). -/
def outlierSignalVec (k : Nat) (M a : Int) : Fin (2 ^ k) → Int :=
  fun i => if i.val = 0 then M else if i.val = 1 then a else 0

/-- 1-bit SimHash sign encoding (`true` for `x ≥ 0`, `false` for `x < 0`). -/
def signBit (x : Int) : Bool :=
  decide (0 ≤ x)

/-- Coordinatewise 1-bit SimHash vector. -/
def simHash {n : Nat} (v : Fin n → Int) : Fin n → Bool :=
  fun i => signBit (v i)

/-- Exact Hamming distance between two binary SimHash codes. -/
def hammingDist {n : Nat} (a b : Fin n → Bool) : Nat :=
  finSumNat (fun i => if a i = b i then 0 else 1)

/-! ### Pillar 3: Multi-Layer ViT Merging Schedules, FLOPs, and Compounding Drift -/

/-- Cumulative merges through layer `k`: `P_k(r) = ∑_{l ≤ k} r_l`. -/
def prefixSum {L : Nat} (r : Fin L → Nat) (k : Nat) : Nat :=
  finSumNat (fun l : Fin L => if l.val ≤ k then r l else 0)

/-- Remaining tokens at layer `l` after applying merges `r_0, ..., r_l`. -/
def remTokens (N0 : Nat) {L : Nat} (r : Fin L → Nat) (l : Fin L) : Nat :=
  N0 - prefixSum r l.val

/-- Total quadratic attention FLOPs `∑_{l=0}^{L-1} N_l²`. -/
def attnFlops (N0 : Nat) {L : Nat} (r : Fin L → Nat) : Nat :=
  finSumNat (fun l => remTokens N0 r l * remTokens N0 r l)

/-- Total ViT FLOPs `∑_{l=0}^{L-1} (N_l² + c * N_l)` (e.g. `c = 6144` for ViT-L/14). -/
def vitFlops (N0 c : Nat) {L : Nat} (r : Fin L → Nat) : Nat :=
  finSumNat (fun l => remTokens N0 r l * remTokens N0 r l + c * remTokens N0 r l)

/-- Total compounding representation drift `∑_{l=0}^{L-1} w_l * r_l`. -/
def scheduleDrift {L : Nat} (w : Fin L → Rat) (r : Fin L → Nat) : Rat :=
  finSum (fun l => w l * (r l : Rat))

/-- Schedule obtained by shifting `Δ` merges from later layer `j` to earlier layer `i`. -/
def shiftSchedule {L : Nat} (r : Fin L → Nat) (i j : Fin L) (Δ : Nat) : Fin L → Nat :=
  fun l => if l = i then r l + Δ else if l = j then r l - Δ else r l

end VlmTomeCumulant
