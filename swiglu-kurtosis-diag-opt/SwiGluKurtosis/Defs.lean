/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Core Pure-`Init` Definitions (`swiglu-kurtosis-diag-opt`)

All definitions live purely in Lean 4's `Init` prelude over `Rat` and `Nat`
(zero Mathlib, zero floating-point approximations, zero `native_decide`).
-/

namespace SwiGluKurtosis

/-! ### Finite Sums, Absolute Value, and Dyadic Powers -/

def finSumAux : (k : Nat) → (Fin k → Rat) → Rat
  | 0, _ => 0
  | k + 1, f => finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) + f ⟨k, Nat.lt_succ_self k⟩

def finSum {n : Nat} (f : Fin n → Rat) : Rat :=
  finSumAux n f

def ratAbs (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then x else -x

def pow2Rat (k : Nat) : Rat :=
  ((2 ^ k : Nat) : Rat)

def invPow2Rat (k : Nat) : Rat :=
  (1 : Rat) / pow2Rat k

def sq (x : Rat) : Rat := x * x

def pow4 (x : Rat) : Rat := sq (sq x)

def pow6 (x : Rat) : Rat := sq x * pow4 x

def pow8 (x : Rat) : Rat := sq (pow4 x)

/-! ### Pillar 1: Symmetric Discrete Rational Distributions & Gated-Bilinear Kurtosis -/

/-- Exact `ReLU(x) = max(0, x)` over `Rat`. -/
def relu (x : Rat) : Rat :=
  if (0 : Rat) ≤ x then x else 0

/-- A symmetric finite discrete rational distribution supported on `2 * n` nonzero atoms
    `± val i` (`val i > 0`), each occurring with probability `prob i ≥ 0` where
    `∑ i, prob i = 1 / 2`. Hence `P(X > 0) = P(X < 0) = 1 / 2`, `P(X = 0) = 0`,
    and total probability mass is `1`. -/
structure SymHalfDist (n : Nat) where
  val : Fin n → Rat
  prob : Fin n → Rat
  val_pos : ∀ i, (0 : Rat) < val i
  prob_nonneg : ∀ i, (0 : Rat) ≤ prob i
  sum_prob : finSum prob = 1 / 2

/-- Expectation `E[f(X)]` under a symmetric distribution `D`. -/
def symExpect {n : Nat} (D : SymHalfDist n) (f : Rat → Rat) : Rat :=
  finSum (fun i => D.prob i * f (D.val i) + D.prob i * f (-D.val i))

/-- Joint expectation `E[h(G, U)]` for independent symmetric distributions `G` and `U`. -/
def prodSymExpect {n m : Nat} (G : SymHalfDist n) (U : SymHalfDist m) (h : Rat → Rat → Rat) : Rat :=
  symExpect G (fun g => symExpect U (fun u => h g u))

/-- Raw even moments `M_{2k} = E[X^{2k}]`. -/
def symMoment2 {n : Nat} (D : SymHalfDist n) : Rat := symExpect D sq
def symMoment4 {n : Nat} (D : SymHalfDist n) : Rat := symExpect D pow4
def symMoment6 {n : Nat} (D : SymHalfDist n) : Rat := symExpect D pow6
def symMoment8 {n : Nat} (D : SymHalfDist n) : Rat := symExpect D pow8

/-- Raw 4th-to-2nd moment kurtosis ratio `E[Y^4] / (E[Y^2])^2`. -/
def rawKurtosis (m2 m4 : Rat) : Rat := m4 / sq m2

/-- Kurtosis of a symmetric (hence zero-mean) distribution `D`. -/
def symKurtosis {n : Nat} (D : SymHalfDist n) : Rat :=
  rawKurtosis (symMoment2 D) (symMoment4 D)

/-- Raw kurtosis of independent bilinear product `G * U`. -/
def bilinearRawKurt {n m : Nat} (G : SymHalfDist n) (U : SymHalfDist m) : Rat :=
  rawKurtosis
    (prodSymExpect G U (fun g u => sq (g * u)))
    (prodSymExpect G U (fun g u => pow4 (g * u)))

/-- Raw kurtosis of independent ReGLU product `ReLU(G) * U`. -/
def regluIndepRawKurt {n m : Nat} (G : SymHalfDist n) (U : SymHalfDist m) : Rat :=
  rawKurtosis
    (prodSymExpect G U (fun g u => sq (relu g * u)))
    (prodSymExpect G U (fun g u => pow4 (relu g * u)))

/-- Raw kurtosis of identically correlated ReGLU product `ReLU(G) * G`. -/
def regluSelfRawKurt {n : Nat} (G : SymHalfDist n) : Rat :=
  rawKurtosis
    (symExpect G (fun g => sq (relu g * g)))
    (symExpect G (fun g => pow4 (relu g * g)))

/-- Raw kurtosis of linearly correlated ReGLU product `ReLU(G) * (a * G + b * Z)`
    for independent identically distributed `G, Z ~ D`. -/
def regluCorrMixRawKurt {n : Nat} (D : SymHalfDist n) (a b : Rat) : Rat :=
  rawKurtosis
    (prodSymExpect D D (fun g z => sq (relu g * (a * g + b * z))))
    (prodSymExpect D D (fun g z => pow4 (relu g * (a * g + b * z))))

/-- Exact closed-form Gaussian-moment (`M2=1, M4=3, M6=15, M8=105`) correlated ReGLU
    raw kurtosis as a function of squared correlation `t = ρ^2 ∈ [0, 1]` (`a^2 = t, b^2 = 1 - t`). -/
def gaussCorrReGLUKurt (t : Rat) : Rat :=
  2 * (105 * (t * t) + 90 * t * (1 - t) + 9 * ((1 - t) * (1 - t))) /
    sq (3 * t + (1 - t))

private theorem def_inv_nonneg {c : Rat} (hc : (0 : Rat) < c) : (0 : Rat) ≤ c⁻¹ := by
  have hne : c ≠ 0 := Rat.ne_of_gt hc
  have h1 : (0 : Rat) < c⁻¹ * c := by
    rw [Rat.inv_mul_cancel c hne]; decide
  cases Rat.le_total (a := (0 : Rat)) (b := c⁻¹) with
  | inl hle => exact hle
  | inr hge =>
    have h0 : (0 : Rat) ≤ (-c⁻¹) * c := by
      have hn : (0 : Rat) ≤ -c⁻¹ := by
        have := (Rat.add_le_add_right (c := -c⁻¹)).mpr hge
        grind
      exact Rat.mul_nonneg hn (Rat.le_of_lt hc)
    have hneg : c⁻¹ * c ≤ 0 := by
      have := (Rat.add_le_add_right (c := c⁻¹ * c)).mpr h0
      grind
    exact False.elim (Rat.not_le.mpr h1 hneg)

private theorem def_div_nonneg {a b : Rat} (ha : (0 : Rat) ≤ a) (hb : (0 : Rat) < b) :
    (0 : Rat) ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (def_inv_nonneg hb)

/-- Exact 3-point symmetric rational distribution matching Gaussian kurtosis `3`
    (`val = (1, 2, 4)`, half-probs `(31/90, 10/90, 4/90)`, `M2 = 3`, `M4 = 27`). -/
def gaussMoment3Dist : SymHalfDist 3 where
  val := fun i => if i.val = 0 then 1 else if i.val = 1 then 2 else 4
  prob := fun i => if i.val = 0 then 31 / 90 else if i.val = 1 then 10 / 90 else 4 / 90
  val_pos := by intro ⟨v, hv⟩; match v with | 0 => simp; decide | 1 => simp; decide | 2 => simp; decide | _ + 3 => omega
  prob_nonneg := by
    intro ⟨v, hv⟩
    match v with
    | 0 => simp; exact def_div_nonneg (by decide) (by decide)
    | 1 => simp; exact def_div_nonneg (by decide) (by decide)
    | 2 => simp; exact def_div_nonneg (by decide) (by decide)
    | _ + 3 => omega
  sum_prob := by simp [finSum, finSumAux]; grind

/-- Exact 3-point symmetric rational distribution matching Laplace kurtosis `6`
    (`val = (1, 2, 5)`, half-probs `(77/168, 4/168, 3/168)`, `M2 = 2`, `M4 = 24`). -/
def laplaceMoment3Dist : SymHalfDist 3 where
  val := fun i => if i.val = 0 then 1 else if i.val = 1 then 2 else 5
  prob := fun i => if i.val = 0 then 77 / 168 else if i.val = 1 then 4 / 168 else 3 / 168
  val_pos := by intro ⟨v, hv⟩; match v with | 0 => simp; decide | 1 => simp; decide | 2 => simp; decide | _ + 3 => omega
  prob_nonneg := by
    intro ⟨v, hv⟩
    match v with
    | 0 => simp; exact def_div_nonneg (by decide) (by decide)
    | 1 => simp; exact def_div_nonneg (by decide) (by decide)
    | 2 => simp; exact def_div_nonneg (by decide) (by decide)
    | _ + 3 => omega
  sum_prob := by simp [finSum, finSumAux]; grind

/-- Exact 3-point symmetric heavy-tail rational distribution (`val = (1, 2, 4)`,
    half-probs `(5/16, 5/32, 1/32)`) witnessing strict correlated kurtosis amplification
    `regluSelfRawKurt > regluIndepRawKurt`. -/
def heavyTail3Dist : SymHalfDist 3 where
  val := fun i => if i.val = 0 then 1 else if i.val = 1 then 2 else 4
  prob := fun i => if i.val = 0 then 5 / 16 else if i.val = 1 then 5 / 32 else 1 / 32
  val_pos := by intro ⟨v, hv⟩; match v with | 0 => simp; decide | 1 => simp; decide | 2 => simp; decide | _ + 3 => omega
  prob_nonneg := by
    intro ⟨v, hv⟩
    match v with
    | 0 => simp; exact def_div_nonneg (by decide) (by decide)
    | 1 => simp; exact def_div_nonneg (by decide) (by decide)
    | 2 => simp; exact def_div_nonneg (by decide) (by decide)
    | _ + 3 => omega
  sum_prob := by simp [finSum, finSumAux]; grind

/-! ### Pillar 3: Zero-FLOP SwiGLU Diagonal Equivalence & AM-GM Optimal Scale -/

/-- Exact rational matrix-vector product `(W v)_i = ∑_j W_{ij} v_j`. -/
def matVec {r c : Nat} (W : Fin r → Fin c → Rat) (v : Fin c → Rat) (i : Fin r) : Rat :=
  finSum (fun j => W i j * v j)

/-- Elementwise Hadamard product `(a ⊙ b)_j = a_j * b_j`. -/
def hadamard {m : Nat} (a b : Fin m → Rat) (j : Fin m) : Rat :=
  a j * b j

/-- General gated FFN output `W_down (φ(g) ⊙ u)` for arbitrary gate nonlinearity `φ`
    (`SiLU`, `GELU`, `ReLU`, etc.). -/
def gatedFFN {d_out m : Nat} (φ : Rat → Rat) (W_down : Fin d_out → Fin m → Rat)
    (g u : Fin m → Rat) : Fin d_out → Rat :=
  matVec W_down (hadamard (fun j => φ (g j)) u)

/-- Row-scaled up-projection weight matrix `(S W_up)_{jk} = s_j * (W_up)_{jk}`. -/
def scaleRows {m d_in : Nat} (s : Fin m → Rat) (W_up : Fin m → Fin d_in → Rat) :
    Fin m → Fin d_in → Rat :=
  fun j k => s j * W_up j k

/-- Inverse-column-scaled down-projection weight matrix `(W_down S^{-1})_{ij} = (W_down)_{ij} / s_j`. -/
def invScaleCols {d_out m : Nat} (s : Fin m → Rat) (W_down : Fin d_out → Fin m → Rat) :
    Fin d_out → Fin m → Rat :=
  fun i j => W_down i j / s j

/-- Joint activation-weight quantization MSE for a channel with outlier ratio `K`,
    quantization noise floors `(εa, εw)`, and diagonal down-scale `λ > 0`:
    `E(λ) = εa (K / λ)^2 + εw λ^2`. -/
def diagQuantMSE (εa εw K lam : Rat) : Rat :=
  εa * sq (K / lam) + εw * sq lam

/-! ### Pillar 2: Gate-Up-Down First-Order Sensitivity & Asymmetric Bit Allocation -/

/-- First-order quantized gated-FFN MSE under bit triple `(bg, bu, bd)` where
    `b`-bit uniform quantization noise scales as `4^{-b} = 2^{-2b}`:
    `MSE = S_gate * 4^{-bg} + S_up * 4^{-bu} + S_down * 4^{-bd}`. -/
def bitAllocMSE (Sg Su Sd : Rat) (bg bu bd : Nat) : Rat :=
  Sg * invPow2Rat (2 * bg) + Su * invPow2Rat (2 * bu) + Sd * invPow2Rat (2 * bd)

/-! ### Pillar 1 (Hardware): MXFP4 (`B=32, E8M0`) vs NVFP4 (`B=16`) Underflow -/

/-- Maximum representable positive magnitude of FP4 `E2M1` (`6.0`). -/
def maxE2M1 : Rat := 6

/-- Smallest positive (subnormal) magnitude of FP4 `E2M1` (`0.5`). -/
def minSubE2M1 : Rat := 1 / 2

/-- Round-to-nearest midpoint between `0` and `minSubE2M1 = 1/2` (`1/4`). -/
def underflowMidE2M1 : Rat := 1 / 4

/-- A block scale `s > 0` validly covers block maximum `M` in FP4 `E2M1` iff `M ≤ 6 * s`. -/
def validE2M1Scale (s M : Rat) : Prop :=
  (0 : Rat) < s ∧ M ≤ s * maxE2M1

/-- An entry `x` flushes to exact zero under FP4 `E2M1` block scale `s > 0` iff `|x| < s / 4`. -/
def fp4Underflows (s x : Rat) : Prop :=
  ratAbs x < s * underflowMidE2M1

/-- An entry `x` is preserved nonzero under FP4 `E2M1` block scale `s > 0` iff `|x| ≥ s / 4`. -/
def fp4PreservedNonzero (s x : Rat) : Prop :=
  s * underflowMidE2M1 ≤ ratAbs x

/-- Lower 16-element NVFP4 sub-block of a 32-element MXFP4 block. -/
def lowerHalf16 (v : Fin 32 → Rat) (k : Fin 16) : Rat :=
  v ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩

/-- Upper 16-element NVFP4 sub-block of a 32-element MXFP4 block. -/
def upperHalf16 (v : Fin 32 → Rat) (k : Fin 16) : Rat :=
  v ⟨k.val + 16, Nat.add_lt_add_right k.isLt 16⟩

/-- Clean 16-element NVFP4 sub-block (the half not containing outlier index `idx`). -/
def cleanHalf16 (v : Fin 32 → Rat) (idx : Fin 32) : Fin 16 → Rat :=
  if idx.val < 16 then upperHalf16 v else lowerHalf16 v

end SwiGluKurtosis
