/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Shared Pure-`Init` Definitions (`bitnet-contraction-hierarchy`)

All public definitions shared between `Challenge.lean` and `Solution.lean`.
Pure Lean 4 `Init` only — zero Mathlib dependencies.
-/

namespace BitnetContraction

/-- Finite sum of a `Rat`-valued function over `Fin n`. -/
def sumRat : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | _ + 1, f => sumRat (fun i => f i.castSucc) + f ⟨_, Nat.lt_succ_self _⟩

/-- Squared Euclidean norm `‖x‖_2^2 = ∑_i x_i^2` over `Rat`. -/
def normSq {d : Nat} (x : Fin d → Rat) : Rat :=
  sumRat (fun i => x i * x i)

/-- `ℓ_1` norm `‖x‖_1 = ∑_i |x_i|` over `Rat`. -/
def l1Norm {d : Nat} (x : Fin d → Rat) : Rat :=
  sumRat (fun i => (x i).abs)

/-- Nearest-neighbor ternary rounding with scale `γ` (non-strict `≥` tie-break):
    maps `x` to `γ` if `x ≥ γ / 2`, to `-γ` if `x ≤ -(γ / 2)`, and to `0` otherwise. -/
def ternRound (γ x : Rat) : Rat :=
  if γ / 2 ≤ x then γ
  else if x ≤ -(γ / 2) then -γ
  else 0

/-- Nearest-neighbor ternary rounding with scale `γ` (strict `>` tie-break):
    maps `x` to `γ` if `x > γ / 2`, to `-γ` if `x < -(γ / 2)`, and to `0` otherwise. -/
def ternRoundStrict (γ x : Rat) : Rat :=
  if γ / 2 < x then γ
  else if x < -(γ / 2) then -γ
  else 0

/-- Squared quantization error `∑_i (x_i - ternRound γ (x_i))^2`. -/
def ternErrSq {d : Nat} (γ : Rat) (x : Fin d → Rat) : Rat :=
  sumRat (fun i => (x i - ternRound γ (x i)) * (x i - ternRound γ (x i)))

/-- Squared quantization error under strict tie-breaking `ternRoundStrict`. -/
def ternErrSqStrict {d : Nat} (γ : Rat) (x : Fin d → Rat) : Rat :=
  sumRat (fun i => (x i - ternRoundStrict γ (x i)) * (x i - ternRoundStrict γ (x i)))

/-- EF21 contraction factor `α(x; γ) = 1 - ‖x - Q_γ(x)‖_2^2 / ‖x‖_2^2`. -/
def ternAlpha {d : Nat} (γ : Rat) (x : Fin d → Rat) : Rat :=
  1 - ternErrSq γ x / normSq x

/-- EF21 contraction factor under strict tie-breaking `ternRoundStrict`. -/
def ternAlphaStrict {d : Nat} (γ : Rat) (x : Fin d → Rat) : Rat :=
  1 - ternErrSqStrict γ x / normSq x

/-- First standard basis vector `e_0 = (1, 0, ..., 0)` in `Rat^d`. -/
def unitE0 (d : Nat) : Fin d → Rat :=
  fun i => if i.val = 0 then 1 else 0

/-- AbsMax extremal vector `(1, 1/2, ..., 1/2)` in `Rat^d`. -/
def absMaxWitness (d : Nat) : Fin d → Rat :=
  fun i => if i.val = 0 then 1 else (1 : Rat) / 2

/-- AbsMax/2 extremal vector `(1, 1/4, ..., 1/4)` in `Rat^d`. -/
def absMaxHalfWitness (d : Nat) : Fin d → Rat :=
  fun i => if i.val = 0 then 1 else (1 : Rat) / 4

/-- Rational RMS extremal vector `(s/2, 1/2, ..., 1/2)` in `Rat^d` (exact when `s^2 = 3d + 1`). -/
def rmsWitness (d s : Nat) : Fin d → Rat :=
  fun i => if i.val = 0 then (s : Rat) / 2 else (1 : Rat) / 2

/-! ## Frontier 2: Multi-Level Codebooks & Critical Phase-Transition Dimension -/

/-- Critical phase-transition dimension `d_crit(G_M) = 8 M^2 + 4` for the symmetric
    integer grid `G_M = {0, ±1, ..., ±M}`. -/
def dCrit (M : Nat) : Nat :=
  8 * M * M + 4

/-- Auxiliary accumulator for the Codebook Harmonic Constant
    `H(G) = ∑_{j=1}^L (g_j - g_{j-1}) / (g_j + g_{j-1})` starting from `prev = g_0 = 0`. -/
def harmonicConstAux (prev : Nat) : List Nat → Rat
  | [] => 0
  | g :: gs =>
      (((g : Int) - (prev : Int) : Int) : Rat) / (((g : Int) + (prev : Int) : Int) : Rat) +
        harmonicConstAux g gs

/-- Codebook Harmonic Constant `H(G)` for positive grid levels `[g_1, ..., g_L]` (with `g_0 = 0`). -/
def harmonicConst (levels : List Nat) : Rat :=
  harmonicConstAux 0 levels

/-! ## Frontier 3: 2-Stage Residual Ternary Quantization (Greedy vs Joint Disjoint) -/

/-- Exact integer insertion-sort in descending order. -/
def insertDesc (v : Int) : List Int → List Int
  | [] => [v]
  | h :: t => if h ≤ v then v :: h :: t else h :: insertDesc v t

/-- Sort a list of integers in descending order. -/
def sortDesc : List Int → List Int
  | [] => []
  | h :: t => insertDesc h (sortDesc t)

/-- Prefix sums `[0, x_0, x_0 + x_1, ...]`. -/
def prefixSumsAux (acc : Int) : List Int → List Int
  | [] => [acc]
  | h :: t => acc :: prefixSumsAux (acc + h) t

def prefixSums (xs : List Int) : List Int :=
  prefixSumsAux 0 xs

/-- Best prefix length `k ∈ {1, ..., d}` maximizing `(∑_{i<k} x_i)^2 / k` for a descending
    non-negative integer vector `xs`, returning `(best_k, best_sum_sq)`. -/
def bestPrefixLoop (prefs : List Int) (k : Nat) (bestK : Nat) (bestSq : Int) : Nat × Int :=
  match prefs with
  | [] => (bestK, bestSq)
  | s :: rest =>
      let sSq := s * s
      if sSq * (bestK : Int) > bestSq * (k : Int) then
        bestPrefixLoop rest (k + 1) k sSq
      else
        bestPrefixLoop rest (k + 1) bestK bestSq

def bestPrefix (xsDesc : List Int) : Nat × Int :=
  match xsDesc with
  | [] => (1, 0)
  | h :: t =>
      let ps := prefixSumsAux h t
      match ps with
      | [] => (1, 0)
      | s1 :: rest => bestPrefixLoop rest 2 1 (s1 * s1)

/-- Squared norm of an integer list `∑ x_i^2`. -/
def normSqList : List Int → Int
  | [] => 0
  | h :: t => h * h + normSqList t

/-- Exact integer `(num, den)` pair for Greedy 2-stage residual ternary contraction. -/
def greedyTwoStageNumDen (xs : List Int) : Int × Int :=
  let xd := sortDesc xs
  let n2 := normSqList xd
  if n2 == 0 then (1, 1)
  else
    let (k1, s1Sq) := bestPrefix xd
    let ps := prefixSums xd
    let s1 := ps.getD k1 0
    let resAbs :=
      (xd.zipIdx).map (fun (v, idx) =>
        let r := (k1 : Int) * v - (if idx < k1 then s1 else 0)
        if r < 0 then -r else r)
    let rDesc := sortDesc resAbs
    let (k2, r2Sq) := bestPrefix rDesc
    let num : Int := s1Sq * (k1 : Int) * (k2 : Int) + r2Sq
    let den : Int := (k1 : Int) * (k1 : Int) * (k2 : Int) * n2
    (num, den)

/-- Exact Greedy 2-stage residual ternary contraction factor `α_greedy(x)` on a non-negative
    integer vector `x` (matching `cpu_eval_twostage(..., mode=0)` bit-for-bit). -/
def greedyTwoStageAlpha (xs : List Int) : Rat :=
  let p := greedyTwoStageNumDen xs
  (p.1 : Rat) / (p.2 : Rat)

/-- Inner loop for Joint Disjoint 2-stage ternary over `k2 ∈ {k1 + 1, ..., d}`. -/
def jointDisjointInner (k1 : Nat) (s1 s1Sq : Int) (k2 : Nat) (remPrefs : List Int)
    (bestN bestD : Int) : Int × Int :=
  match remPrefs with
  | [] => (bestN, bestD)
  | p2 :: rest =>
      let len2 : Int := ((k2 - k1 : Nat) : Int)
      let s2 : Int := p2 - s1
      let nCur : Int := s1Sq * len2 + s2 * s2 * (k1 : Int)
      let dCur : Int := (k1 : Int) * len2
      let (bn, bd) :=
        if nCur * bestD > bestN * dCur then (nCur, dCur) else (bestN, bestD)
      jointDisjointInner k1 s1 s1Sq (k2 + 1) rest bn bd

/-- Outer loop for Joint Disjoint 2-stage ternary over `k1 ∈ {1, ..., d}`. -/
def jointDisjointOuter (k1 : Nat) (remPrefs : List Int) (bestN bestD : Int) : Int × Int :=
  match remPrefs with
  | [] => (bestN, bestD)
  | s1 :: rest =>
      let s1Sq : Int := s1 * s1
      let (bn0, bd0) :=
        if s1Sq * bestD > bestN * (k1 : Int) then (s1Sq, (k1 : Int)) else (bestN, bestD)
      let (bn1, bd1) := jointDisjointInner k1 s1 s1Sq (k1 + 1) rest bn0 bd0
      jointDisjointOuter (k1 + 1) rest bn1 bd1

/-- Exact integer `(num, den)` pair for Joint Disjoint 2-stage ternary contraction. -/
def jointDisjointTwoStageNumDen (xs : List Int) : Int × Int :=
  let xd := sortDesc xs
  let n2 := normSqList xd
  if n2 == 0 then (1, 1)
  else
    let ps := prefixSums xd
    match ps with
    | [] => (1, 1)
    | _ :: p1Rest =>
        match p1Rest with
        | [] => (1, 1)
        | s1 :: _ =>
            let (bn, bd) := jointDisjointOuter 1 p1Rest (s1 * s1) 1
            (bn, bd * n2)

/-- Exact Joint Disjoint 2-stage ternary contraction factor `α_disjoint(x)` on a non-negative
    integer vector `x` (matching `cpu_eval_twostage(..., mode=1)` bit-for-bit). -/
def jointDisjointTwoStageAlpha (xs : List Int) : Rat :=
  let p := jointDisjointTwoStageNumDen xs
  (p.1 : Rat) / (p.2 : Rat)

/-- Exact `d = 3` witness where Greedy 2-stage strictly beats Joint Disjoint 2-stage
    (overlapping supports beat 2 disjoint buckets: `0.997336` vs `0.953461`). -/
def witnessD3Disjoint : List Int := [4096, 2583, 1070]

/-- Exact `d = 3` GPU worst-case witness for Greedy 2-stage (`0.972958 > 0.953461`). -/
def witnessD3Greedy : List Int := [4096, 1697, 1302]

/-- Exact `d = 4` witness where Joint Disjoint 2-stage strictly beats Greedy 2-stage
    (`0.997936` vs `0.935594`). -/
def witnessD4Greedy : List Int := [4096, 1499, 1398, 1200]

/-- Exact `d = 4` GPU worst-case witness for Joint Disjoint 2-stage (`0.936222 > 0.935594`). -/
def witnessD4Disjoint : List Int := [4096, 2365, 979, 752]

end BitnetContraction
