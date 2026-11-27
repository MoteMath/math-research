/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DyadicLdltSchurPosdefEngine

/-!
# Verified Solutions (`dyadic-ldlt-schur-posdef-engine`)
-/

namespace DyadicLdltSchurPosdefEngineChallenge

open DyadicLDLT DyadicLDLT.Dyad in
/-- Theorem 1 (LDL^T iff): given an exact dyadic LDL^T factorization, M is strictly positive definite iff every pivot D r is positive. -/
theorem ldlt_strictlyPosDef_iff {N : Nat} {M L : Mat} {D : Vec}
    (h : IsLDLTAlg N M L D) :
    StrictlyPosDef N M ↔ (∀ r, r < N → zero <ᵈ D r) :=
  DyadicLDLT.ldlt_strictlyPosDef_iff h

open DyadicLDLT DyadicLDLT.Dyad in
/-- Theorem 2 (Quadratic-form lower bound): a uniform pivot lower bound delta gives v^T M v >= delta times the sum of squares of L^T v. -/
theorem ldlt_quadForm_lower_bound {N : Nat} {M L : Mat} {D : Vec} {δ : Dyad}
    (h : IsLDLTAlg N M L D) (hδ : ∀ r, r < N → δ ≤ᵈ D r) (v : Vec) :
    δ * dsum N (fun r => matTVec N L v r * matTVec N L v r) ≤ᵈ quadForm N M v :=
  DyadicLDLT.ldlt_quadForm_lower_bound h hδ v

open DyadicLDLT DyadicLDLT.Dyad in
/-- Theorem 3 (Schur-system lifting): for a nested Schur system agreeing with M on all dyadic prefixes, positive definiteness of every n x n leading block is equivalent to positivity of the Schur pivots. -/
theorem schurSystem_nested_iff {State : Type} (S : SchurSystem State) (σ : State) (M : Mat)
    (hagree : ∀ k i j, i < 2 ^ k → j < 2 ^ k → M i j ≈ S.mat σ k i j)
    (n : Nat) :
    StrictlyPosDef n M ↔ (∀ r, r < n → zero <ᵈ schurD S σ n r) :=
  DyadicLDLT.schurSystem_nested_iff S σ M hagree n

open DyadicLDLT DyadicLDLT.Dyad in
/-- Theorem 4 (Hamming sharp threshold): the van der Corput Hamming matrix is strictly positive definite for all n iff 4 beta <= 3 c. -/
theorem vdcHamming_strictlyPosDef_all_n_iff {c β : Dyad} (hβ : zero <ᵈ β) :
    (∀ n : Nat, StrictlyPosDef n (vdcHammingMat c β)) ↔
    ofInt 4 * β ≤ᵈ ofInt 3 * c :=
  DyadicLDLT.vdcHamming_strictlyPosDef_all_n_iff hβ

open DyadicLDLT DyadicLDLT.Dyad in
/-- Theorem 5 (Critical Hamming instance): at the critical parameters (c, beta) = (4, 3) the matrix is strictly positive definite for every n. -/
theorem vdcHamming_critical_4_3_all_n (n : Nat) :
    StrictlyPosDef n (vdcHammingMat (ofInt 4) (ofInt 3)) :=
  DyadicLDLT.vdcHamming_critical_4_3_all_n n

open DyadicLDLT DyadicLDLT.Dyad in
/-- Theorem 6 (Hamming sharpness witness): at (15/4, 3) the matrix is not strictly positive definite at n = 16. -/
theorem vdcHamming_sharp_15_4_fails_16 :
    ¬ StrictlyPosDef 16 (vdcHammingMat ⟨15, 2⟩ (ofInt 3)) :=
  DyadicLDLT.vdcHamming_sharp_15_4_fails_16

open DyadicLDLT DyadicLDLT.Dyad in
/-- Theorem 7 (Gray-weighted family): the Gray-weighted matrix is strictly positive definite for every n. -/
theorem grayWeighted_strictlyPosDef_all_n (n : Nat) :
    StrictlyPosDef n grayWeightedMat :=
  DyadicLDLT.grayWeighted_strictlyPosDef_all_n n

open DyadicLDLT DyadicLDLT.Dyad in
/-- Theorem 8 (Exponential family critical instance): the exponential van der Corput matrix with parameters (7, 6) is strictly positive definite for every n. -/
theorem expVdc_critical_7_6_all_n (n : Nat) :
    StrictlyPosDef n (expVdcMat (ofInt 7) (ofInt 6)) :=
  DyadicLDLT.expVdc_critical_7_6_all_n n

end DyadicLdltSchurPosdefEngineChallenge
