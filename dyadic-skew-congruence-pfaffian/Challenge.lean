import DyadicSkewCongruencePfaffian.Defs

namespace DyadicSkewCongruencePfaffianChallenge

open SiliconPfaffian

theorem pfaffian_blockUpperId {p q r : Nat} (hpq : p + q = 2 * r)
    (X : Fin p → Fin q → Int) {A : Mat (2 * r)} (hA : IsSkew A) :
    pfaffian r (congruence (castMat hpq (blockUpperId X)) A) = pfaffian r A := by
  sorry

theorem pfaffian_blockSchur_bot {m n : Nat}
    (A00 : Mat (2 * m)) (A01 : Fin (2 * m) → Fin (2 * n) → Int) (A11 : Mat (2 * n))
    (h00 : IsSkew A00) (h11 : IsSkew A11)
    (d : Int) (Y : Fin (2 * n) → Fin (2 * m) → Int)
    (hcert : ∀ i j, d * A01 i j + matMul (matTrans Y) A11 i j = 0) :
    d ^ (2 * m) * pfaffian (m + n) (castMat (by omega) (blockMat A00 A01 (fun i j => -A01 j i) A11)) =
    pfaffian m (fun i j => d * d * A00 i j - d * matMul (matTrans Y) (matTrans A01) i j) * pfaffian n A11 := by
  sorry

/-- Reusable Mechanism 3: Skew-Conference Complementary-Minor Reflection Theorem. For ANY `2(m+n) × 2(m+n)` skew-symmetric integer matrix `A` satisfying `A^2 = -μ I`, let `B` be its leading `2m × 2m` principal submatrix and `D` its trailing `2n × 2n` complementary principal submatrix. Then: `Pf(D)^2 * Pf(A) = μ^n * Pf(D) * Pf(B)` (and if `Pf(D) ≠ 0`, `Pf(D) * Pf(A) = μ^n * Pf(B)`). -/
theorem pfaffian_skewConference_compl {m n : Nat} (A : Mat (2 * (m + n))) (μ : Int)
    (hA : IsSkew A)
    (hconf : ∀ i j, matMul A A i j = if i = j then -μ else 0) :
    let B : Mat (2 * m) := fun i j => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    let D : Mat (2 * n) := fun i j => A ⟨2 * m + i.val, by omega⟩ ⟨2 * m + j.val, by omega⟩
    pfaffian n D * pfaffian n D * pfaffian (m + n) A =
    μ ^ n * pfaffian n D * pfaffian m B := by
  sorry

/-- **Corollary A2 (Exact Dyadic Collapse at `a = 1, b = -1`):** `Pf(C_k - S_{2^k}) = (-1)^{2^{k-1}} * 2^{2^k - 1}` for all `k ≥ 1`. -/
theorem pfaffian_carry_dyadic : ∀ (k : Nat) (hk : 1 ≤ k),
    pfaffian (2 ^ (k - 1)) (castMat (show 2 ^ k = 2 * 2 ^ (k - 1) by
      have : k = (k - 1) + 1 := by omega
      conv => lhs; rw [this]; rw [pow2_succ]) (carryPencilMat k 1 (-1))) =
    ((-1 : Int) ^ (2 ^ (k - 1))) * (2 : Int) ^ (2 ^ k - 1) := by
  sorry

/-- **Corollary B3 (Unweighted Gray-Walsh Signed Mersenne-Power Pfaffian Law):** -/
theorem pfaffian_grayWalsh_pow2 (k : Nat) (hk : 1 ≤ k) :
    pfaffian (2 ^ (k - 1)) (castMat (show 2 ^ k = 2 * 2 ^ (k - 1) by
      have : k = (k - 1) + 1 := by omega
      conv => lhs; rw [this]; rw [pow2_succ]) (grayWalshMat (2 ^ k))) =
    if k = 1 then 1 else if k = 2 then -3 else ((2 : Int) ^ k - 1) ^ (2 ^ (k - 2)) := by
  sorry

/-- **Theorem D (Skew-Walsh Exact Unimodularity Law):** Removing the 1-bit Gray shift from `grayWalshMat` causes an exact phase transition from exponential Mersenne powers `(2^k - 1)^{2^{k-2}}` to universal unimodularity `Pf(W_{2^k}) = +1`! -/
theorem pfaffian_skewWalsh (k : Nat) (hk : 1 ≤ k) :
    pfaffian (2 ^ (k - 1)) (castMat (show 2 ^ k = 2 * 2 ^ (k - 1) by
      have : k = (k - 1) + 1 := by omega
      conv => lhs; rw [this]; rw [pow2_succ]) (skewWalshMat k)) = 1 := by
  sorry

/-- Counterexample 1: Removing bit-complement from `carryAsymMat` (`sgn(y-x) * carries(x, y)`) collapses `Pf` at `k = 2` to `0` (vs `Pf(C_2) = 3`). -/
theorem sharpness_raw_carry_no_complement :
    pfaffian 2 (fun i j : Fin 4 => sgnInt i.val j.val * carries i.val j.val) = 0 ∧
    pfaffian 2 (castMat (by decide) (carryAsymMat 2)) = 3 := by
  sorry

/-- Counterexample 3: Shifting Skew-Walsh by `s = 2` breaks unimodularity at `k = 2` (`Pf = 3 ≠ 1`), whereas `s = 0` and `s = 1` both give `1`. -/
theorem sharpness_shifted_skewWalsh :
    pfaffian 2 (fun i j : Fin 4 =>
      sgnInt i.val j.val * paritySign ((i.val + 2) &&& (j.val + 2))) = 3 ∧
    pfaffian 2 (fun i j : Fin 4 =>
      sgnInt i.val j.val * paritySign ((i.val + 1) &&& (j.val + 1))) = 1 := by
  sorry

end DyadicSkewCongruencePfaffianChallenge
