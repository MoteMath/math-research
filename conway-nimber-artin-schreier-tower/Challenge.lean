import ConwayNimberArtinSchreierTower.Defs

namespace ConwayNimberArtinSchreierTowerChallenge

open ConwaySilicon ConwaySilicon.Nim

/-- Simultaneous proof of field invertibility `x ≠ 0 → x ⊗ inv x = 1` for all `k`. -/
theorem mul_inv : ∀ {k : Nat} (x : Nim k), x ≠ zero → mul x (inv x) = one := by
  sorry

/-- **Theorem B (Exact Artin-Schreier Bit-Length Contraction):** For every Fermat block `k` and every nonzero nimber `x ∈ Nim k`, applying `℘_k(x) = x^2 ⊕ x` drops `bitLen` by **exactly 1**. -/
theorem wp_bitLen_contraction : ∀ {k : Nat} (x : Nim k), x ≠ zero → bitLen (wp x) = bitLen x - 1 := by
  sorry

/-- **Theorem D2 (Universal Coset Nim-Harmonic Law):** For ALL `k`, ALL `m ≤ 2^k`, and ALL `X ∈ Nim k` with `X.toNat ≥ 2^m`: `⨁_{a < 2^m} (X ⊕ a)^{-1} = (℘^m(X))^{-1}`. -/
theorem cosetHarmonic_eq_inv_wpIter (k m : Nat) (hm : m ≤ 2 ^ k) :
    ∀ X : Nim k, 2 ^ m ≤ X.toNat → cosetHarmonic k m X = inv (wpIter m X) := by
  sorry

/-- **Theorem E4 (Binary Power-Sum Collapse):** For ALL `k`, ALL `m ≤ 2^k` (even when `m` is NOT a power of 2, so `[0, 2^m)` is NOT a field!), and ALL exponents `d : Nat`: `⨁_{x < 2^m} x^d ∈ {0, 1}`. -/
theorem powerSum_binary_collapse (k m : Nat) (hm : m ≤ 2 ^ k) :
    ∀ d : Nat, powerSum k m d = zero ∨ powerSum k m d = one := by
  sorry

/-- **Theorem G4 (Finite-to-Infinite Evaluation Compiler):** For ANY `k, m, r, n` with `r < 2^k` and `m + r < 2^n`, the exponentially large `2^m`-term dyadic-coset nim-product `⨂_{a < 2^m} (2^(m + r) ⊕ a)` is **identically equal** to a single finite-table lookup at `m % 2^k` inside the fixed finite block `Nim (k + 1)`! -/
theorem finite_table_evaluates_all_m (k m r n : Nat) (hr : r < 2 ^ k) (hbound : m + r < 2 ^ n) :
    (dyadicProd n m (pow2 n (m + r))).toNat =
      (wpIter (m % 2 ^ k) (pow2 (k + 1) (m % 2 ^ k + r))).toNat := by
  sorry

/-- For ALL blocks `n` and ALL `m` with `m + 3 < 2^n`, the fourth-shell coset nim-product `⨂_{a < 2^m} (2^(m+3) ⊕ a)` cycles with **exact period 4** through `[8, 8, 10, 11]`. -/
theorem dyadicProd_fourth_shell_period4 (n m : Nat) (h : m + 3 < 2 ^ n) :
    (dyadicProd n m (pow2 n (m + 3))).toNat =
      match m % 4 with
      | 0 => 8
      | 1 => 8
      | 2 => 10
      | _ => 11 := by
  sorry

/-- **Sharpness 1a:** Period `2^k` in Theorem G1/G2 FAILS at the exact boundary `r = 2^k` for `k = 1` (`r = 2`: `f_2(0) = 4 ≠ 5 = f_2(2)`). -/
theorem sharpness_period_fails_at_k1_r2 :
    wpIter (0 + 2 ^ 1) (pow2 3 (0 + 2 ^ 1 + 2)) ≠ wpIter 0 (pow2 3 (0 + 2)) := by
  sorry

/-- **Sharpness 5:** Popcount Annihilation (`popcount d < m → S(m, d) = 0`, Theorem E2) FAILS at the exact boundary `popcount d = m` (`d = 2^m - 1`) for EVERY `k, m ≤ 2^k`! -/
theorem sharpness_popcount_boundary_nonzero (k m : Nat) (hm : m ≤ 2 ^ k) :
    popcount (2 ^ m - 1) = m ∧ powerSum k m (2 ^ m - 1) ≠ zero := by
  sorry

end ConwayNimberArtinSchreierTowerChallenge
