/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitSliceHankelDifferenceLdu.Defs

/-!
# Trusted Challenge Statements (`bit-slice-hankel-difference-ldu`)

Statements of the affine-shift Laplace identity for Hankel determinants, the odd-parameter mod-8 master invariant and period-8 law, nonsingularity of the odd-parameter Hankel family, vanishing and signed-square laws for the ruler family, the exact 2-adic valuation of the signed ruler Hankel determinant, and the popcount-power factorization.
-/

namespace BitSliceHankelDifferenceLduChallenge

open BitwiseHankelLDU in
/-- Theorem 1 (Affine-shift Laplace identity): det Hankel(alpha a + beta) of size m + 1 equals alpha^(m+1) det Hankel(a) + beta alpha^m det Hankel(second difference of a) of size m. -/
theorem hankel_affine_shift (a : Nat → Int) (α β : Int) (m : Nat) :
    det (hankel (fun k => α * a k + β) (m + 1)) =
      intPow α (m + 1) * det (hankel a (m + 1)) + β * intPow α m * det (hankel (diff2 a) m) := by
  sorry

open BitwiseHankelLDU in
/-- Theorem 2 (Odd-parameter master invariant): for odd c, alpha, beta, the three Hankel determinant families satisfy explicit parity, mod-4 and mod-8 invariants for every n. -/
theorem ecSeq_odd_master_invariant (c α β : Int)
    (hc : c % 2 = 1) (hα : α % 2 = 1) (hβ : β % 2 = 1) (n : Nat) :
    (hankelA c α β n % 2 = 1) ∧
    (hankelB c α β n % 2 = 1) ∧
    (n % 2 = 0 → hankelC c α β n % 8 = altSign (n / 2) % 8) ∧
    (n % 4 = 1 → hankelC c α β n % 4 = 2) ∧
    (n % 4 = 3 → hankelC c α β n % 4 = 0) ∧
    (1 ≤ n → hankelA c α β n % 8 = mod8Pattern c α β (n % 8)) := by
  sorry

open BitwiseHankelLDU in
/-- Theorem 3 (Period-8 law): for odd parameters the Hankel determinant of ecSeq is periodic modulo 8 in n with period 8. -/
theorem ecSeq_odd_mod8_periodic (c α β : Int)
    (hc : c % 2 = 1) (hα : α % 2 = 1) (hβ : β % 2 = 1) (n : Nat) (hn : 1 ≤ n) :
    det (hankel (ecSeq c α β) (n + 8)) % 8 = det (hankel (ecSeq c α β) n) % 8 := by
  sorry

open BitwiseHankelLDU in
/-- Theorem 4 (Nonsingularity): for odd parameters every Hankel determinant of ecSeq is nonzero. -/
theorem ecSeq_odd_nonsingular (c α β : Int)
    (hc : c % 2 = 1) (hα : α % 2 = 1) (hβ : β % 2 = 1) (n : Nat) :
    det (hankel (ecSeq c α β) n) ≠ 0 := by
  sorry

open BitwiseHankelLDU in
/-- Theorem 5 (Ruler odd vanishing): the Hankel determinant of the ruler family ecSeq 0 alpha beta vanishes at every odd size 2m + 1. -/
theorem ruler_family_odd_zero (α β : Int) (m : Nat) :
    det (hankel (ecSeq 0 α β) (2 * m + 1)) = 0 := by
  sorry

open BitwiseHankelLDU in
/-- Theorem 6 (Ruler even signed square): at every even size 2(m + 1) the ruler-family Hankel determinant is altSign(m + 1) times a perfect square. -/
theorem ruler_family_even_signed_square (α β : Int) (m : Nat) :
    ∃ s : Int, det (hankel (ecSeq 0 α β) (2 * (m + 1))) = altSign (m + 1) * (s * s) := by
  sorry

open BitwiseHankelLDU in
/-- Theorem 7 (Exact 2-adic valuation): for n not congruent to 2 modulo 4, the Hankel determinant of the signed ruler sequence is nonzero with 2-adic valuation exactly 2 floor(n/2). -/
theorem signed_ruler_v2_exact (n : Nat) (hn : 1 ≤ n) (hmod : n % 4 ≠ 2) :
    (intPow 2 (2 * (n / 2)) ∣ det (hankel (fun k => altSign (v2 (k + 1))) n)) ∧
    ¬ (intPow 2 (2 * (n / 2) + 1) ∣ det (hankel (fun k => altSign (v2 (k + 1))) n)) ∧
    det (hankel (fun k => altSign (v2 (k + 1))) n) ≠ 0 := by
  sorry

open BitwiseHankelLDU in
/-- Theorem 8 (Popcount-power factorization): the Hankel determinant of r^popcount factors into two Hankel determinants of half size. -/
theorem popPow_hankel_factorization (r : Int) (n : Nat) :
    det (hankel (popPow r) n) =
      det (hankel (popPow r) ((n + 1) / 2)) *
      det (hankel (fun k => popPow r (k + 1) - r * r * popPow r k) (n / 2)) := by
  sorry

end BitSliceHankelDifferenceLduChallenge
