/-
  Pure-Silicon Mathematical "Big Bang" — Apex 2 Zero-Dependency Lean 4 Proofs
  (`lean/Apex2DedekindRobinVerify.lean`: Epochs 77..80 Odd-Sawtooth Dedekind
  Antisymmetry & Reciprocity, Stern-Brocot / Haros `SL_2(Z)` Farey Unimodularity,
  Universal Arbitrary-Dimension Lagrange / Franel Cauchy-Schwarz Inequality,
  and Certified Robin Exception & Pass Integer Verifier Soundness)

  NO Mathlib. NO built-in `Nat`, `Int`, `Rat`, `Real`, or `Bool` arithmetic used anywhere.
  Extends `BigBangScratchVerify` .. `Apex1ConcreteWeilLDLTVerify`:
    1. Exact Integer-Cleared Sawtooth `bsawtooth_2b`:
       - Universal Odd-Sawtooth Reflection Antisymmetry (`bsawtooth_2b_reflect_antisym`:
         `2(b - m) - b ≈ -(2m - b)` whenever `m + d = b`);
       - Universal Midpoint Annihilation (`bsawtooth_2b_midpoint_zero`: `((1/2)) = 0`);
       - Exact Dedekind Reciprocity Certificates `a * S_12(a, b) + b * S_12(b, a) ≈ a^2 + b^2 - 3ab + 1`
         for coprime pairs `(1, 1), (1, 2), (1, 3), (1, 4), (3, 7)`!
    2. Farey Mediant & Haros Next-Fraction `SL_2(Z)` Unimodularity:
       - `bfarey_mediant_left_det` & `bfarey_mediant_right_det`:
         `det(u, u + v) ≈ det(u, v)` and `det(u + v, v) ≈ det(u, v)`;
       - `bharos_step_preserves_det`: proves for ALL `p0 q0 p1 q1 k : BSignPair` that
         `(k * p1 - p0) * q1 - p1 * (k * q1 - q0) ≈ p1 * q0 - p0 * q1`, formally certifying why
         every Haros Farey step in `k_a2b_dedekind_and_franel` preserves `det == 1`!
    3. Arbitrary-Dimension Lagrange Sum-of-Squares Identity & Franel Cauchy-Schwarz Bound:
       - `bvec_lagrange_identity`: for ALL dimensions `n` and vectors `v : BVec`,
         `len(v) * (∑ v_i^2) ≈ (∑ v_i)^2 + ∑_{i < j} (v_i - v_j)^2`;
       - `bfranel_cauchy_schwarz_universal`: `(∑ v_i)^2 <= len(v) * (∑ v_i^2)` for ALL `v : BVec`!
    4. Robin Exception & Pass Integer Verifier Soundness + Coprime Multiplicativity Witnesses:
       - `brobin_exception_verifier_sound` & `brobin_pass_verifier_sound` (`brat_lt` strict order);
       - Ground Robin exception certificates at `n = 2, 6, 12` and coprime `σ_1` multiplicativity.

  Paper Inputs Recorded Explicitly (Literature Equivalences to RH — NOT Claimed Formalised Here):
    - G. Robin (1984), J. Math. Pures Appl. 63, 187-213 (`RH <=> ∀ n >= 5041, σ_1(n) < e^γ n log log n`).
    - J. C. Lagarias (2002), Amer. Math. Monthly 109, 534-543 (`RH <=> ∀ n >= 1, σ_1(n) <= H_n + e^{H_n} log H_n`).
    - J. Franel (1924) & E. Landau (1924), Gott. Nachr., 198-206.
    - R. Dedekind (1892), Erlauterungen zu den Fragmenten XXVIII.

  Mandatory Scope Note: Finite-`n` evaluations up to `n = 1,048,576` and finite-order Farey /
  Dedekind checks say nothing about the zeros of `zeta(s)` over `Q`; no route to RH is claimed.
-/

import BitCircuitSynthesis.BigBangScratchVerify
import BitCircuitSynthesis.Epoch7PrimesVerify
import BitCircuitSynthesis.Epoch10AllThreeVerify
import BitCircuitSynthesis.AutoCompiledArenaVerify
import BitCircuitSynthesis.Waves1To4Verify
import BitCircuitSynthesis.Waves5To8Verify
import BitCircuitSynthesis.Waves9To12Verify
import BitCircuitSynthesis.Stage3CarryRHVerify
import BitCircuitSynthesis.Track1UnshackledVerify
import BitCircuitSynthesis.Waves13To16Verify
import BitCircuitSynthesis.Track3PositivityCarryVerify
import BitCircuitSynthesis.Frontier1ModularityWittVerify
import BitCircuitSynthesis.AutoInductiveArenaVerify
import BitCircuitSynthesis.Frontier3LDLTCheckerVerify
import BitCircuitSynthesis.AutoEpoch6Complete1799Verify
import BitCircuitSynthesis.Horizon2ExplicitRobinCriteriaVerify
import BitCircuitSynthesis.Horizon3DirichletTwistVerify
import BitCircuitSynthesis.Apex1ConcreteWeilLDLTVerify

namespace SiliconBigBang

-- ============================================================================
-- PART I: Integer-Cleared Sawtooth Antisymmetry & Dedekind Reciprocity
-- ============================================================================

-- For `0 < m < b`, `2 * b * ((m / b)) = 2 * m - b`, represented exactly in `BSignPair`!
def bsawtooth_2b (m b : BBin) : BSignPair :=
  ⟨badd m m, b⟩

-- Theorem 1A: Universal Odd-Sawtooth Reflection Antisymmetry `2(b - m) - b ≈ -(2m - b)`!
theorem bsawtooth_2b_reflect_antisym (m d : BBin) :
    bsign_equiv (bsawtooth_2b d (badd m d)) (bsign_neg (bsawtooth_2b m (badd m d))) := by
  unfold bsawtooth_2b bsign_neg bsign_equiv
  dsimp only
  rw [badd_four_swap m d m d, badd_comm (badd m m) (badd d d)]

-- Theorem 1B: Universal Midpoint Zero `((1/2)) = 0` (`2m - 2m ≈ 0`)!
theorem bsawtooth_2b_midpoint_zero (m : BBin) :
    bsign_equiv (bsawtooth_2b m (badd m m)) bsign_zero := by
  unfold bsawtooth_2b bsign_zero bsign_equiv
  dsimp only
  exact badd_zero_right (badd m m)

-- Exact Dedekind Reciprocity Polynomial RHS: `a^2 + b^2 - 3*a*b + 1` in `BSignPair`!
def bdedekind_recip_rhs (a b : BSignPair) : BSignPair :=
  let three := bpos_to_sign bpos_three
  let a2 := bsign_mul a a
  let b2 := bsign_mul b b
  let ab3 := bsign_mul three (bsign_mul a b)
  bsign_add (bsign_add (bsign_add a2 b2) (bsign_neg ab3)) bsign_one

-- Ground Dedekind `S_12(a, b) = 12 * b * s(a, b)` Reciprocity Certificates on
-- `(1, 1): S_12=0`, `(1, 2): S_12=0`, `(1, 3): S_12(1,3)=2, S_12(3,1)=0`,
-- `(1, 4): S_12(1,4)=6, S_12(4,1)=0`, and `(3, 7): S_12(3,7)=-6, S_12(7,3)=2`!
def bs_two   : BSignPair := bpos_to_sign bpos_two
def bs_three : BSignPair := bpos_to_sign bpos_three
def bs_four  : BSignPair := bsign_nonneg_of bfour
def bs_six   : BSignPair := bpos_to_sign bpos_six
def bs_seven : BSignPair := bsign_nonneg_of bseven

theorem bdedekind_reciprocity_ground_certificates :
    bsign_equiv (bsign_add (bsign_mul bsign_one bsign_zero) (bsign_mul bsign_one bsign_zero))
                (bdedekind_recip_rhs bsign_one bsign_one) ∧
    bsign_equiv (bsign_add (bsign_mul bsign_one bsign_zero) (bsign_mul bs_two bsign_zero))
                (bdedekind_recip_rhs bsign_one bs_two) ∧
    bsign_equiv (bsign_add (bsign_mul bsign_one bs_two) (bsign_mul bs_three bsign_zero))
                (bdedekind_recip_rhs bsign_one bs_three) ∧
    bsign_equiv (bsign_add (bsign_mul bsign_one bs_six) (bsign_mul bs_four bsign_zero))
                (bdedekind_recip_rhs bsign_one bs_four) ∧
    bsign_equiv (bsign_add (bsign_mul bs_three (bsign_neg bs_six)) (bsign_mul bs_seven bs_two))
                (bdedekind_recip_rhs bs_three bs_seven) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- PART II: Stern-Brocot Mediant & Haros Next-Fraction `SL_2(Z)` Unimodularity
-- ============================================================================

def bfarey_det (p0 q0 p1 q1 : BSignPair) : BSignPair :=
  bsign_add (bsign_mul p1 q0) (bsign_neg (bsign_mul p0 q1))

theorem bsign_neg_add_distrib (x y : BSignPair) :
    bsign_neg (bsign_add x y) = bsign_add (bsign_neg x) (bsign_neg y) := rfl

-- Helper: `(x + a) + (-x + b) ≈ a + b`!
theorem bsign_cancel_outer_pair (x a b : BSignPair) :
    bsign_equiv (bsign_add (bsign_add x a) (bsign_add (bsign_neg x) b)) (bsign_add a b) := by
  rw [bsign_add_four_swap x a (bsign_neg x) b]
  exact bsign_equiv_trans _ (bsign_add bsign_zero (bsign_add a b)) _
    (bsign_add_congr _ _ _ _ (bsign_add_neg_cancel x) (bsign_equiv_refl _))
    (by rw [bsign_add_zero_left]; exact bsign_equiv_refl _)

-- Theorem 2A: Left Stern-Brocot / Farey Mediant Preserves `SL_2(Z)` Determinant!
-- `(p0 + p1) * q0 - p0 * (q0 + q1) ≈ p1 * q0 - p0 * q1`
theorem bfarey_mediant_left_det (p0 q0 p1 q1 : BSignPair) :
    bsign_equiv (bfarey_det p0 q0 (bsign_add p0 p1) (bsign_add q0 q1))
                (bfarey_det p0 q0 p1 q1) := by
  unfold bfarey_det
  rw [bsign_mul_add_right p0 p1 q0, bsign_mul_add_distrib p0 q0 q1, bsign_neg_add_distrib]
  exact bsign_cancel_outer_pair (bsign_mul p0 q0) (bsign_mul p1 q0) (bsign_neg (bsign_mul p0 q1))

-- Theorem 2B: Right Stern-Brocot / Farey Mediant Preserves `SL_2(Z)` Determinant!
-- `p1 * (q0 + q1) - (p0 + p1) * q1 ≈ p1 * q0 - p0 * q1`
theorem bfarey_mediant_right_det (p0 q0 p1 q1 : BSignPair) :
    bsign_equiv (bfarey_det (bsign_add p0 p1) (bsign_add q0 q1) p1 q1)
                (bfarey_det p0 q0 p1 q1) := by
  unfold bfarey_det
  rw [bsign_mul_add_distrib p1 q0 q1, bsign_mul_add_right p0 p1 q1, bsign_neg_add_distrib]
  rw [bsign_add_comm (bsign_mul p1 q0) (bsign_mul p1 q1),
      bsign_add_comm (bsign_neg (bsign_mul p0 q1)) (bsign_neg (bsign_mul p1 q1))]
  exact bsign_cancel_outer_pair (bsign_mul p1 q1) (bsign_mul p1 q0) (bsign_neg (bsign_mul p0 q1))

-- Theorem 2C (`bharos_step_preserves_det`):
-- Universal Soundness of Haros's Next-Farey-Term Recurrence `(p2, q2) = (k*p1 - p0, k*q1 - q0)`!
-- Proves `(k * p1 - p0) * q1 - p1 * (k * q1 - q0) ≈ p1 * q0 - p0 * q1` for ALL `p0, q0, p1, q1, k`!
theorem bharos_step_preserves_det (p0 q0 p1 q1 k : BSignPair) :
    bsign_equiv (bfarey_det p1 q1
                  (bsign_add (bsign_mul k p1) (bsign_neg p0))
                  (bsign_add (bsign_mul k q1) (bsign_neg q0)))
                (bfarey_det p0 q0 p1 q1) := by
  unfold bfarey_det
  rw [bsign_mul_add_right (bsign_mul k p1) (bsign_neg p0) q1,
      bsign_mul_add_distrib p1 (bsign_mul k q1) (bsign_neg q0),
      bsign_neg_add_distrib]
  have h1 : bsign_mul (bsign_neg p0) q1 = bsign_neg (bsign_mul p0 q1) := bsign_mul_neg_left p0 q1
  have h2 : bsign_neg (bsign_mul p1 (bsign_neg q0)) = bsign_mul p1 q0 := by
    rw [bsign_mul_neg_right p1 q0, bsign_neg_invol]
  have h3 : bsign_mul p1 (bsign_mul k q1) = bsign_mul (bsign_mul k p1) q1 := by
    rw [← bsign_mul_assoc p1 k q1, bsign_mul_comm p1 k]
  rw [h1, h2, h3]
  exact bsign_equiv_trans _ (bsign_add (bsign_neg (bsign_mul p0 q1)) (bsign_mul p1 q0)) _
    (bsign_cancel_outer_pair (bsign_mul (bsign_mul k p1) q1) (bsign_neg (bsign_mul p0 q1)) (bsign_mul p1 q0))
    (by rw [bsign_add_comm]; exact bsign_equiv_refl _)

-- ============================================================================
-- PART III: Arbitrary-Dimension Lagrange Identity & Franel Cauchy-Schwarz Bound
-- ============================================================================

def bvec_len_sign : BVec → BSignPair
  | BVec.vnil       => bsign_zero
  | BVec.vcons _ xs => bsign_add bsign_one (bvec_len_sign xs)

def bvec_sum : BVec → BSignPair
  | BVec.vnil       => bsign_zero
  | BVec.vcons x xs => bsign_add x (bvec_sum xs)

def bvec_sq_sum : BVec → BSignPair
  | BVec.vnil       => bsign_zero
  | BVec.vcons x xs => bsign_add (bsign_mul x x) (bvec_sq_sum xs)

def bvec_pair_diff_sq (x : BSignPair) : BVec → BSignPair
  | BVec.vnil       => bsign_zero
  | BVec.vcons y ys =>
      let diff := bsign_add x (bsign_neg y)
      bsign_add (bsign_mul diff diff) (bvec_pair_diff_sq x ys)

def bvec_lagrange_sos : BVec → BSignPair
  | BVec.vnil       => bsign_zero
  | BVec.vcons x xs => bsign_add (bvec_pair_diff_sq x xs) (bvec_lagrange_sos xs)

-- Key scalar identity: `(x - y)^2 + 2*x*y ≈ x^2 + y^2`!
theorem bsign_sub_sq_plus_2xy (x y : BSignPair) :
    bsign_equiv
      (bsign_add (bsign_mul (bsign_add x (bsign_neg y)) (bsign_add x (bsign_neg y)))
                 (bsign_add (bsign_mul x y) (bsign_mul x y)))
      (bsign_add (bsign_mul x x) (bsign_mul y y)) := by
  rw [bsign_mul_add_distrib (bsign_add x (bsign_neg y)) x (bsign_neg y),
      bsign_mul_add_right x (bsign_neg y) x,
      bsign_mul_add_right x (bsign_neg y) (bsign_neg y),
      bsign_mul_neg_left y x, bsign_mul_comm y x,
      bsign_mul_neg_right x y,
      bsign_mul_neg_left y (bsign_neg y), bsign_mul_neg_right y y, bsign_neg_invol]
  -- Now LHS is `((x*x + -(x*y)) + (-(x*y) + y*y)) + (x*y + x*y)`!
  have hmid : bsign_add (bsign_neg (bsign_mul x y)) (bsign_mul y y) =
              bsign_add (bsign_mul y y) (bsign_neg (bsign_mul x y)) :=
    bsign_add_comm _ _
  rw [hmid, bsign_add_four_swap (bsign_mul x x) (bsign_neg (bsign_mul x y))
                                (bsign_mul y y) (bsign_neg (bsign_mul x y))]
  rw [bsign_add_comm (bsign_add (bsign_mul x x) (bsign_mul y y)) _,
      bsign_add_assoc _ (bsign_add (bsign_mul x x) (bsign_mul y y)) (bsign_add (bsign_mul x y) (bsign_mul x y)),
      bsign_add_comm (bsign_add (bsign_mul x x) (bsign_mul y y)) (bsign_add (bsign_mul x y) (bsign_mul x y)),
      ← bsign_add_assoc]
  have hcanc : bsign_equiv
      (bsign_add (bsign_add (bsign_neg (bsign_mul x y)) (bsign_neg (bsign_mul x y)))
                 (bsign_add (bsign_mul x y) (bsign_mul x y)))
      bsign_zero := by
    rw [← bsign_neg_add_distrib (bsign_mul x y) (bsign_mul x y),
        bsign_add_comm (bsign_neg _) _]
    exact bsign_add_neg_cancel _
  exact bsign_equiv_trans _ (bsign_add bsign_zero (bsign_add (bsign_mul x x) (bsign_mul y y))) _
    (bsign_add_congr _ _ _ _ hcanc (bsign_equiv_refl _))
    (by rw [bsign_add_zero_left]; exact bsign_equiv_refl _)

-- Helper: `(∑_{y ∈ ys} (x - y)^2) + 2*x*(∑ ys) ≈ len(ys)*x^2 + (∑ y^2)`!
theorem bvec_pair_diff_sq_expand (x : BSignPair) (ys : BVec) :
    bsign_equiv
      (bsign_add (bvec_pair_diff_sq x ys)
                 (bsign_add (bsign_mul x (bvec_sum ys)) (bsign_mul x (bvec_sum ys))))
      (bsign_add (bsign_mul (bvec_len_sign ys) (bsign_mul x x)) (bvec_sq_sum ys)) := by
  induction ys with
  | vnil =>
    dsimp only [bvec_pair_diff_sq, bvec_sum, bvec_len_sign, bvec_sq_sum]
    rw [bsign_mul_zero_right, bsign_mul_zero_left]
    exact bsign_equiv_refl _
  | vcons y ys ih =>
    dsimp only [bvec_pair_diff_sq, bvec_sum, bvec_len_sign, bvec_sq_sum]
    rw [bsign_mul_add_distrib x y (bvec_sum ys),
        bsign_add_four_swap (bsign_mul x y) (bsign_mul x (bvec_sum ys))
                            (bsign_mul x y) (bsign_mul x (bvec_sum ys)),
        bsign_add_four_swap _ (bvec_pair_diff_sq x ys) _ _,
        bsign_mul_add_right bsign_one (bvec_len_sign ys) (bsign_mul x x),
        bsign_mul_one_left (bsign_mul x x),
        bsign_add_four_swap (bsign_mul x x) (bsign_mul (bvec_len_sign ys) (bsign_mul x x))
                            (bsign_mul y y) (bvec_sq_sum ys)]
    exact bsign_add_congr _ _ _ _ (bsign_sub_sq_plus_2xy x y) ih

-- Scalar binomial square: `(x + s)^2 = x^2 + (2*x*s + s^2)`!
theorem bsign_binom_sq (x s : BSignPair) :
    bsign_mul (bsign_add x s) (bsign_add x s) =
    bsign_add (bsign_mul x x)
              (bsign_add (bsign_add (bsign_mul x s) (bsign_mul x s)) (bsign_mul s s)) := by
  rw [bsign_mul_add_distrib (bsign_add x s) x s,
      bsign_mul_add_right x s x,
      bsign_mul_add_right x s s,
      bsign_mul_comm s x,
      bsign_add_assoc (bsign_mul x x) (bsign_mul x s) (bsign_add (bsign_mul x s) (bsign_mul s s)),
      ← bsign_add_assoc (bsign_mul x s) (bsign_mul x s) (bsign_mul s s)]

-- Theorem 3A (`bvec_lagrange_identity`):
-- Universal Arbitrary-Dimension Lagrange Sum-of-Squares Identity!
-- `len(v) * (∑ v_i^2) ≈ (∑ v_i)^2 + ∑_{i < j} (v_i - v_j)^2` for ALL `v : BVec`!
theorem bvec_lagrange_identity (v : BVec) :
    bsign_equiv
      (bsign_mul (bvec_len_sign v) (bvec_sq_sum v))
      (bsign_add (bsign_mul (bvec_sum v) (bvec_sum v)) (bvec_lagrange_sos v)) := by
  induction v with
  | vnil =>
    dsimp only [bvec_len_sign, bvec_sq_sum, bvec_sum, bvec_lagrange_sos]
    exact bsign_equiv_refl _
  | vcons x xs ih =>
    dsimp only [bvec_len_sign, bvec_sq_sum, bvec_sum, bvec_lagrange_sos]
    -- Expand LHS: `(1 + n) * (x^2 + S2) = (x^2 + S2) + (n * x^2 + n * S2)`
    rw [bsign_mul_add_right bsign_one (bvec_len_sign xs) (bsign_add (bsign_mul x x) (bvec_sq_sum xs)),
        bsign_mul_one_left,
        bsign_mul_add_distrib (bvec_len_sign xs) (bsign_mul x x) (bvec_sq_sum xs)]
    -- Rearrange LHS to `x^2 + ((n * x^2 + S2) + n * S2)`:
    have hlhs :
        bsign_add (bsign_add (bsign_mul x x) (bvec_sq_sum xs))
                  (bsign_add (bsign_mul (bvec_len_sign xs) (bsign_mul x x))
                             (bsign_mul (bvec_len_sign xs) (bvec_sq_sum xs))) =
        bsign_add (bsign_mul x x)
                  (bsign_add (bsign_add (bsign_mul (bvec_len_sign xs) (bsign_mul x x)) (bvec_sq_sum xs))
                             (bsign_mul (bvec_len_sign xs) (bvec_sq_sum xs))) := by
      rw [bsign_add_assoc (bsign_mul x x) (bvec_sq_sum xs) _,
          ← bsign_add_assoc (bvec_sq_sum xs) (bsign_mul (bvec_len_sign xs) (bsign_mul x x)) _,
          bsign_add_comm (bvec_sq_sum xs) (bsign_mul (bvec_len_sign xs) (bsign_mul x x))]
    rw [hlhs]
    -- Expand RHS `(x + S1)^2 + (pair_diff_sq + L)` to `x^2 + ((pair_diff_sq + 2*x*S1) + (S1^2 + L))`:
    rw [bsign_binom_sq x (bvec_sum xs)]
    have hrhs :
        bsign_add (bsign_add (bsign_mul x x)
                             (bsign_add (bsign_add (bsign_mul x (bvec_sum xs)) (bsign_mul x (bvec_sum xs)))
                                        (bsign_mul (bvec_sum xs) (bvec_sum xs))))
                  (bsign_add (bvec_pair_diff_sq x xs) (bvec_lagrange_sos xs)) =
        bsign_add (bsign_mul x x)
                  (bsign_add (bsign_add (bvec_pair_diff_sq x xs)
                                        (bsign_add (bsign_mul x (bvec_sum xs)) (bsign_mul x (bvec_sum xs))))
                             (bsign_add (bsign_mul (bvec_sum xs) (bvec_sum xs)) (bvec_lagrange_sos xs))) := by
      rw [bsign_add_assoc (bsign_mul x x) _ _,
          bsign_add_four_swap (bsign_add (bsign_mul x (bvec_sum xs)) (bsign_mul x (bvec_sum xs)))
                              (bsign_mul (bvec_sum xs) (bvec_sum xs))
                              (bvec_pair_diff_sq x xs)
                              (bvec_lagrange_sos xs),
          bsign_add_comm (bsign_add (bsign_mul x (bvec_sum xs)) (bsign_mul x (bvec_sum xs)))
                         (bvec_pair_diff_sq x xs)]
    rw [hrhs]
    exact bsign_add_congr _ _ _ _ (bsign_equiv_refl _)
      (bsign_add_congr _ _ _ _ (bsign_equiv_symm _ _ (bvec_pair_diff_sq_expand x xs)) ih)

theorem bvec_pair_diff_sq_nonneg (x : BSignPair) (ys : BVec) :
    bsign_le bsign_zero (bvec_pair_diff_sq x ys) := by
  induction ys with
  | vnil => exact bsign_le_refl bsign_zero
  | vcons y ys ih =>
    dsimp only [bvec_pair_diff_sq]
    have h0 : bsign_add bsign_zero bsign_zero = bsign_zero := rfl
    rw [← h0]
    exact bsign_le_add_mono _ _ _ _ (bsign_sq_nonneg _) ih

theorem bvec_lagrange_sos_nonneg (v : BVec) :
    bsign_le bsign_zero (bvec_lagrange_sos v) := by
  induction v with
  | vnil => exact bsign_le_refl bsign_zero
  | vcons x xs ih =>
    dsimp only [bvec_lagrange_sos]
    have h0 : bsign_add bsign_zero bsign_zero = bsign_zero := rfl
    rw [← h0]
    exact bsign_le_add_mono _ _ _ _ (bvec_pair_diff_sq_nonneg x xs) ih

-- Theorem 3B (`bfranel_cauchy_schwarz_universal`):
-- Universal Arbitrary-Dimension Cauchy-Schwarz Inequality `(∑ v_i)^2 <= len(v) * (∑ v_i^2)`!
theorem bfranel_cauchy_schwarz_universal (v : BVec) :
    bsign_le (bsign_mul (bvec_sum v) (bvec_sum v))
             (bsign_mul (bvec_len_sign v) (bvec_sq_sum v)) := by
  rcases bvec_lagrange_sos_nonneg v with ⟨u, hu⟩
  rw [bsign_add_zero_left] at hu
  refine ⟨u, ?_⟩
  exact bsign_equiv_trans _ (bsign_add (bsign_mul (bvec_sum v) (bvec_sum v)) (bvec_lagrange_sos v)) _
    (bsign_add_congr _ _ _ _ (bsign_equiv_refl _) hu)
    (bsign_equiv_symm _ _ (bvec_lagrange_identity v))

-- ============================================================================
-- PART IV: Strict Rational Order `brat_lt`, Robin Exception/Pass Verifiers & Witnesses
-- ============================================================================

def bsign_lt (x y : BSignPair) : Prop :=
  ∃ p : BPos, bsign_equiv (bsign_add x (bsign_nonneg_of (BBin.pos p))) y

def brat_lt (q r : BRat) : Prop :=
  bsign_lt (bsign_mul q.num (bpos_to_sign r.den)) (bsign_mul r.num (bpos_to_sign q.den))

theorem bsign_le_lt_trans (x y z : BSignPair) (hxy : bsign_le x y) (hyz : bsign_lt y z) :
    bsign_lt x z := by
  rcases hxy with ⟨u, hu⟩
  rcases hyz with ⟨p, hp⟩
  have hsum : ∃ q : BPos, badd u (BBin.pos p) = BBin.pos q := by
    cases u with
    | zero => exact ⟨p, rfl⟩
    | pos r => exact ⟨bpos_add r p, rfl⟩
  rcases hsum with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [← hq, ← bsign_nonneg_add u (BBin.pos p), ← bsign_add_assoc x (bsign_nonneg_of u) _]
  exact bsign_equiv_trans _ (bsign_add y (bsign_nonneg_of (BBin.pos p))) _
    (bsign_add_congr _ _ _ _ hu (bsign_equiv_refl _)) hp

theorem bsign_lt_le_trans (x y z : BSignPair) (hxy : bsign_lt x y) (hyz : bsign_le y z) :
    bsign_lt x z := by
  rcases hxy with ⟨p, hp⟩
  rcases hyz with ⟨u, hu⟩
  have hsum : ∃ q : BPos, badd (BBin.pos p) u = BBin.pos q := by
    cases u with
    | zero => exact ⟨p, badd_zero_right (BBin.pos p)⟩
    | pos r => exact ⟨bpos_add p r, rfl⟩
  rcases hsum with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [← hq, ← bsign_nonneg_add (BBin.pos p) u, ← bsign_add_assoc x _ (bsign_nonneg_of u)]
  exact bsign_equiv_trans _ (bsign_add y (bsign_nonneg_of u)) _
    (bsign_add_congr _ _ _ _ hp (bsign_equiv_refl _)) hu

theorem bsign_lt_cancel_pos_right (x y : BSignPair) (c : BPos)
    (h : bsign_lt (bsign_mul x (bpos_to_sign c)) (bsign_mul y (bpos_to_sign c))) :
    bsign_lt x y := by
  rcases bsign_trichotomy (bsign_add y (bsign_neg x)) with h0 | ⟨p, hp⟩ | ⟨p, hn⟩
  · -- Impossible: `y - x ≈ 0` implies `y*c ≈ x*c`, contradicting `x*c + q ≈ y*c`!
    exfalso
    rcases h with ⟨q, hq⟩
    have hyx : bsign_equiv y x := by
      have hx : bsign_equiv (bsign_add (bsign_add y (bsign_neg x)) x) (bsign_add bsign_zero x) :=
        bsign_add_congr _ _ _ _ h0 (bsign_equiv_refl x)
      rw [bsign_add_assoc y (bsign_neg x) x, bsign_add_comm (bsign_neg x) x, bsign_add_zero_left] at hx
      have hy : bsign_equiv (bsign_add y (bsign_add x (bsign_neg x))) y :=
        bsign_equiv_trans _ (bsign_add y bsign_zero) _
          (bsign_add_congr _ _ _ _ (bsign_equiv_refl y) (bsign_add_neg_cancel x))
          (by rw [bsign_add_zero_right]; exact bsign_equiv_refl y)
      exact bsign_equiv_trans _ _ _ (bsign_equiv_symm _ _ hy) hx
    have hxc := bsign_mul_congr _ _ _ _ hyx (bsign_equiv_refl (bpos_to_sign c))
    let xc := bsign_mul x (bpos_to_sign c)
    have heq : bsign_equiv (bsign_add xc (bsign_nonneg_of (BBin.pos q))) xc :=
      bsign_equiv_trans _ _ _ hq hxc
    have hiso : bsign_equiv (bsign_add (bsign_neg xc) (bsign_add xc (bsign_nonneg_of (BBin.pos q))))
                            (bsign_add (bsign_neg xc) xc) :=
      bsign_add_congr _ _ _ _ (bsign_equiv_refl _) heq
    rw [← bsign_add_assoc (bsign_neg xc) xc _, bsign_add_comm (bsign_neg xc) xc] at hiso
    have hq0 : bsign_equiv (bsign_nonneg_of (BBin.pos q)) bsign_zero :=
      bsign_equiv_trans _ (bsign_add bsign_zero (bsign_nonneg_of (BBin.pos q))) _
        (by rw [bsign_add_zero_left]; exact bsign_equiv_refl _)
        (bsign_equiv_trans _ _ _
          (bsign_add_congr _ _ _ _ (bsign_equiv_symm _ _ (bsign_add_neg_cancel xc)) (bsign_equiv_refl _))
          (bsign_equiv_trans _ _ _ hiso (bsign_add_neg_cancel xc)))
    exact bsign_pos_not_le_zero q (bsign_le_congr_both (bsign_equiv_refl _) hq0 (bsign_le_refl _))
  · -- `y - x ≈ +p` => `x + p ≈ y`!
    refine ⟨p, ?_⟩
    have hx : bsign_equiv (bsign_add (bsign_add y (bsign_neg x)) x)
                          (bsign_add (bsign_nonneg_of (BBin.pos p)) x) :=
      bsign_add_congr _ _ _ _ hp (bsign_equiv_refl x)
    rw [bsign_add_assoc y (bsign_neg x) x, bsign_add_comm (bsign_neg x) x,
        bsign_add_comm (bsign_nonneg_of (BBin.pos p)) x] at hx
    have hy : bsign_equiv (bsign_add y (bsign_add x (bsign_neg x))) y :=
      bsign_equiv_trans _ (bsign_add y bsign_zero) _
        (bsign_add_congr _ _ _ _ (bsign_equiv_refl y) (bsign_add_neg_cancel x))
        (by rw [bsign_add_zero_right]; exact bsign_equiv_refl y)
    exact bsign_equiv_symm _ _ (bsign_equiv_trans _ _ _ (bsign_equiv_symm _ _ hy) hx)
  · -- `y - x ≈ -p` contradicts `x*c <= y*c`!
    exfalso
    rcases h with ⟨q, hq⟩
    have hle : bsign_le x y := bsign_le_cancel_pos_right x y c ⟨BBin.pos q, hq⟩
    have hlt_yx : bsign_lt y x := by
      refine ⟨p, ?_⟩
      have hx1 : bsign_equiv (bsign_add (bsign_add y (bsign_neg x)) (bsign_add x (bsign_nonneg_of (BBin.pos p))))
                             (bsign_add (bsign_neg (bsign_nonneg_of (BBin.pos p))) (bsign_add x (bsign_nonneg_of (BBin.pos p)))) :=
        bsign_add_congr _ _ _ _ hn (bsign_equiv_refl _)
      have hlhs : bsign_equiv (bsign_add (bsign_add y (bsign_neg x)) (bsign_add x (bsign_nonneg_of (BBin.pos p))))
                              (bsign_add y (bsign_nonneg_of (BBin.pos p))) := by
        rw [bsign_add_assoc y (bsign_neg x) _, ← bsign_add_assoc (bsign_neg x) x _, bsign_add_comm (bsign_neg x) x,
            ← bsign_add_assoc y (bsign_add x (bsign_neg x)) _]
        exact bsign_equiv_trans _ (bsign_add (bsign_add y bsign_zero) (bsign_nonneg_of (BBin.pos p))) _
          (bsign_add_congr _ _ _ _ (bsign_add_congr _ _ _ _ (bsign_equiv_refl y) (bsign_add_neg_cancel x)) (bsign_equiv_refl _))
          (by rw [bsign_add_zero_right]; exact bsign_equiv_refl _)
      have hrhs : bsign_equiv (bsign_add (bsign_neg (bsign_nonneg_of (BBin.pos p))) (bsign_add x (bsign_nonneg_of (BBin.pos p)))) x := by
        rw [bsign_add_comm x (bsign_nonneg_of (BBin.pos p)), ← bsign_add_assoc, bsign_add_comm (bsign_neg _) _]
        exact bsign_equiv_trans _ (bsign_add bsign_zero x) _
          (bsign_add_congr _ _ _ _ (bsign_add_neg_cancel _) (bsign_equiv_refl x))
          (by rw [bsign_add_zero_left]; exact bsign_equiv_refl x)
      exact bsign_equiv_trans _ _ _ (bsign_equiv_symm _ _ hlhs) (bsign_equiv_trans _ _ _ hx1 hrhs)
    rcases bsign_le_lt_trans x y x hle hlt_yx with ⟨r, hr⟩
    have hiso : bsign_equiv (bsign_add (bsign_neg x) (bsign_add x (bsign_nonneg_of (BBin.pos r))))
                            (bsign_add (bsign_neg x) x) :=
      bsign_add_congr _ _ _ _ (bsign_equiv_refl _) hr
    rw [← bsign_add_assoc (bsign_neg x) x _, bsign_add_comm (bsign_neg x) x] at hiso
    have hr0 : bsign_equiv (bsign_nonneg_of (BBin.pos r)) bsign_zero :=
      bsign_equiv_trans _ (bsign_add bsign_zero (bsign_nonneg_of (BBin.pos r))) _
        (by rw [bsign_add_zero_left]; exact bsign_equiv_refl _)
        (bsign_equiv_trans _ _ _
          (bsign_add_congr _ _ _ _ (bsign_equiv_symm _ _ (bsign_add_neg_cancel x)) (bsign_equiv_refl _))
          (bsign_equiv_trans _ _ _ hiso (bsign_add_neg_cancel x)))
    exact bsign_pos_not_le_zero r (bsign_le_congr_both (bsign_equiv_refl _) hr0 (bsign_le_refl _))

theorem brat_le_lt_trans (q r s : BRat) (hqr : brat_le q r) (hrs : brat_lt r s) :
    brat_lt q s := by
  unfold brat_le at hqr
  unfold brat_lt at hrs ⊢
  have h1 := bsign_mul_nonneg_mono (BBin.pos s.den) _ _ hqr
  rcases hrs with ⟨p, hp⟩
  have h2 : bsign_lt (bsign_mul (bsign_nonneg_of (BBin.pos q.den)) (bsign_mul r.num (bpos_to_sign s.den)))
                     (bsign_mul (bsign_nonneg_of (BBin.pos q.den)) (bsign_mul s.num (bpos_to_sign r.den))) := by
    refine ⟨bpos_mul q.den p, ?_⟩
    have hm := bsign_mul_congr _ _ _ _ (bsign_equiv_refl (bsign_nonneg_of (BBin.pos q.den))) hp
    rw [bsign_mul_add_distrib, bsign_nonneg_mul] at hm
    exact hm
  have eq1L : bsign_mul (bsign_nonneg_of (BBin.pos s.den)) (bsign_mul q.num (bpos_to_sign r.den)) =
              bsign_mul (bsign_mul q.num (bpos_to_sign s.den)) (bpos_to_sign r.den) := by
    rw [← bpos_to_sign_eq_nonneg, bsign_mul_comm (bpos_to_sign s.den) _, bsign_mul_assoc q.num (bpos_to_sign r.den) (bpos_to_sign s.den),
        bsign_mul_comm (bpos_to_sign r.den) (bpos_to_sign s.den), ← bsign_mul_assoc]
  have eq1R : bsign_mul (bsign_nonneg_of (BBin.pos s.den)) (bsign_mul r.num (bpos_to_sign q.den)) =
              bsign_mul (bsign_nonneg_of (BBin.pos q.den)) (bsign_mul r.num (bpos_to_sign s.den)) := by
    rw [← bpos_to_sign_eq_nonneg, ← bpos_to_sign_eq_nonneg,
        bsign_mul_comm (bpos_to_sign s.den) _, bsign_mul_comm (bpos_to_sign q.den) _,
        bsign_mul_assoc r.num (bpos_to_sign q.den) (bpos_to_sign s.den),
        bsign_mul_comm (bpos_to_sign q.den) (bpos_to_sign s.den), ← bsign_mul_assoc]
  have eq2R : bsign_mul (bsign_nonneg_of (BBin.pos q.den)) (bsign_mul s.num (bpos_to_sign r.den)) =
              bsign_mul (bsign_mul s.num (bpos_to_sign q.den)) (bpos_to_sign r.den) := by
    rw [← bpos_to_sign_eq_nonneg, bsign_mul_comm (bpos_to_sign q.den) _, bsign_mul_assoc s.num (bpos_to_sign r.den) (bpos_to_sign q.den),
        bsign_mul_comm (bpos_to_sign r.den) (bpos_to_sign q.den), ← bsign_mul_assoc]
  rw [eq1L, eq1R] at h1
  rw [eq2R] at h2
  exact bsign_lt_cancel_pos_right _ _ r.den (bsign_le_lt_trans _ _ _ h1 h2)

theorem brat_lt_le_trans (q r s : BRat) (hqr : brat_lt q r) (hrs : brat_le r s) :
    brat_lt q s := by
  unfold brat_lt at hqr ⊢
  unfold brat_le at hrs
  rcases hqr with ⟨p, hp⟩
  have h1 : bsign_lt (bsign_mul (bsign_mul q.num (bpos_to_sign s.den)) (bpos_to_sign r.den))
                     (bsign_mul (bsign_nonneg_of (BBin.pos q.den)) (bsign_mul r.num (bpos_to_sign s.den))) := by
    refine ⟨bpos_mul s.den p, ?_⟩
    have hm := bsign_mul_congr _ _ _ _ (bsign_equiv_refl (bsign_nonneg_of (BBin.pos s.den))) hp
    rw [bsign_mul_add_distrib, bsign_nonneg_mul] at hm
    have eq1L : bsign_mul (bsign_nonneg_of (BBin.pos s.den)) (bsign_mul q.num (bpos_to_sign r.den)) =
                bsign_mul (bsign_mul q.num (bpos_to_sign s.den)) (bpos_to_sign r.den) := by
      rw [← bpos_to_sign_eq_nonneg, bsign_mul_comm (bpos_to_sign s.den) _, bsign_mul_assoc q.num (bpos_to_sign r.den) (bpos_to_sign s.den),
          bsign_mul_comm (bpos_to_sign r.den) (bpos_to_sign s.den), ← bsign_mul_assoc]
    have eq1R : bsign_mul (bsign_nonneg_of (BBin.pos s.den)) (bsign_mul r.num (bpos_to_sign q.den)) =
                bsign_mul (bsign_nonneg_of (BBin.pos q.den)) (bsign_mul r.num (bpos_to_sign s.den)) := by
      rw [← bpos_to_sign_eq_nonneg, ← bpos_to_sign_eq_nonneg,
          bsign_mul_comm (bpos_to_sign s.den) _, bsign_mul_comm (bpos_to_sign q.den) _,
          bsign_mul_assoc r.num (bpos_to_sign q.den) (bpos_to_sign s.den),
          bsign_mul_comm (bpos_to_sign q.den) (bpos_to_sign s.den), ← bsign_mul_assoc]
    rw [eq1L, eq1R] at hm
    exact hm
  have h2 := bsign_mul_nonneg_mono (BBin.pos q.den) _ _ hrs
  have eq2R : bsign_mul (bsign_nonneg_of (BBin.pos q.den)) (bsign_mul s.num (bpos_to_sign r.den)) =
              bsign_mul (bsign_mul s.num (bpos_to_sign q.den)) (bpos_to_sign r.den) := by
    rw [← bpos_to_sign_eq_nonneg, bsign_mul_comm (bpos_to_sign q.den) _, bsign_mul_assoc s.num (bpos_to_sign r.den) (bpos_to_sign q.den),
        bsign_mul_comm (bpos_to_sign r.den) (bpos_to_sign q.den), ← bsign_mul_assoc]
  rw [eq2R] at h2
  exact bsign_lt_cancel_pos_right _ _ r.den (bsign_lt_le_trans _ _ _ h1 h2)

-- Theorem 4A (`brobin_pass_verifier_sound`):
-- If `⟨N_lo, D_n⟩ <= rhs_n` and `sigma_n * D_n < N_lo`, then `⟨sigma_n, 1⟩ < rhs_n`!
theorem brobin_pass_verifier_sound
    (sigma_n N_lo : BSignPair) (D_n : BPos) (rhs_n : BRat)
    (h_enc : brat_le ⟨N_lo, D_n⟩ rhs_n)
    (h_chk : bsign_lt (bsign_mul sigma_n (bpos_to_sign D_n)) N_lo) :
    brat_lt ⟨sigma_n, BPos.one⟩ rhs_n := by
  have h_step : brat_lt ⟨sigma_n, BPos.one⟩ ⟨N_lo, D_n⟩ := by
    unfold brat_lt; dsimp only
    have h1 : bpos_to_sign BPos.one = bsign_one := rfl
    rw [h1, bsign_mul_one_right]
    exact h_chk
  exact brat_lt_le_trans _ _ _ h_step h_enc

-- Theorem 4B (`brobin_exception_verifier_sound`):
-- If `rhs_n <= ⟨N_hi, D_n⟩` and `N_hi < sigma_n * D_n`, then `rhs_n < ⟨sigma_n, 1⟩` (certified exception)!
theorem brobin_exception_verifier_sound
    (sigma_n N_hi : BSignPair) (D_n : BPos) (rhs_n : BRat)
    (h_enc : brat_le rhs_n ⟨N_hi, D_n⟩)
    (h_chk : bsign_lt N_hi (bsign_mul sigma_n (bpos_to_sign D_n))) :
    brat_lt rhs_n ⟨sigma_n, BPos.one⟩ := by
  have h_step : brat_lt ⟨N_hi, D_n⟩ ⟨sigma_n, BPos.one⟩ := by
    unfold brat_lt; dsimp only
    have h1 : bpos_to_sign BPos.one = bsign_one := rfl
    rw [h1, bsign_mul_one_right]
    exact h_chk
  exact brat_le_lt_trans _ _ _ h_enc h_step

-- Ground Coprime `σ_1` Multiplicativity & Certified Robin Exception Witnesses (`n = 2, 6, 12`)!
theorem bsigma1_coprime_mul_witnesses :
    bu_sigma1 bu_6 = bmul (bu_sigma1 bu_2) (bu_sigma1 bu_3) ∧
    bu_sigma1 bu_12 = bmul (bu_sigma1 bu_3) (bu_sigma1 bu_4) :=
  ⟨rfl, rfl⟩

-- Certified Robin exception witnesses (`σ_1(2) = 3 > 0`, `σ_1(6) = 12 > 7`, `σ_1(12) = 28 > 20`)!
theorem brobin_exception_n2_n6_n12_witnesses :
    bsign_lt bsign_zero (bsign_nonneg_of (bu_sigma1 bu_2)) ∧
    bsign_lt bs_seven (bsign_nonneg_of (bu_sigma1 bu_6)) ∧
    bsign_lt (bsign_nonneg_of (BBin.pos (BPos.x0 (BPos.x0 (BPos.x1 (BPos.x0 BPos.one))))))
             (bsign_nonneg_of (bu_sigma1 bu_12)) :=
  ⟨⟨bpos_three, rfl⟩,
   ⟨BPos.x1 (BPos.x0 BPos.one), rfl⟩,
   ⟨BPos.x0 (BPos.x0 (BPos.x0 BPos.one)), rfl⟩⟩

end SiliconBigBang
