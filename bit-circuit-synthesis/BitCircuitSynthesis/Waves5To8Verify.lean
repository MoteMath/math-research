/-
  Pure-Silicon Mathematical "Big Bang" — Waves 5..8 Zero-Dependency Lean 4 Kernel Proofs
  (`Waves5To8Verify.lean`: Epochs 21..28 End-to-End Verification)

  NO Mathlib. NO built-in `Nat`, `Int`, `Rat`, `Matrix`, or `Bool` arithmetic used anywhere.
  Extends `BigBangScratchVerify` + `Epoch7PrimesVerify` + `Epoch10AllThreeVerify` + `Waves1To4Verify`
  strictly from Epoch-0 `BBit`, `BPos`, `BBin`, and `BSignPair`:

  1. Wave 5 (Epochs 21..22 — Divided-Power Jet Calculus, Jacobi Matrix-Dual Law,
     Hamilton's Quaternions `H` & Lie Algebra Jacobi Identity):
     - `BJet3`: Fundamental Theorem of Calculus `D(Int(F)) = F` & Picard `exp` fixed point `D(exp) = exp`,
     - `bmat2_dual_jacobi_at_id`: Universal Jacobi Derivative Identity `det(I + eps*A) ≈ 1 + tr(A)*eps`,
     - `BQuat`: Non-commutativity `i*j ≠ j*i` & Universal **Euler Four-Square Norm Multiplicativity**
       `N(q1 * q2) ≈ N(q1) * N(q2)` proved via Cayley-Dickson reduction to `BGauss`!
     - `bmat2_comm_f2_jacobi`: Universal Lie Bracket Jacobi Identity `[A,[B,C]] + [B,[C,A]] + [C,[A,B]] = 0`.
  2. Wave 6 (Epochs 23..24 — Walsh-Hadamard Transform, Convolution Diagonalization & Poisson Summation):
     - `bwalsh2_conv_diag`: Universal XOR Convolution Diagonalization `W(f * g) = W(f) . W(g)`,
     - `bwalsh2_poisson`: Exact Subgroup Poisson Summation `W(f)_0 + W(f)_1 ≈ 2 * f_0`,
     - `bwalsh2_invol`: Exact Walsh Involution `W(W(f)) ≈ (2*f_0, 2*f_1)`.
  3. Wave 7 (Epochs 25..26 — Projective Plane `P^2(F_2)` Fano Bezout Incidence):
     - `bfano_bezout_unique_intersection`: Every two distinct projective lines in `P^2(F_2)` meet in
       a UNIQUE projective point!
  4. Wave 8 (Epochs 27..28 — Polymorphic Cantor Diagonalization & Boolean Inclusion-Exclusion):
     - `cantor_diagonal_no_surjection`: Universal Cantor Theorem `∀ (α : Type) (f : α → (α → BBit)),
       ∃ D : α → BBit, ∀ x : α, f x ≠ D` (valid for ALL finite and infinite types `α`!),
     - `bbool2_inclusion_exclusion`: Universal Boolean Poset Mobius Inversion
       `G(1,1) - G(1,0) - G(0,1) + G(0,0) ≈ F(1,1)`.
-/

import BitCircuitSynthesis.BigBangScratchVerify
import BitCircuitSynthesis.Epoch7PrimesVerify
import BitCircuitSynthesis.Epoch10AllThreeVerify
import BitCircuitSynthesis.Waves1To4Verify

namespace SiliconBigBang

-- ============================================================================
-- PART I (Wave 5): Divided-Power Jet Calculus, Jacobi Law, Quaternions & Lie Brackets
-- ============================================================================

-- 1. Divided-Power Jet Series `BJet3` (`c0 + c1*t + c2*t^2/2! + c3*t^3/3!`)
structure BJet3 where
  c0 : BSignPair
  c1 : BSignPair
  c2 : BSignPair
  c3 : BSignPair
  deriving DecidableEq

def bjet3_deriv (F : BJet3) : BJet3 := ⟨F.c1, F.c2, F.c3, bsign_zero⟩
def bjet3_integ (F : BJet3) : BJet3 := ⟨bsign_zero, F.c0, F.c1, F.c2⟩

-- Fundamental Theorem of Calculus on Formal Jets: `D(Int(F))` recovers `(c0, c1, c2)` identically!
theorem bjet3_ftc_deriv_integ (F : BJet3) :
    (bjet3_deriv (bjet3_integ F)).c0 = F.c0 ∧
    (bjet3_deriv (bjet3_integ F)).c1 = F.c1 ∧
    (bjet3_deriv (bjet3_integ F)).c2 = F.c2 :=
  ⟨rfl, rfl, rfl⟩

-- Picard Exponential Fixed Point `exp(t) = 1 + t + t^2/2! + t^3/3!` satisfies `D(exp) = exp` on `0..2`!
def bjet3_exp : BJet3 := ⟨bsign_one, bsign_one, bsign_one, bsign_one⟩

theorem bjet3_exp_ode_fixed_point :
    (bjet3_deriv bjet3_exp).c0 = bjet3_exp.c0 ∧
    (bjet3_deriv bjet3_exp).c1 = bjet3_exp.c1 ∧
    (bjet3_deriv bjet3_exp).c2 = bjet3_exp.c2 :=
  ⟨rfl, rfl, rfl⟩

-- 2. Jacobi's Matrix-Dual Bridge (`Wave 2 x Wave 3`): `det(I + eps * A) ≈ 1 + tr(A) * eps`!
def bdual_equiv (x y : BDual) : Prop :=
  bsign_equiv x.val y.val ∧ bsign_equiv x.eps y.eps

def bdual_neg (x : BDual) : BDual := ⟨bsign_neg x.val, bsign_neg x.eps⟩

def bmat2_dual_id : BMat2 BDual :=
  ⟨⟨bsign_one, bsign_zero⟩, ⟨bsign_zero, bsign_zero⟩,
   ⟨bsign_zero, bsign_zero⟩, ⟨bsign_one, bsign_zero⟩⟩

def bmat2_dual_lift_eps (A : BMat2 BSignPair) : BMat2 BDual :=
  ⟨⟨bsign_zero, A.a00⟩, ⟨bsign_zero, A.a01⟩,
   ⟨bsign_zero, A.a10⟩, ⟨bsign_zero, A.a11⟩⟩

def bmat2_dual_add (M N : BMat2 BDual) : BMat2 BDual :=
  ⟨bdual_add M.a00 N.a00, bdual_add M.a01 N.a01,
   bdual_add M.a10 N.a10, bdual_add M.a11 N.a11⟩

def bmat2_dual_det (M : BMat2 BDual) : BDual :=
  bdual_add (bdual_mul M.a00 M.a11) (bdual_neg (bdual_mul M.a01 M.a10))

theorem bmat2_dual_jacobi_at_id (A : BMat2 BSignPair) :
    bdual_equiv
      (bmat2_dual_det (bmat2_dual_add bmat2_dual_id (bmat2_dual_lift_eps A)))
      ⟨bsign_one, bmat2_tr A⟩ := by
  unfold bdual_equiv bmat2_dual_det bmat2_dual_add bmat2_dual_id bmat2_dual_lift_eps
         bdual_add bdual_mul bdual_neg bmat2_tr
  dsimp only
  simp only [bsign_add_zero_left, bsign_add_zero_right,
             bsign_mul_zero_left, bsign_mul_zero_right,
             bsign_mul_one_left, bsign_mul_one_right]
  have hz : bsign_neg bsign_zero = bsign_zero := rfl
  rw [hz, bsign_add_zero_right, bsign_add_zero_right, bsign_add_comm A.a11 A.a00]
  exact ⟨bsign_equiv_refl _, bsign_equiv_refl _⟩

-- 3. Hamilton's Quaternions `BQuat` via Cayley-Dickson Pair `(z, w) in BGauss x BGauss`
--    & Universal Euler Four-Square Norm Multiplicativity `N(q1 * q2) ≈ N(q1) * N(q2)`!
def bgauss_add (z w : BGauss) : BGauss := ⟨bsign_add z.re w.re, bsign_add z.im w.im⟩
def bgauss_neg (z : BGauss)   : BGauss := ⟨bsign_neg z.re, bsign_neg z.im⟩
def bgauss_sub (z w : BGauss) : BGauss := bgauss_add z (bgauss_neg w)
def bgauss_conj (z : BGauss)  : BGauss := ⟨z.re, bsign_neg z.im⟩

theorem bgauss_norm_conj (z : BGauss) : bgauss_norm (bgauss_conj z) = bgauss_norm z := by
  unfold bgauss_norm bgauss_conj
  dsimp only
  rw [bsign_mul_neg_left, bsign_mul_neg_right, bsign_neg_invol]

structure BQuat where
  z : BGauss
  w : BGauss
  deriving DecidableEq

-- Cayley-Dickson multiplication: `(z1, w1) * (z2, w2) = (z1*z2 - conj(w2)*w1, w2*z1 + w1*conj(z2))`!
def bquat_mul (q1 q2 : BQuat) : BQuat :=
  ⟨bgauss_sub (bgauss_mul q1.z q2.z) (bgauss_mul (bgauss_conj q2.w) q1.w),
   bgauss_add (bgauss_mul q2.w q1.z) (bgauss_mul q1.w (bgauss_conj q2.z))⟩

def bquat_norm (q : BQuat) : BSignPair :=
  bsign_add (bgauss_norm q.z) (bgauss_norm q.w)

def bquat_i : BQuat := ⟨⟨bsign_zero, bsign_one⟩, ⟨bsign_zero, bsign_zero⟩⟩
def bquat_j : BQuat := ⟨⟨bsign_zero, bsign_zero⟩, ⟨bsign_one, bsign_zero⟩⟩

-- Non-Commutativity of Quaternions: `i * j = +k ≠ -k = j * i`!
theorem bquat_ij_ne_ji : bquat_mul bquat_i bquat_j ≠ bquat_mul bquat_j bquat_i := by
  intro h
  cases h

theorem bsign_quad_cancel_core (A M B C P D : BSignPair) :
    bsign_add (bsign_add (bsign_add A M) (bsign_add M B))
              (bsign_add (bsign_add C P) (bsign_add P D)) =
    bsign_add (bsign_add (bsign_add A B) (bsign_add C D))
              (bsign_add (bsign_add P M) (bsign_add P M)) := by
  rw [bsign_add_four_swap (bsign_add A M) (bsign_add M B) (bsign_add C P) (bsign_add P D)]
  rw [bsign_add_four_swap A M C P]
  rw [bsign_add_comm M B, bsign_add_comm P D]
  rw [bsign_add_four_swap B M D P]
  rw [bsign_add_comm M P]
  rw [bsign_add_four_swap (bsign_add A C) (bsign_add P M) (bsign_add B D) (bsign_add P M)]
  rw [bsign_add_four_swap A C B D]

theorem bgauss_parallelogram_cancel (U V U' V' : BGauss)
    (hdot : bsign_add (bsign_mul U'.re V'.re) (bsign_mul U'.im V'.im) =
            bsign_add (bsign_mul U.re V.re) (bsign_mul U.im V.im)) :
    bsign_equiv
      (bsign_add (bgauss_norm (bgauss_sub U V)) (bgauss_norm (bgauss_add U' V')))
      (bsign_add (bsign_add (bgauss_norm U) (bgauss_norm V))
                 (bsign_add (bgauss_norm U') (bgauss_norm V'))) := by
  unfold bgauss_norm bgauss_sub bgauss_add bgauss_neg
  dsimp only
  rw [bsign_add_four_swap
        (bsign_mul (bsign_add U.re (bsign_neg V.re)) (bsign_add U.re (bsign_neg V.re)))
        (bsign_mul (bsign_add U.im (bsign_neg V.im)) (bsign_add U.im (bsign_neg V.im)))
        (bsign_mul (bsign_add U'.re V'.re) (bsign_add U'.re V'.re))
        (bsign_mul (bsign_add U'.im V'.im) (bsign_add U'.im V'.im))]
  simp only [bsign_mul_add_distrib, bsign_mul_add_right,
             bsign_mul_neg_left, bsign_mul_neg_right, bsign_neg_add, bsign_neg_invol]
  rw [bsign_mul_comm V.re U.re, bsign_mul_comm V'.re U'.re]
  rw [bsign_mul_comm V.im U.im, bsign_mul_comm V'.im U'.im]
  rw [bsign_quad_cancel_core (bsign_mul U.re U.re) (bsign_neg (bsign_mul U.re V.re)) (bsign_mul V.re V.re)
                             (bsign_mul U'.re U'.re) (bsign_mul U'.re V'.re) (bsign_mul V'.re V'.re)]
  rw [bsign_quad_cancel_core (bsign_mul U.im U.im) (bsign_neg (bsign_mul U.im V.im)) (bsign_mul V.im V.im)
                             (bsign_mul U'.im U'.im) (bsign_mul U'.im V'.im) (bsign_mul V'.im V'.im)]
  rw [bsign_add_four_swap
        (bsign_add (bsign_add (bsign_mul U.re U.re) (bsign_mul V.re V.re))
                   (bsign_add (bsign_mul U'.re U'.re) (bsign_mul V'.re V'.re)))
        _
        (bsign_add (bsign_add (bsign_mul U.im U.im) (bsign_mul V.im V.im))
                   (bsign_add (bsign_mul U'.im U'.im) (bsign_mul V'.im V'.im)))
        _]
  have cross_eq :
      bsign_add
        (bsign_add (bsign_add (bsign_mul U'.re V'.re) (bsign_neg (bsign_mul U.re V.re)))
                   (bsign_add (bsign_mul U'.re V'.re) (bsign_neg (bsign_mul U.re V.re))))
        (bsign_add (bsign_add (bsign_mul U'.im V'.im) (bsign_neg (bsign_mul U.im V.im)))
                   (bsign_add (bsign_mul U'.im V'.im) (bsign_neg (bsign_mul U.im V.im)))) =
      bsign_add
        (bsign_add (bsign_add (bsign_mul U.re V.re) (bsign_mul U.im V.im))
                   (bsign_neg (bsign_add (bsign_mul U.re V.re) (bsign_mul U.im V.im))))
        (bsign_add (bsign_add (bsign_mul U.re V.re) (bsign_mul U.im V.im))
                   (bsign_neg (bsign_add (bsign_mul U.re V.re) (bsign_mul U.im V.im)))) := by
    rw [bsign_add_four_swap
          (bsign_add (bsign_mul U'.re V'.re) (bsign_neg (bsign_mul U.re V.re)))
          (bsign_add (bsign_mul U'.re V'.re) (bsign_neg (bsign_mul U.re V.re)))
          (bsign_add (bsign_mul U'.im V'.im) (bsign_neg (bsign_mul U.im V.im)))
          (bsign_add (bsign_mul U'.im V'.im) (bsign_neg (bsign_mul U.im V.im)))]
    rw [bsign_add_four_swap (bsign_mul U'.re V'.re) (bsign_neg (bsign_mul U.re V.re))
                            (bsign_mul U'.im V'.im) (bsign_neg (bsign_mul U.im V.im))]
    rw [hdot, ← bsign_neg_add]
  rw [cross_eq]
  have rear_norms :
      bsign_add
        (bsign_add (bsign_add (bsign_mul U.re U.re) (bsign_mul V.re V.re))
                   (bsign_add (bsign_mul U'.re U'.re) (bsign_mul V'.re V'.re)))
        (bsign_add (bsign_add (bsign_mul U.im U.im) (bsign_mul V.im V.im))
                   (bsign_add (bsign_mul U'.im U'.im) (bsign_mul V'.im V'.im))) =
      bsign_add
        (bsign_add (bsign_add (bsign_mul U.re U.re) (bsign_mul U.im U.im))
                   (bsign_add (bsign_mul V.re V.re) (bsign_mul V.im V.im)))
        (bsign_add (bsign_add (bsign_mul U'.re U'.re) (bsign_mul U'.im U'.im))
                   (bsign_add (bsign_mul V'.re V'.re) (bsign_mul V'.im V'.im))) := by
    rw [bsign_add_four_swap
          (bsign_add (bsign_mul U.re U.re) (bsign_mul V.re V.re))
          (bsign_add (bsign_mul U'.re U'.re) (bsign_mul V'.re V'.re))
          (bsign_add (bsign_mul U.im U.im) (bsign_mul V.im V.im))
          (bsign_add (bsign_mul U'.im U'.im) (bsign_mul V'.im V'.im))]
    rw [bsign_add_four_swap (bsign_mul U.re U.re) (bsign_mul V.re V.re)
                            (bsign_mul U.im U.im) (bsign_mul V.im V.im)]
    rw [bsign_add_four_swap (bsign_mul U'.re U'.re) (bsign_mul V'.re V'.re)
                            (bsign_mul U'.im U'.im) (bsign_mul V'.im V'.im)]
  rw [rear_norms]
  exact bsign_sub_two_pairs_cancel _ _ _

theorem bgauss_conj_invol (z : BGauss) : bgauss_conj (bgauss_conj z) = z := by
  cases z
  unfold bgauss_conj
  dsimp only
  rw [bsign_neg_invol]

theorem bgauss_mul_comm (x y : BGauss) : bgauss_mul x y = bgauss_mul y x := by
  unfold bgauss_mul
  rw [bsign_mul_comm x.re y.re, bsign_mul_comm x.im y.im]
  rw [bsign_mul_comm x.re y.im, bsign_mul_comm x.im y.re]
  rw [bsign_add_comm (bsign_mul y.im x.re)]

theorem bgauss_conj_mul (x y : BGauss) :
    bgauss_conj (bgauss_mul x y) = bgauss_mul (bgauss_conj x) (bgauss_conj y) := by
  unfold bgauss_conj bgauss_mul
  dsimp only
  simp only [bsign_mul_neg_left, bsign_mul_neg_right, bsign_neg_invol, bsign_neg_add]

theorem bgauss_mul_assoc (x y z : BGauss) :
    bgauss_mul (bgauss_mul x y) z = bgauss_mul x (bgauss_mul y z) := by
  unfold bgauss_mul
  dsimp only
  simp only [bsign_mul_add_distrib, bsign_mul_add_right,
             bsign_mul_neg_left, bsign_mul_neg_right, bsign_neg_add, bsign_mul_assoc]
  rw [bsign_add_four_swap (bsign_mul x.re (bsign_mul y.re z.re))
                          (bsign_neg (bsign_mul x.im (bsign_mul y.im z.re)))
                          (bsign_neg (bsign_mul x.re (bsign_mul y.im z.im)))
                          (bsign_neg (bsign_mul x.im (bsign_mul y.re z.im)))]
  rw [bsign_add_comm (bsign_neg (bsign_mul x.im (bsign_mul y.im z.re)))
                     (bsign_neg (bsign_mul x.im (bsign_mul y.re z.im)))]
  rw [bsign_add_four_swap (bsign_mul x.re (bsign_mul y.re z.im))
                          (bsign_neg (bsign_mul x.im (bsign_mul y.im z.im)))
                          (bsign_mul x.re (bsign_mul y.im z.re))
                          (bsign_mul x.im (bsign_mul y.re z.re))]
  rw [bsign_add_comm (bsign_neg (bsign_mul x.im (bsign_mul y.im z.im)))
                     (bsign_mul x.im (bsign_mul y.re z.re))]

theorem bgauss_dot_eq_re_mul_conj (A B : BGauss) :
    bsign_add (bsign_mul A.re B.re) (bsign_mul A.im B.im) =
    (bgauss_mul A (bgauss_conj B)).re := by
  unfold bgauss_mul bgauss_conj
  dsimp only
  rw [bsign_mul_neg_right, bsign_neg_invol]

theorem bgauss_cayley_dot_eq (z1 w1 z2 w2 : BGauss) :
    bsign_add (bsign_mul (bgauss_mul w2 z1).re (bgauss_mul w1 (bgauss_conj z2)).re)
              (bsign_mul (bgauss_mul w2 z1).im (bgauss_mul w1 (bgauss_conj z2)).im) =
    bsign_add (bsign_mul (bgauss_mul z1 z2).re (bgauss_mul (bgauss_conj w2) w1).re)
              (bsign_mul (bgauss_mul z1 z2).im (bgauss_mul (bgauss_conj w2) w1).im) := by
  rw [bgauss_dot_eq_re_mul_conj (bgauss_mul w2 z1) (bgauss_mul w1 (bgauss_conj z2))]
  rw [bgauss_dot_eq_re_mul_conj (bgauss_mul z1 z2) (bgauss_mul (bgauss_conj w2) w1)]
  rw [bgauss_conj_mul, bgauss_conj_mul, bgauss_conj_invol, bgauss_conj_invol]
  have h4 : bgauss_mul (bgauss_mul w2 z1) (bgauss_mul (bgauss_conj w1) z2) =
            bgauss_mul (bgauss_mul z1 z2) (bgauss_mul w2 (bgauss_conj w1)) := by
    rw [bgauss_mul_comm w2 z1, bgauss_mul_comm (bgauss_conj w1) z2]
    rw [bgauss_mul_assoc z1 w2 (bgauss_mul z2 (bgauss_conj w1))]
    rw [← bgauss_mul_assoc w2 z2 (bgauss_conj w1), bgauss_mul_comm w2 z2]
    rw [bgauss_mul_assoc z2 w2 (bgauss_conj w1)]
    rw [← bgauss_mul_assoc z1 z2 (bgauss_mul w2 (bgauss_conj w1))]
  rw [h4]

theorem bsign_foil_rearrange (A D C B : BSignPair) :
    bsign_add (bsign_add A D) (bsign_add C B) =
    bsign_add (bsign_add A B) (bsign_add C D) := by
  rw [bsign_add_comm C B, bsign_add_four_swap A D B C, bsign_add_comm D C]

-- UNIVERSAL EULER FOUR-SQUARE NORM MULTIPLICATIVITY: `N(q1 * q2) ≈ N(q1) * N(q2)` for ALL `q1, q2 in BQuat`!
theorem bquat_euler_four_square_norm (q1 q2 : BQuat) :
    bsign_equiv (bquat_norm (bquat_mul q1 q2)) (bsign_mul (bquat_norm q1) (bquat_norm q2)) := by
  unfold bquat_norm bquat_mul
  dsimp only
  apply bsign_equiv_trans _
    (bsign_add (bsign_add (bgauss_norm (bgauss_mul q1.z q2.z))
                          (bgauss_norm (bgauss_mul (bgauss_conj q2.w) q1.w)))
               (bsign_add (bgauss_norm (bgauss_mul q2.w q1.z))
                          (bgauss_norm (bgauss_mul q1.w (bgauss_conj q2.z))))) _
  · exact bgauss_parallelogram_cancel _ _ _ _ (bgauss_cayley_dot_eq q1.z q1.w q2.z q2.w)
  · have h1 := bgauss_norm_mul q1.z q2.z
    have h2 := bgauss_norm_mul (bgauss_conj q2.w) q1.w
    rw [bgauss_norm_conj, bsign_mul_comm (bgauss_norm q2.w) (bgauss_norm q1.w)] at h2
    have h3 := bgauss_norm_mul q2.w q1.z
    rw [bsign_mul_comm (bgauss_norm q2.w) (bgauss_norm q1.z)] at h3
    have h4 := bgauss_norm_mul q1.w (bgauss_conj q2.z)
    rw [bgauss_norm_conj] at h4
    apply bsign_equiv_trans _
      (bsign_add (bsign_add (bsign_mul (bgauss_norm q1.z) (bgauss_norm q2.z))
                            (bsign_mul (bgauss_norm q1.w) (bgauss_norm q2.w)))
                 (bsign_add (bsign_mul (bgauss_norm q1.z) (bgauss_norm q2.w))
                            (bsign_mul (bgauss_norm q1.w) (bgauss_norm q2.z)))) _
    · exact bsign_add_congr _ _ _ _ (bsign_add_congr _ _ _ _ h1 h2) (bsign_add_congr _ _ _ _ h3 h4)
    · simp only [bsign_mul_add_distrib, bsign_mul_add_right]
      rw [bsign_foil_rearrange
            (bsign_mul (bgauss_norm q1.z) (bgauss_norm q2.z))
            (bsign_mul (bgauss_norm q1.w) (bgauss_norm q2.w))
            (bsign_mul (bgauss_norm q1.z) (bgauss_norm q2.w))
            (bsign_mul (bgauss_norm q1.w) (bgauss_norm q2.z))]
      exact bsign_equiv_refl _

-- 4. Lie Bracket Commutator `[A, B] = AB + BA` on `M_2(F_2)` & Universal Jacobi Identity!
def bmat2_add_f2 (A B : BMat2 BBit) : BMat2 BBit :=
  ⟨bxor A.a00 B.a00, bxor A.a01 B.a01, bxor A.a10 B.a10, bxor A.a11 B.a11⟩

def bmat2_zero_f2 : BMat2 BBit := ⟨BBit.b0, BBit.b0, BBit.b0, BBit.b0⟩

def bmat2_lie_f2 (A B : BMat2 BBit) : BMat2 BBit :=
  bmat2_add_f2 (bmat2_mul_f2 A B) (bmat2_mul_f2 B A)

theorem bmat2_lie_f2_self_zero (A : BMat2 BBit) :
    bmat2_lie_f2 A A = bmat2_zero_f2 := by
  rcases A with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem bmat2_mul_f2_assoc (A B C : BMat2 BBit) :
    bmat2_mul_f2 (bmat2_mul_f2 A B) C = bmat2_mul_f2 A (bmat2_mul_f2 B C) := by
  rcases A with ⟨a0, a1, a2, a3⟩
  rcases B with ⟨u0, u1, u2, u3⟩
  rcases C with ⟨c0, c1, c2, c3⟩
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;>
  cases u0 <;> cases u1 <;> cases u2 <;> cases u3 <;>
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> rfl

theorem bmat2_mul_f2_distrib_left (A B C : BMat2 BBit) :
    bmat2_mul_f2 A (bmat2_add_f2 B C) = bmat2_add_f2 (bmat2_mul_f2 A B) (bmat2_mul_f2 A C) := by
  rcases A with ⟨a0, a1, a2, a3⟩
  rcases B with ⟨u0, u1, u2, u3⟩
  rcases C with ⟨c0, c1, c2, c3⟩
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;>
  cases u0 <;> cases u1 <;> cases u2 <;> cases u3 <;>
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> rfl

theorem bmat2_mul_f2_distrib_right (A B C : BMat2 BBit) :
    bmat2_mul_f2 (bmat2_add_f2 A B) C = bmat2_add_f2 (bmat2_mul_f2 A C) (bmat2_mul_f2 B C) := by
  rcases A with ⟨a0, a1, a2, a3⟩
  rcases B with ⟨u0, u1, u2, u3⟩
  rcases C with ⟨c0, c1, c2, c3⟩
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;>
  cases u0 <;> cases u1 <;> cases u2 <;> cases u3 <;>
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> rfl

theorem bxor_jacobi12 (u v w x y z : BBit) :
    bxor (bxor (bxor (bxor u v) (bxor w z)) (bxor (bxor w x) (bxor y v)))
         (bxor (bxor y z) (bxor u x)) = BBit.b0 := by
  cases u <;> cases v <;> cases w <;> cases x <;> cases y <;> cases z <;> rfl

-- Universal Lie Jacobi Identity `[A,[B,C]] + [B,[C,A]] + [C,[A,B]] = 0`!
theorem bmat2_comm_f2_jacobi (A B C : BMat2 BBit) :
    bmat2_add_f2 (bmat2_add_f2 (bmat2_lie_f2 A (bmat2_lie_f2 B C))
                               (bmat2_lie_f2 B (bmat2_lie_f2 C A)))
                 (bmat2_lie_f2 C (bmat2_lie_f2 A B)) = bmat2_zero_f2 := by
  unfold bmat2_lie_f2
  simp only [bmat2_mul_f2_distrib_left, bmat2_mul_f2_distrib_right, bmat2_mul_f2_assoc]
  unfold bmat2_add_f2 bmat2_zero_f2
  dsimp only
  rw [bxor_jacobi12, bxor_jacobi12, bxor_jacobi12, bxor_jacobi12]

-- ============================================================================
-- PART II (Wave 6): Walsh-Hadamard Transform, Convolution Diagonalization & Poisson
-- ============================================================================

structure BFunc2 where
  v0 : BSignPair
  v1 : BSignPair
  deriving DecidableEq

def bfunc2_equiv (f g : BFunc2) : Prop :=
  bsign_equiv f.v0 g.v0 ∧ bsign_equiv f.v1 g.v1

-- XOR Convolution `(f * g)_0 = f0*g0 + f1*g1`, `(f * g)_1 = f0*g1 + f1*g0`!
def bxor_conv2 (f g : BFunc2) : BFunc2 :=
  ⟨bsign_add (bsign_mul f.v0 g.v0) (bsign_mul f.v1 g.v1),
   bsign_add (bsign_mul f.v0 g.v1) (bsign_mul f.v1 g.v0)⟩

-- Walsh-Hadamard Transform `W(f) = (f0 + f1, f0 - f1)`!
def bwalsh2 (f : BFunc2) : BFunc2 :=
  ⟨bsign_add f.v0 f.v1, bsign_add f.v0 (bsign_neg f.v1)⟩

def bfunc2_ptwise_mul (f g : BFunc2) : BFunc2 :=
  ⟨bsign_mul f.v0 g.v0, bsign_mul f.v1 g.v1⟩

-- Universal Walsh Convolution Diagonalization Theorem: `W(f *_xor g) = W(f) . W(g)`!
theorem bwalsh2_conv_diag (f g : BFunc2) :
    bwalsh2 (bxor_conv2 f g) = bfunc2_ptwise_mul (bwalsh2 f) (bwalsh2 g) := by
  unfold bwalsh2 bxor_conv2 bfunc2_ptwise_mul
  dsimp only
  simp only [bsign_mul_add_distrib, bsign_mul_add_right,
             bsign_mul_neg_left, bsign_mul_neg_right, bsign_neg_invol, bsign_neg_add]
  rw [bsign_foil_rearrange (bsign_mul f.v0 g.v0) (bsign_mul f.v1 g.v1)
                           (bsign_mul f.v0 g.v1) (bsign_mul f.v1 g.v0)]
  rw [bsign_foil_rearrange (bsign_mul f.v0 g.v0) (bsign_mul f.v1 g.v1)
                           (bsign_neg (bsign_mul f.v0 g.v1)) (bsign_neg (bsign_mul f.v1 g.v0))]

-- Universal Subgroup Poisson Summation (`H = {0}`, `H^perp = F_2`): `W(f)_0 + W(f)_1 ≈ 2 * f_0`!
theorem bwalsh2_poisson (f : BFunc2) :
    bsign_equiv (bsign_add (bwalsh2 f).v0 (bwalsh2 f).v1) (bsign_add f.v0 f.v0) := by
  unfold bwalsh2
  dsimp only
  rw [bsign_add_four_swap f.v0 f.v1 f.v0 (bsign_neg f.v1)]
  exact bsign_sub_pair_cancel (bsign_add f.v0 f.v0) f.v1

-- Universal Walsh Involution: `W(W(f)) ≈ (2 * f_0, 2 * f_1)`!
theorem bwalsh2_invol (f : BFunc2) :
    bfunc2_equiv (bwalsh2 (bwalsh2 f)) ⟨bsign_add f.v0 f.v0, bsign_add f.v1 f.v1⟩ := by
  refine ⟨bwalsh2_poisson f, ?_⟩
  unfold bwalsh2
  dsimp only
  rw [bsign_neg_add, bsign_neg_invol]
  rw [bsign_add_four_swap f.v0 f.v1 (bsign_neg f.v0) f.v1]
  rw [bsign_add_comm (bsign_add f.v0 (bsign_neg f.v0)) (bsign_add f.v1 f.v1)]
  exact bsign_sub_pair_cancel (bsign_add f.v1 f.v1) f.v0

-- ============================================================================
-- PART III (Wave 7): Projective Plane `P^2(F_2)` Fano Bezout Incidence Theorem
-- ============================================================================

inductive BFanoPt : Type where
  | p001 | p010 | p011 | p100 | p101 | p110 | p111
  deriving DecidableEq

def bfano_coords : BFanoPt → BBit × BBit × BBit
  | BFanoPt.p001 => (BBit.b0, BBit.b0, BBit.b1)
  | BFanoPt.p010 => (BBit.b0, BBit.b1, BBit.b0)
  | BFanoPt.p011 => (BBit.b0, BBit.b1, BBit.b1)
  | BFanoPt.p100 => (BBit.b1, BBit.b0, BBit.b0)
  | BFanoPt.p101 => (BBit.b1, BBit.b0, BBit.b1)
  | BFanoPt.p110 => (BBit.b1, BBit.b1, BBit.b0)
  | BFanoPt.p111 => (BBit.b1, BBit.b1, BBit.b1)

def bfano_dot (L P : BFanoPt) : BBit :=
  let (l0, l1, l2) := bfano_coords L
  let (p0, p1, p2) := bfano_coords P
  bxor (bxor (band l0 p0) (band l1 p1)) (band l2 p2)

def bfano_on_line (L P : BFanoPt) : Prop :=
  bfano_dot L P = BBit.b0

-- Constructive Projective Cross-Product `L1 x L2` over `F_2` (`L1 ⊕ L2` in `F_2^3 \ {0}`? Wait:
-- in `P^2(F_2)`, the 3D cross product `(y1*z2 ⊕ z1*y2, z1*x2 ⊕ x1*z2, x1*y2 ⊕ y1*x2)` gives the UNIQUE intersection point!)
def bfano_meet (L1 L2 : BFanoPt) : BFanoPt :=
  let (x1, y1, z1) := bfano_coords L1
  let (x2, y2, z2) := bfano_coords L2
  let cx := bxor (band y1 z2) (band z1 y2)
  let cy := bxor (band z1 x2) (band x1 z2)
  let cz := bxor (band x1 y2) (band y1 x2)
  match cx, cy, cz with
  | BBit.b0, BBit.b0, _       => BFanoPt.p001
  | BBit.b0, BBit.b1, BBit.b0 => BFanoPt.p010
  | BBit.b0, BBit.b1, BBit.b1 => BFanoPt.p011
  | BBit.b1, BBit.b0, BBit.b0 => BFanoPt.p100
  | BBit.b1, BBit.b0, BBit.b1 => BFanoPt.p101
  | BBit.b1, BBit.b1, BBit.b0 => BFanoPt.p110
  | BBit.b1, BBit.b1, BBit.b1 => BFanoPt.p111

-- Universal Projective Bezout Theorem on `P^2(F_2)`:
-- Every two distinct projective lines `L1 ≠ L2` intersect in the UNIQUE point `bfano_meet L1 L2`!
theorem bfano_bezout_unique_intersection (L1 L2 : BFanoPt) (hne : L1 ≠ L2) :
    (bfano_on_line L1 (bfano_meet L1 L2) ∧ bfano_on_line L2 (bfano_meet L1 L2)) ∧
    (∀ Q : BFanoPt, bfano_on_line L1 Q → bfano_on_line L2 Q → Q = bfano_meet L1 L2) := by
  refine ⟨?_, ?_⟩
  · cases L1 <;> cases L2 <;> first | exact absurd rfl hne | exact ⟨rfl, rfl⟩
  · intro Q
    cases L1 <;> cases L2 <;> cases Q
    all_goals (try exact fun _ _ => absurd rfl hne)
    all_goals (try exact fun _ _ => rfl)
    all_goals (intro h1 h2; first | (cases h1; done) | (cases h2; done))

-- ============================================================================
-- PART IV (Wave 8): Polymorphic Cantor Diagonal Theorem & Poset Inclusion-Exclusion
-- ============================================================================

-- 1. Universal Polymorphic Cantor Diagonal Theorem (`TAG_CANTOR_POW`)
--    Holds for EVERY type `α : Type` (finite OR infinite)!
def bcantor_diag {α : Type} (f : α → (α → BBit)) (x : α) : BBit :=
  bnot (f x x)

theorem bbit_bnot_ne_self (b : BBit) : bnot b ≠ b := by
  cases b <;> intro h <;> cases h

theorem cantor_diagonal_no_surjection {α : Type} (f : α → (α → BBit)) :
    ∃ D : α → BBit, ∀ x : α, f x ≠ D := by
  refine ⟨bcantor_diag f, fun x hx => ?_⟩
  have hxx : f x x = bcantor_diag f x := congrFun hx x
  exact bbit_bnot_ne_self (f x x) hxx.symm

-- 2. Universal Boolean Poset `B_2` Inclusion-Exclusion Mobius Inversion (`TAG_POSET_MOBIUS`)!
theorem bbool2_inclusion_exclusion (f00 f10 f01 f11 : BSignPair) :
    bsign_equiv
      (bsign_add
        (bsign_add (bsign_add (bsign_add f00 f10) (bsign_add f01 f11))
                   (bsign_neg (bsign_add f00 f10)))
        (bsign_add (bsign_neg (bsign_add f00 f01)) f00))
      f11 := by
  have hL : bsign_equiv
      (bsign_add (bsign_add (bsign_add f00 f10) (bsign_add f01 f11))
                 (bsign_neg (bsign_add f00 f10)))
      (bsign_add f01 f11) := by
    rw [bsign_add_comm (bsign_add f00 f10) (bsign_add f01 f11)]
    rw [bsign_add_assoc (bsign_add f01 f11) (bsign_add f00 f10) (bsign_neg (bsign_add f00 f10))]
    exact bsign_sub_pair_cancel (bsign_add f01 f11) (bsign_add f00 f10)
  have hR : bsign_equiv
      (bsign_add (bsign_neg (bsign_add f00 f01)) f00)
      (bsign_neg f01) := by
    rw [bsign_neg_add f00 f01, bsign_add_comm (bsign_neg f00) (bsign_neg f01)]
    rw [bsign_add_assoc (bsign_neg f01) (bsign_neg f00) f00, bsign_add_comm (bsign_neg f00) f00]
    exact bsign_sub_pair_cancel (bsign_neg f01) f00
  apply bsign_equiv_trans _ (bsign_add (bsign_add f01 f11) (bsign_neg f01)) _
  · exact bsign_add_congr _ _ _ _ hL hR
  · rw [bsign_add_comm f01 f11, bsign_add_assoc f11 f01 (bsign_neg f01)]
    exact bsign_sub_pair_cancel f11 f01
