/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CauchyHadamardFrobeniusReflect

/-!
# Verified Solutions (`cauchy-hadamard-frobenius-reflect`)
-/

namespace CauchyHadamardFrobeniusReflectChallenge

open CHReflect

theorem reflect_all_bitvec (e1 e2 : Expr) (c : Cert) (h : checkCert e1 e2 c = true) :
    ∀ (w : Nat) (env : Nat → BitVec w), evalBV w env e1 = evalBV w env e2 :=
  CHReflect.reflect_all_bitvec e1 e2 c h

theorem reflect_all_scales_and_widths (e1 e2 : Expr) (c : Cert)
    (hs1 : isLaneSafe e1 = true) (hs2 : isLaneSafe e2 = true)
    (h : checkCert e1 e2 c = true) :
    ∀ (r w : Nat) (env : Nat → BitVec w),
      evalBV w env (dilate r e1) = evalBV w env (dilate r e2) :=
  CHReflect.reflect_all_scales_and_widths e1 e2 c hs1 hs2 h

theorem binary_ito2_all_scales_widths :
    ∀ (r w : Nat) (a b : BitVec w),
      bvPr r a &&& bvPr r b =
      bvPr r (((a &&& bvPr r b) ^^^ (b &&& bvPr r a)) ^^^ (a &&& b)) :=
  CHReflect.binary_ito2_all_scales_widths 

theorem binary_ito_general_n (n r w : Nat) (hn : 1 ≤ n) (xs : Nat → BitVec w) :
    bvAndRange n (fun i => bvPr r (xs i)) =
    bvPr r (bvXorRange (2 ^ n - 1) (fun m =>
      bvAndRange n (fun i => if ((m + 1) >>> i) % 2 == 1 then xs i else bvPr r (xs i)))) :=
  CHReflect.binary_ito_general_n n r w hn xs

theorem self_scale_ladder_all_scales_widths :
    ∀ (r w : Nat) (a : BitVec w),
      bvPr r a &&& bvPr (r + 1) a =
      bvPr (r + 1) a ^^^ bvPr r (a &&& (bvPr r a ^^^ bvPr (r + 1) a)) :=
  CHReflect.self_scale_ladder_all_scales_widths 

theorem two_scale_ladder_all_scales_widths :
    ∀ (r w : Nat) (a : BitVec w),
      bvPr r a &&& bvPr (r + 2) a =
      bvPr r ((a &&& bvPr (r + 2) a) ^^^ ((a ^^^ bvPr r a) &&& bvPr r (bvPr (r + 1) a))) :=
  CHReflect.two_scale_ladder_all_scales_widths 

theorem residue_conv_split_all_r_w (r t w : Nat) (ht : t < 2 ^ r) (a b : BitVec w) :
    bvClmul a b &&& (bvE w r <<< t) =
    bvXorRange (2 ^ r) (fun u =>
      bvClmul (a &&& (bvE w r <<< u))
              (b &&& (bvE w r <<< ((t + 2 ^ r - u) % 2 ^ r)))) :=
  CHReflect.residue_conv_split_all_r_w r t w ht a b

theorem frob_hadamard_orthogonal_all (r s1 s2 w : Nat) (hne : s1 % 2 ^ r ≠ s2 % 2 ^ r)
    (a b : BitVec w) :
    (bvFrob r a <<< s1) &&& (bvFrob r b <<< s2) = 0 :=
  CHReflect.frob_hadamard_orthogonal_all r s1 s2 w hne a b

end CauchyHadamardFrobeniusReflectChallenge
