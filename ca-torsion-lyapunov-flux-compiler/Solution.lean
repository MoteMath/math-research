/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CaTorsionLyapunovFluxCompiler

/-!
# Verified Solutions (`ca-torsion-lyapunov-flux-compiler`)
-/

namespace CaTorsionLyapunovFluxCompilerChallenge

open CAFluxCompiler

theorem thm_pat101_conservation_0xac8c {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential 3 cert_pat101_0xac8c.phi (caIter 4 1 0xac8c t x) =
    ringPotential 3 cert_pat101_0xac8c.phi x :=
  CAFluxCompiler.thm_pat101_conservation_0xac8c hw x t

theorem thm_strict_fp_termination_0x2c48 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    caStep 4 1 0x2c48 (caIter 4 1 0x2c48 (4 * w) x) = caIter 4 1 0x2c48 (4 * w) x :=
  CAFluxCompiler.thm_strict_fp_termination_0x2c48 hw x

theorem thm_global_acyclicity_0x2c48 {w : Nat} (hw : 0 < w) (x : BitVec w)
    (P : Nat) (hP : 1 ≤ P) (hcyc : caIter 4 1 0x2c48 P x = x) :
    caStep 4 1 0x2c48 x = x :=
  CAFluxCompiler.thm_global_acyclicity_0x2c48 hw x P hP hcyc

theorem thm_travelingWave_locking_rule152 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    caStep 3 1 152 (caIter 3 1 152 (3 * w) x) = ringRot 1 (caIter 3 1 152 (3 * w) x) :=
  CAFluxCompiler.thm_travelingWave_locking_rule152 hw x

theorem thm_microcanonical_0xf0e0 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    let xStar := caIter 4 1 0xf0e0 w x
    caStep 4 1 0xf0e0 xStar = ringRot 1 xStar ∧
    ringPotential 2 cert_micro_cons_0xf0e0.phi xStar =
    ringPotential 2 cert_micro_cons_0xf0e0.phi x :=
  CAFluxCompiler.thm_microcanonical_0xf0e0 hw x

theorem thm_blinker_convergence_rule108 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    let y := caIter 3 1 108 (2 * w) x
    caStep 3 1 108 (caStep 3 1 108 y) = y :=
  CAFluxCompiler.thm_blinker_convergence_rule108 hw x

theorem thm_mod3_torsion_0xb0f0 {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential 2 cert_mod3_0xb0f0.phi (caIter 4 1 0xb0f0 t x) % 3 =
    ringPotential 2 cert_mod3_0xb0f0.phi x % 3 :=
  CAFluxCompiler.thm_mod3_torsion_0xb0f0 hw x t

theorem thm_mod2_torsion_0x83bc {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential 2 cert_mod2_0x83bc.phi (caIter 4 1 0x83bc t x) % 2 =
    ringPotential 2 cert_mod2_0x83bc.phi x % 2 :=
  CAFluxCompiler.thm_mod2_torsion_0x83bc hw x t

end CaTorsionLyapunovFluxCompilerChallenge
