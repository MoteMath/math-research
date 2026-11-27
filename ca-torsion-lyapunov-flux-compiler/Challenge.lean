/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CaTorsionLyapunovFluxCompiler.Defs

/-!
# Trusted Challenge Statements (`ca-torsion-lyapunov-flux-compiler`)

Eight universally quantified laws for one-dimensional binary cellular automata on periodic
rings `BitVec w` of every length `w ≥ 1`: an exact conserved motif count, linear-time
fixed-point termination with global acyclicity, rigid traveling-wave locking, a coupled
conservative-dissipative law, period-2 blinker convergence of ECA rule 108, and two pure
torsion conservation laws (mod 3 and mod 2) that have no integer lift.
-/

namespace CaTorsionLyapunovFluxCompilerChallenge

open CAFluxCompiler

/-- Theorem 1 (exact conserved `101`-motif count): the nonlinear `k = 4` rule `0xac8c`
conserves the number of cyclic `101` windows on every ring and at every time. -/
theorem thm_pat101_conservation_0xac8c {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential 3 cert_pat101_0xac8c.phi (caIter 4 1 0xac8c t x) =
    ringPotential 3 cert_pat101_0xac8c.phi x := by
  sorry

/-- Theorem 2 (linear-time fixed-point termination): the nonlinear non-monotone `k = 4`
rule `0x2c48` reaches an exact fixed point within `4 * w` steps on every ring of length `w`. -/
theorem thm_strict_fp_termination_0x2c48 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    caStep 4 1 0x2c48 (caIter 4 1 0x2c48 (4 * w) x) = caIter 4 1 0x2c48 (4 * w) x := by
  sorry

/-- Theorem 3 (global acyclicity): rule `0x2c48` has no periodic orbit of period `P ≥ 1`
other than a fixed point, on any ring of any length. -/
theorem thm_global_acyclicity_0x2c48 {w : Nat} (hw : 0 < w) (x : BitVec w)
    (P : Nat) (hP : 1 ≤ P) (hcyc : caIter 4 1 0x2c48 P x = x) :
    caStep 4 1 0x2c48 x = x := by
  sorry

/-- Theorem 4 (traveling-wave locking): under rule 152 every configuration on every ring of
length `w` locks into a rigid velocity-1 traveling wave within `3 * w` steps. -/
theorem thm_travelingWave_locking_rule152 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    caStep 3 1 152 (caIter 3 1 152 (3 * w) x) = ringRot 1 (caIter 3 1 152 (3 * w) x) := by
  sorry

/-- Theorem 5 (microcanonical law): for the `k = 4` rule `0xf0e0`, the state `T ^ w x` is
simultaneously a rigid velocity-1 traveling wave and has the same number of `11` dominoes as `x`. -/
theorem thm_microcanonical_0xf0e0 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    let xStar := caIter 4 1 0xf0e0 w x
    caStep 4 1 0xf0e0 xStar = ringRot 1 xStar ∧
    ringPotential 2 cert_micro_cons_0xf0e0.phi xStar =
    ringPotential 2 cert_micro_cons_0xf0e0.phi x := by
  sorry

/-- Theorem 6 (period-2 blinker convergence): ECA rule 108 reaches a configuration `y` with
`T (T y) = y` within `2 * w` steps on every ring of length `w`. -/
theorem thm_blinker_convergence_rule108 {w : Nat} (hw : 0 < w) (x : BitVec w) :
    let y := caIter 3 1 108 (2 * w) x
    caStep 3 1 108 (caStep 3 1 108 y) = y := by
  sorry

/-- Theorem 7 (pure `Z / 3` torsion conservation): the `k = 4` rule `0xb0f0` conserves
`#1 + #11` modulo 3 on every ring at every time. -/
theorem thm_mod3_torsion_0xb0f0 {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential 2 cert_mod3_0xb0f0.phi (caIter 4 1 0xb0f0 t x) % 3 =
    ringPotential 2 cert_mod3_0xb0f0.phi x % 3 := by
  sorry

/-- Theorem 8 (pure `Z / 2` torsion conservation): the `k = 4` rule `0x83bc` conserves
the parity of the number of `1` and `11` windows on every ring at every time. -/
theorem thm_mod2_torsion_0x83bc {w : Nat} (hw : 0 < w) (x : BitVec w) (t : Nat) :
    ringPotential 2 cert_mod2_0x83bc.phi (caIter 4 1 0x83bc t x) % 2 =
    ringPotential 2 cert_mod2_0x83bc.phi x % 2 := by
  sorry

end CaTorsionLyapunovFluxCompilerChallenge
