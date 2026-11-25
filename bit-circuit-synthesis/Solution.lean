/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitCircuitSynthesis

/-!
# Verified Proofs of the Challenge Statements (`bit-circuit-synthesis`)
-/

namespace BitCircuitChallenge

open SiliconBigBang

theorem bpos_clmul_deg_additive (p q : BPos) :
    ∃ r : BPos,
      bclmul (BBin.pos p) (BBin.pos q) = BBin.pos r ∧
      bpos_deg r = badd (bpos_deg p) (bpos_deg q) :=
  SiliconBigBang.bpos_clmul_deg_additive p q

theorem bf2x_integral_domain (x y : BBin) :
    bclmul x y = BBin.zero ↔ x = BBin.zero ∨ y = BBin.zero :=
  SiliconBigBang.bf2x_integral_domain x y

theorem bcarried_vs_carryless_deg_jump_witness :
    bclmul (BBin.pos bp_three) (BBin.pos bp_three) = BBin.pos bp_five ∧
    bmul   (BBin.pos bp_three) (BBin.pos bp_three) = BBin.pos bp_nine ∧
    bpos_deg bp_five = badd (bpos_deg bp_three) (bpos_deg bp_three) ∧
    bpos_deg bp_nine ≠ badd (bpos_deg bp_three) (bpos_deg bp_three) :=
  SiliconBigBang.bcarried_vs_carryless_deg_jump_witness

theorem bartin_schreier_add_hom (x y : BBin) :
    bartin_schreier_op (bxor_bin x y) = bxor_bin (bartin_schreier_op x) (bartin_schreier_op y) :=
  SiliconBigBang.bartin_schreier_add_hom x y

theorem bartin_schreier_shift_one_inv (x : BBin) :
    bartin_schreier_op (bxor_bin x bone) = bartin_schreier_op x :=
  SiliconBigBang.bartin_schreier_shift_one_inv x

theorem bfrob2_xor_hom (x y : BBin) :
    bfrob2 (bxor_bin x y) = bxor_bin (bfrob2 x) (bfrob2 y) :=
  SiliconBigBang.bfrob2_xor_hom x y

theorem bfrob_trace_artin_schreier_telescope (m : BUnary) (x : BBin) :
    bfrob_trace m (bartin_schreier_op x) = bxor_bin (bfrob_pow m x) x :=
  SiliconBigBang.bfrob_trace_artin_schreier_telescope m x

theorem bhilbert90_additive_trace_zero_mod (P_m x : BBin) (m : BUnary)
    (hfrob_fix : bf2x_cong P_m (bfrob_pow m x) x) :
    bf2x_cong P_m (bfrob_trace m (bartin_schreier_op x)) BBin.zero :=
  SiliconBigBang.bhilbert90_additive_trace_zero_mod P_m x m hfrob_fix

end BitCircuitChallenge
