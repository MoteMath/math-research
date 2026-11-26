/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Fp8E4m3Lop3.Dyadic

/-!
# Bit-Sliced OCP `FP8-E4M3FN` `LOP3` Circuits (`BitSlicedCircuits.lean`)

Kernel-checked 0-ULP proofs for all five Wave 3A Frontier-1 OCP `FP8-E4M3FN` circuits:
1. `fp8_e4m3_rsqrt_15_lop3_exact`: 15-`LOP3` (depth 8) `e4m3RsqrtPosDag` satisfies the exact
   pure-integer RNE Voronoi condition for `1 / sqrt(val(x))` on ALL 126 positive finite codes
   `0x01..0x7E`, with `y7 = 0` (0 gates).
2. `fp8_e4m3_rsqrt_full_33_lop3_exact`: 33-`LOP3` (depth 14) `e4m3RsqrtFullDag` matches
   `e4m3RsqrtPosDag` (and the exact RNE Voronoi condition) on all 126 positive finite codes and
   outputs canonical NaN `0x7F` on all 130 non-positive/NaN codes (`0x00`, `0x7F`, `0x80..0xFF`).
3. `fp8_e4m3_activations_lop3_exact`: 0-ULP exactness over all 254 finite OCP `FP8-E4M3FN` codes
   for `e4m3ExpDag` (67 `LOP3`, depth 9), `e4m3GeluDag` (82 `LOP3`, depth 15, plus 1-`LOP3` tight
   `y6 = (!x7) && x6`), and `e4m3SiluDag` (93 `LOP3`, depth 16, plus 0-`LOP3` tight `y7 = x7`).
-/

namespace Fp8E4m3Lop3

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-! ## Theorem 1: 15-`LOP3` Positive `rsqrt` with Exact Algebraic RNE Certification -/

private theorem rsqrt_pos_rne_check :
    checkBv8 (fun x =>
      !isPosFiniteE4M3 x || isExactRneRsqrtE4M3 x (evalLop3Dag8 e4m3RsqrtPosDag x)) = true := by
  decide

private theorem rsqrt_pos_sign_zero_check :
    checkBv8 (fun x =>
      !isPosFiniteE4M3 x || !(evalLop3Dag8 e4m3RsqrtPosDag x).getLsbD 7) = true := by
  decide

theorem fp8_e4m3_rsqrt_15_lop3_exact :
    e4m3RsqrtPosDag.gates.length = 15 ∧
    dagDepth e4m3RsqrtPosDag = 8 ∧
    (∀ x : BitVec 8, isPosFiniteE4M3 x = true →
      isExactRneRsqrtE4M3 x (evalLop3Dag8 e4m3RsqrtPosDag x) = true) ∧
    (∀ x : BitVec 8, isPosFiniteE4M3 x = true →
      (evalLop3Dag8 e4m3RsqrtPosDag x).getLsbD 7 = false) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro x hx
    have h := forall_bv8_of_checkBv8 rsqrt_pos_rne_check x
    simp only [hx, Bool.not_true, Bool.false_or] at h
    exact h
  · intro x hx
    have h := forall_bv8_of_checkBv8 rsqrt_pos_sign_zero_check x
    simp only [hx, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at h
    exact h

/-! ## Theorem 2: 33-`LOP3` Full-Domain `rsqrt` (All 256 Codes) -/

private theorem rsqrt_full_pos_check :
    checkBv8 (fun x =>
      !isPosFiniteE4M3 x ||
        (evalLop3Dag8 e4m3RsqrtFullDag x == evalLop3Dag8 e4m3RsqrtPosDag x &&
         isExactRneRsqrtE4M3 x (evalLop3Dag8 e4m3RsqrtFullDag x))) = true := by
  decide

private theorem rsqrt_full_nonpos_nan_check :
    checkBv8 (fun x =>
      isPosFiniteE4M3 x || (evalLop3Dag8 e4m3RsqrtFullDag x == 0x7F#8)) = true := by
  decide

theorem fp8_e4m3_rsqrt_full_33_lop3_exact :
    e4m3RsqrtFullDag.gates.length = 33 ∧
    dagDepth e4m3RsqrtFullDag = 14 ∧
    (∀ x : BitVec 8, isPosFiniteE4M3 x = true →
      evalLop3Dag8 e4m3RsqrtFullDag x = evalLop3Dag8 e4m3RsqrtPosDag x ∧
      isExactRneRsqrtE4M3 x (evalLop3Dag8 e4m3RsqrtFullDag x) = true) ∧
    (∀ x : BitVec 8, isPosFiniteE4M3 x = false →
      evalLop3Dag8 e4m3RsqrtFullDag x = 0x7F#8) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro x hx
    have h := forall_bv8_of_checkBv8 rsqrt_full_pos_check x
    simp only [hx, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
    exact h
  · intro x hx
    have h := forall_bv8_of_checkBv8 rsqrt_full_nonpos_nan_check x
    simp only [hx, Bool.false_or, beq_iff_eq] at h
    exact h

/-! ## Theorem 3: Exact 0-ULP `exp` (67 `LOP3`), `gelu` (82 `LOP3`), and `silu` (93 `LOP3`) -/

private theorem exp_exact_check :
    checkBv8 (fun x =>
      !isFiniteE4M3 x || (evalLop3Dag8 e4m3ExpDag x == e4m3ExpRefTable.getD x.toNat 0#8)) = true := by
  decide

private theorem gelu_exact_check :
    checkBv8 (fun x =>
      !isFiniteE4M3 x || (evalLop3Dag8 e4m3GeluDag x == e4m3GeluRefTable.getD x.toNat 0#8)) = true := by
  decide

private theorem gelu_y6_single_lop3_check :
    checkBv8 (fun x =>
      !isFiniteE4M3 x ||
        ((evalLop3Dag8 e4m3GeluDag x).getLsbD 6 == lop3 0x04#8 (x.getLsbD 7) (x.getLsbD 6) (x.getLsbD 7))) = true := by
  decide

private theorem silu_exact_check :
    checkBv8 (fun x =>
      !isFiniteE4M3 x || (evalLop3Dag8 e4m3SiluDag x == e4m3SiluRefTable.getD x.toNat 0#8)) = true := by
  decide

private theorem silu_y7_wire_check :
    checkBv8 (fun x =>
      !isFiniteE4M3 x || ((evalLop3Dag8 e4m3SiluDag x).getLsbD 7 == x.getLsbD 7)) = true := by
  decide

theorem fp8_e4m3_activations_lop3_exact :
    e4m3ExpDag.gates.length = 67 ∧
    dagDepth e4m3ExpDag = 9 ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      evalLop3Dag8 e4m3ExpDag x = e4m3ExpRefTable.getD x.toNat 0#8) ∧
    e4m3GeluDag.gates.length = 82 ∧
    dagDepth e4m3GeluDag = 15 ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      evalLop3Dag8 e4m3GeluDag x = e4m3GeluRefTable.getD x.toNat 0#8) ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      (evalLop3Dag8 e4m3GeluDag x).getLsbD 6 =
        lop3 0x04#8 (x.getLsbD 7) (x.getLsbD 6) (x.getLsbD 7)) ∧
    e4m3SiluDag.gates.length = 93 ∧
    dagDepth e4m3SiluDag = 16 ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      evalLop3Dag8 e4m3SiluDag x = e4m3SiluRefTable.getD x.toNat 0#8) ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      (evalLop3Dag8 e4m3SiluDag x).getLsbD 7 = x.getLsbD 7) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, ?_, ?_, by decide, by decide, ?_, ?_⟩
  · intro x hx
    have h := forall_bv8_of_checkBv8 exp_exact_check x
    simp only [hx, Bool.not_true, Bool.false_or, beq_iff_eq] at h
    exact h
  · intro x hx
    have h := forall_bv8_of_checkBv8 gelu_exact_check x
    simp only [hx, Bool.not_true, Bool.false_or, beq_iff_eq] at h
    exact h
  · intro x hx
    have h := forall_bv8_of_checkBv8 gelu_y6_single_lop3_check x
    simp only [hx, Bool.not_true, Bool.false_or, beq_iff_eq] at h
    exact h
  · intro x hx
    have h := forall_bv8_of_checkBv8 silu_exact_check x
    simp only [hx, Bool.not_true, Bool.false_or, beq_iff_eq] at h
    exact h
  · intro x hx
    have h := forall_bv8_of_checkBv8 silu_y7_wire_check x
    simp only [hx, Bool.not_true, Bool.false_or, beq_iff_eq] at h
    exact h

end Fp8E4m3Lop3
