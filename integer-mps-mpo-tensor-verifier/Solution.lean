/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import IntegerMpsMpoTensorVerifier

/-!
# Verified Solutions (`integer-mps-mpo-tensor-verifier`)
-/

namespace IntegerMpsMpoTensorVerifierChallenge

open SiliconTensorEngine

theorem sound_rightReductionCert {K r : Nat} {u : Vec K} {T : Mat K K} {v : Vec K}
    {cert : RightReductionCert K r} (h : checkRightReductionCert u T v cert = true) :
    ∀ w : Nat, cert.d * transferSeq u T v (w + cert.w0) =
      transferSeq cert.u_r cert.M cert.v_r w :=
  SiliconTensorEngine.sound_rightReductionCert h

theorem sound_orthogonalityCert {K r : Nat} {u : Vec K} {T : Mat K K} {v : Vec K}
    {cert : RightReductionCert K r} (h : checkOrthogonalityCert u T v cert = true) :
    ∀ w : Nat, transferSeq u T v (w + cert.w0) = 0 :=
  SiliconTensorEngine.sound_orthogonalityCert h

theorem sound_recurrenceCert {K r1 r2 : Nat} {u : Vec K} {T : Mat K K} {v : Vec K}
    {cert : TwoStageCert K r1 r2} {coeffs : Vec r2}
    (h : checkRecurrenceCert u T v cert coeffs = true) :
    ∀ w : Nat,
      transferSeq u T v (w + cert.stage1.w0 + r2) =
      sumFin r2 (fun k => coeffs k * transferSeq u T v (w + cert.stage1.w0 + k.val)) :=
  SiliconTensorEngine.sound_recurrenceCert h

-- Theorem 1b: Uniform Parametric Closed Form (∀ q : Int, ∀ w : Nat)
theorem thm_rs_carry_parametric_closed (q : Int) (w : Nat) :
    (q + 3) * rsCarrySum q w = (q + 2) * (2 : Int) ^ (w + 1) + (-(q + 1)) ^ (w + 1) :=
  SiliconTensorEngine.thm_rs_carry_parametric_closed q w

theorem thm_carry_hadamard_fibonacci (w : Nat) :
    carryHadamardTrace w = (2 : Int) ^ w * (fib (w + 2) : Int) :=
  SiliconTensorEngine.thm_carry_hadamard_fibonacci w

theorem thm_carry_borrow_orthogonal (w : Nat) :
    sumNat (2 ^ (w + 1)) (fun x => sumNat (2 ^ (w + 1)) (fun y =>
      (-1 : Int) ^ carries (w + 1) x y * (-1 : Int) ^ borrows (w + 1) y x)) = 0 ∧
    sumNat (2 ^ (w + 1)) (fun x => sumNat (2 ^ (w + 1)) (fun y =>
      (-1 : Int) ^ carries (w + 1) x y * (-1 : Int) ^ borrows (w + 1) x y)) = 0 :=
  SiliconTensorEngine.thm_carry_borrow_orthogonal w

-- Theorem 7: ALL odd spectral moments of C_w vanish for ALL w ≥ 1 and ALL k : Nat!
theorem thm_carry_all_odd_traces_zero (w k : Nat) :
    sumNat (2 ^ (w + 1)) (fun x => carryMatPow (w + 1) (2 * k + 1) x x) = 0 :=
  SiliconTensorEngine.thm_carry_all_odd_traces_zero w k

theorem thm_carry_plus_borrow_tm (w x : Nat) :
    sumNat (2 ^ (w + 1)) (fun y => ((-1 : Int) ^ carries (w + 1) x y + (-1 : Int) ^ borrows (w + 1) x y) * thueMorse (w + 1) y) = 2 :=
  SiliconTensorEngine.thm_carry_plus_borrow_tm w x

end IntegerMpsMpoTensorVerifierChallenge
