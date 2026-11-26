/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Fp8E4m3Lop3.Defs

/-!
# Exact OCP `FP8-E4M3FN` Dyadic Value Law (`Dyadic.lean`)

Kernel-checked universal characterization of OCP `FP8-E4M3FN` (`e4m3ScaledVal x = 512 * val(x)`):
- Max finite magnitude `448` (`0x7E`, scaled `229376`), min positive subnormal `2^-9` (`0x01`, scaled `1`),
- Exact sign-bit symmetry `e4m3ScaledVal (x ^^^ 0x80#8) = -e4m3ScaledVal x`,
- Strict order-preserving monotonicity on positive finite codes `0x01..0x7E`,
- Exact signed-zero characterization (`0x00`, `0x80`) and exact partition cardinality `126 + 126 + 2 + 2 = 256`.
-/

namespace Fp8E4m3Lop3

/-- Binary-splitting universal range checker over `[base, base + 2^d)` (recursion depth `d`). -/
def checkPow2 (p : Nat → Bool) : Nat → Nat → Bool
  | 0, base => p base
  | d + 1, base => checkPow2 p d base && checkPow2 p d (base + 2 ^ d)

theorem checkPow2_spec (p : Nat → Bool) :
    ∀ d base, checkPow2 p d base = true → ∀ k, base ≤ k → k < base + 2 ^ d → p k = true := by
  intro d
  induction d with
  | zero =>
    intro base h k hlo hhi
    have hEq : k = base := by omega
    subst hEq
    exact h
  | succ d ih =>
    intro base h k hlo hhi
    simp only [checkPow2, Bool.and_eq_true] at h
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by
      rw [Nat.pow_succ, Nat.mul_two]
    by_cases hlt : k < base + 2 ^ d
    · exact ih base h.1 k hlo hlt
    · exact ih (base + 2 ^ d) h.2 k (by omega) (by omega)

/-- Exhaustive binary-splitting checker on `BitVec 8` (depth 8). -/
def checkBv8 (p : BitVec 8 → Bool) : Bool :=
  checkPow2 (fun k => p (BitVec.ofNat 8 k)) 8 0

/-- Exhaustive binary-splitting checker on `BitVec 6` (depth 6). -/
def checkBv6 (p : BitVec 6 → Bool) : Bool :=
  checkPow2 (fun k => p (BitVec.ofNat 6 k)) 6 0

/-- Exhaustive binary-splitting checker on `BitVec 4` (depth 4). -/
def checkBv4 (p : BitVec 4 → Bool) : Bool :=
  checkPow2 (fun k => p (BitVec.ofNat 4 k)) 4 0

theorem forall_bv8_of_checkBv8 {p : BitVec 8 → Bool} (h : checkBv8 p = true) :
    ∀ x : BitVec 8, p x = true := by
  intro x
  have h1 := checkPow2_spec (fun k => p (BitVec.ofNat 8 k)) 8 0 h x.toNat (Nat.zero_le _) x.isLt
  simpa [BitVec.ofNat_toNat] using h1

theorem forall_bv6_of_checkBv6 {p : BitVec 6 → Bool} (h : checkBv6 p = true) :
    ∀ x : BitVec 6, p x = true := by
  intro x
  have h1 := checkPow2_spec (fun k => p (BitVec.ofNat 6 k)) 6 0 h x.toNat (Nat.zero_le _) x.isLt
  simpa [BitVec.ofNat_toNat] using h1

theorem forall_bv4_of_checkBv4 {p : BitVec 4 → Bool} (h : checkBv4 p = true) :
    ∀ x : BitVec 4, p x = true := by
  intro x
  have h1 := checkPow2_spec (fun k => p (BitVec.ofNat 4 k)) 4 0 h x.toNat (Nat.zero_le _) x.isLt
  simpa [BitVec.ofNat_toNat] using h1

private theorem e4m3_max_bound_check :
    checkBv8 (fun x =>
      !isFiniteE4M3 x || decide (-229376 ≤ e4m3ScaledVal x ∧ e4m3ScaledVal x ≤ 229376)) = true := by
  decide

private theorem e4m3_min_pos_check :
    checkBv8 (fun x =>
      !isPosFiniteE4M3 x || decide (1 ≤ e4m3ScaledVal x)) = true := by
  decide

private theorem e4m3_sign_sym_check :
    checkBv8 (fun x =>
      !isFiniteE4M3 x || decide (e4m3ScaledVal (x ^^^ 0x80#8) = -e4m3ScaledVal x)) = true := by
  decide

private theorem e4m3_pos_step_mono_check :
    checkPow2 (fun k =>
      if 1 ≤ k && k < 126 then
        decide (e4m3ScaledVal (BitVec.ofNat 8 k) < e4m3ScaledVal (BitVec.ofNat 8 (k + 1)))
      else true) 7 0 = true := by
  decide

private theorem e4m3_pos_mono_aux :
    ∀ a b : Nat, 1 ≤ a → a < b → b ≤ 126 →
      e4m3ScaledVal (BitVec.ofNat 8 a) < e4m3ScaledVal (BitVec.ofNat 8 b) := by
  intro a b ha hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    have hstep : e4m3ScaledVal (BitVec.ofNat 8 b) < e4m3ScaledVal (BitVec.ofNat 8 (b + 1)) := by
      have h := checkPow2_spec _ 7 0 e4m3_pos_step_mono_check b (Nat.zero_le _) (by omega)
      have hcond : (1 ≤ b && b < 126) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      simp only [hcond, ↓reduceIte, decide_eq_true_eq] at h
      exact h
    by_cases hEq : a = b
    · subst hEq; exact hstep
    · exact Int.lt_trans (ih (by omega) (by omega)) hstep

private theorem e4m3_zero_check :
    checkBv8 (fun x =>
      !isFiniteE4M3 x || decide (e4m3ScaledVal x = 0 ↔ isZeroE4M3 x = true)) = true := by
  decide

/-- Theorem 6: Universal exact dyadic value law for OCP `FP8-E4M3FN` (`e4m3ScaledVal x = 512 * val(x)`). -/
theorem fp8_e4m3_exact_dyadic_value_law :
    e4m3ScaledVal 0x7E#8 = 448 * 512 ∧
    e4m3ScaledVal 0x01#8 = 1 ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      -(448 * 512) ≤ e4m3ScaledVal x ∧ e4m3ScaledVal x ≤ 448 * 512) ∧
    (∀ x : BitVec 8, isPosFiniteE4M3 x = true → 1 ≤ e4m3ScaledVal x) ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      e4m3ScaledVal (x ^^^ 0x80#8) = -e4m3ScaledVal x) ∧
    (∀ x y : BitVec 8, isPosFiniteE4M3 x = true → isPosFiniteE4M3 y = true →
      x.toNat < y.toNat → e4m3ScaledVal x < e4m3ScaledVal y) ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      (e4m3ScaledVal x = 0 ↔ isZeroE4M3 x = true)) ∧
    countBv8 isPosFiniteE4M3 = 126 ∧
    countBv8 isNegFiniteE4M3 = 126 ∧
    countBv8 isZeroE4M3 = 2 ∧
    countBv8 isNanE4M3 = 2 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩
  · intro x hx
    have h := forall_bv8_of_checkBv8 e4m3_max_bound_check x
    simp only [hx, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
    exact h
  · intro x hx
    have h := forall_bv8_of_checkBv8 e4m3_min_pos_check x
    simp only [hx, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
    exact h
  · intro x hx
    have h := forall_bv8_of_checkBv8 e4m3_sign_sym_check x
    simp only [hx, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
    exact h
  · intro x y hx hy hlt
    simp only [isPosFiniteE4M3, Bool.and_eq_true, decide_eq_true_eq] at hx hy
    have h := e4m3_pos_mono_aux x.toNat y.toNat hx.1 hlt hy.2
    simpa [BitVec.ofNat_toNat] using h
  · intro x hx
    have h := forall_bv8_of_checkBv8 e4m3_zero_check x
    simp only [hx, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
    exact h

end Fp8E4m3Lop3
