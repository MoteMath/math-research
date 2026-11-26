/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GrpoK3Kl.RatOrder

/-!
# `FP8-E4M3` / `BF16` Log-Prob Cancellation Clip-Window Collapse & Direct Logit-Difference Invariance

Proves Headline Theorems 3 and 4 purely over `Rat`, `Int`, and `Nat` inside `Init` (zero Mathlib):
3. `fp8_bf16_logprob_cancellation_clip_collapse`
4. `direct_logit_diff_binade_invariance`
-/

namespace GrpoK3Kl

theorem binadeUlp_pos (k m : Nat) : (0 : Rat) < binadeUlp k m :=
  rat_mul_pos (pow2Rat_pos k) (invPow2Rat_pos m)

theorem binadeUlp_ge_quarter_of_le {k m : Nat} (h : m ≤ k + 2) :
    (1 / 4 : Rat) ≤ binadeUlp k m := by
  unfold binadeUlp invPow2Rat
  have hp : pow2Rat m ≤ pow2Rat (k + 2) := pow2Rat_mono h
  have h4 : pow2Rat (k + 2) = 4 * pow2Rat k := by
    rw [pow2Rat_succ, pow2Rat_succ]
    grind
  rw [h4] at hp
  have hpm : (0 : Rat) < pow2Rat m := pow2Rat_pos m
  have hdiv := rat_div_le_div_of_pos hp hpm
  rw [Rat.div_def, Rat.mul_inv_cancel _ (Rat.ne_of_gt hpm)] at hdiv
  have hmul := rat_mul_le_mul_of_nonneg_left hdiv (rat_div_nonneg (by decide) (by decide) : (0 : Rat) ≤ 1 / 4)
  have hL : (1 / 4 : Rat) * 1 = 1 / 4 := by grind
  have hR : (1 / 4 : Rat) * (4 * pow2Rat k / pow2Rat m) = pow2Rat k * (1 / pow2Rat m) := by
    rw [Rat.div_def, Rat.div_def]
    grind
  rw [hL, hR] at hmul
  exact hmul

theorem ratAbs_intCast_ge_one {z : Int} (hz : z ≠ 0) : (1 : Rat) ≤ ratAbs (z : Rat) := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => exact absurd rfl hz
    | succ k =>
      have hcast : ((Int.ofNat (k + 1)) : Rat) = ((k + 1 : Nat) : Rat) := rfl
      rw [hcast]
      have hnn : (0 : Rat) ≤ ((k + 1 : Nat) : Rat) := rat_natCast_nonneg (k + 1)
      rw [ratAbs_of_nonneg hnn]
      exact rat_natCast_le (Nat.succ_le_succ (Nat.zero_le k))
  | negSucc k =>
    have hcast : ((Int.negSucc k) : Rat) = -(((k + 1 : Nat) : Rat)) := by
      have h1 : Int.negSucc k = -((k + 1 : Nat) : Int) := rfl
      rw [h1, Rat.intCast_neg]
      rfl
    rw [hcast, ratAbs_neg]
    have hnn : (0 : Rat) ≤ ((k + 1 : Nat) : Rat) := rat_natCast_nonneg (k + 1)
    rw [ratAbs_of_nonneg hnn]
    exact rat_natCast_le (Nat.succ_le_succ (Nat.zero_le k))

theorem clip_escape_pos {Δ r : Rat} (hΔ : (1 / 4 : Rat) ≤ Δ)
    (hr : 1 + Δ + Δ * Δ / 2 ≤ r) : (6 / 5 : Rat) < r ∧ ¬ inClipWindow r := by
  have hΔ0 : (0 : Rat) ≤ Δ := Rat.le_trans (rat_div_nonneg (by decide) (by decide)) hΔ
  have hsq : (1 / 4 : Rat) * (1 / 4 : Rat) ≤ Δ * Δ :=
    Rat.le_trans (rat_mul_le_mul_of_nonneg_left hΔ (rat_div_nonneg (by decide) (by decide)))
                 (rat_mul_le_mul_of_nonneg_right hΔ hΔ0)
  have hsq2 : (1 / 32 : Rat) ≤ Δ * Δ / 2 := by
    have h := rat_div_le_div_of_pos hsq (by decide : (0 : Rat) < 2)
    have eq : ((1 / 4 : Rat) * (1 / 4 : Rat)) / 2 = 1 / 32 := by grind
    rw [eq] at h; exact h
  have h1 : (41 / 32 : Rat) ≤ 1 + Δ + Δ * Δ / 2 := by
    have hsum := rat_add_le_add (rat_add_le_add (Rat.le_refl (a := (1 : Rat))) hΔ) hsq2
    have eq : (1 : Rat) + 1 / 4 + 1 / 32 = 41 / 32 := by grind
    rw [eq] at hsum; exact hsum
  have hgt : (6 / 5 : Rat) < r :=
    rat_lt_of_lt_of_le (by grind : (6 / 5 : Rat) < 41 / 32) (Rat.le_trans h1 hr)
  refine ⟨hgt, ?_⟩
  intro hwin
  exact Rat.not_le.mpr hgt hwin.2

theorem clip_escape_neg {Δ r : Rat} (hΔ : Δ ≤ -(1 / 4 : Rat)) (_hr0 : (0 : Rat) < r)
    (hr : 1 + (-Δ) + (-Δ) * (-Δ) / 2 ≤ r⁻¹) : r < (4 / 5 : Rat) ∧ ¬ inClipWindow r := by
  have hu : (1 / 4 : Rat) ≤ -Δ := by
    apply rat_le_of_sub_nonneg
    have h := rat_sub_nonneg hΔ
    have eq : (-Δ) - 1 / 4 = -(1 / 4 : Rat) - Δ := by grind
    rw [eq]; exact h
  have hu0 : (0 : Rat) ≤ -Δ := Rat.le_trans (rat_div_nonneg (by decide) (by decide)) hu
  have hsq : (1 / 4 : Rat) * (1 / 4 : Rat) ≤ (-Δ) * (-Δ) :=
    Rat.le_trans (rat_mul_le_mul_of_nonneg_left hu (rat_div_nonneg (by decide) (by decide)))
                 (rat_mul_le_mul_of_nonneg_right hu hu0)
  have hsq2 : (1 / 32 : Rat) ≤ (-Δ) * (-Δ) / 2 := by
    have h := rat_div_le_div_of_pos hsq (by decide : (0 : Rat) < 2)
    have eq : ((1 / 4 : Rat) * (1 / 4 : Rat)) / 2 = 1 / 32 := by grind
    rw [eq] at h; exact h
  have h1 : (41 / 32 : Rat) ≤ r⁻¹ := by
    have hsum := rat_add_le_add (rat_add_le_add (Rat.le_refl (a := (1 : Rat))) hu) hsq2
    have eq : (1 : Rat) + 1 / 4 + 1 / 32 = 41 / 32 := by grind
    rw [eq] at hsum
    exact Rat.le_trans hsum hr
  have hinv := rat_inv_le_inv_of_pos (rat_div_pos (by decide) (by decide) : (0 : Rat) < 41 / 32) h1
  rw [Rat.inv_inv] at hinv
  have hinv_val : ((41 / 32 : Rat))⁻¹ = 32 / 41 := by
    rw [Rat.div_def, rat_mul_inv (by decide) (Rat.ne_of_gt (rat_inv_pos (by decide))),
        Rat.inv_inv, Rat.div_def]
  rw [hinv_val] at hinv
  have hlt : r < (4 / 5 : Rat) :=
    rat_lt_of_le_of_lt hinv (by grind : (32 / 41 : Rat) < 4 / 5)
  refine ⟨hlt, ?_⟩
  intro hwin
  exact Rat.not_le.mpr hlt hwin.1

/-- Headline Theorem 3 (`fp8_bf16_logprob_cancellation_clip_collapse`). -/
theorem fp8_bf16_logprob_cancellation_clip_collapse :
    (∀ (k m : Nat) (q1 q2 : Int),
      (q1 : Rat) * binadeUlp k m - (q2 : Rat) * binadeUlp k m =
        ((q1 - q2 : Int) : Rat) * binadeUlp k m ∧
      (q1 ≠ q2 → binadeUlp k m ≤
        ratAbs ((q1 : Rat) * binadeUlp k m - (q2 : Rat) * binadeUlp k m))) ∧
    (∀ (Δ r : Rat), (1 / 4 : Rat) ≤ Δ → 1 + Δ + Δ * Δ / 2 ≤ r →
      (6 / 5 : Rat) < r ∧ ¬ inClipWindow r) ∧
    (∀ (Δ r : Rat), Δ ≤ -(1 / 4 : Rat) → (0 : Rat) < r →
      1 + (-Δ) + (-Δ) * (-Δ) / 2 ≤ r⁻¹ →
      r < (4 / 5 : Rat) ∧ ¬ inClipWindow r) ∧
    (∀ (k m : Nat), m ≤ k + 2 → (1 / 4 : Rat) ≤ binadeUlp k m) ∧
    (∀ k : Nat, 1 ≤ k → (1 / 4 : Rat) ≤ binadeUlp k 3) ∧
    (∀ k : Nat, 5 ≤ k → (1 / 4 : Rat) ≤ binadeUlp k 7) ∧
    (∀ k : Nat, 8 ≤ k → (1 / 4 : Rat) ≤ binadeUlp k 10) ∧
    (binadeUlp 1 3 = 1 / 4 ∧ binadeUlp 3 7 = 1 / 16 ∧ binadeUlp 4 7 = 1 / 8 ∧
     binadeUlp 5 7 = 1 / 4 ∧ binadeUlp 8 10 = 1 / 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k m q1 q2
    have heq : (q1 : Rat) * binadeUlp k m - (q2 : Rat) * binadeUlp k m =
        ((q1 - q2 : Int) : Rat) * binadeUlp k m := by
      rw [Rat.intCast_sub]
      grind
    refine ⟨heq, ?_⟩
    intro hne
    rw [heq, ratAbs_mul]
    have hdiff : q1 - q2 ≠ 0 := by
      intro h0
      exact hne (Int.sub_eq_zero.mp h0)
    have h1 : (1 : Rat) ≤ ratAbs ((q1 - q2 : Int) : Rat) := ratAbs_intCast_ge_one hdiff
    have hu : (0 : Rat) < binadeUlp k m := binadeUlp_pos k m
    rw [ratAbs_of_nonneg (Rat.le_of_lt hu)]
    have hmul := rat_mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hu)
    rw [Rat.one_mul] at hmul
    exact hmul
  · intro Δ r hΔ hr
    exact clip_escape_pos hΔ hr
  · intro Δ r hΔ hr0 hr
    exact clip_escape_neg hΔ hr0 hr
  · intro k m h
    exact binadeUlp_ge_quarter_of_le h
  · intro k hk
    exact binadeUlp_ge_quarter_of_le (by omega)
  · intro k hk
    exact binadeUlp_ge_quarter_of_le (by omega)
  · intro k hk
    exact binadeUlp_ge_quarter_of_le (by omega)
  · unfold binadeUlp invPow2Rat pow2Rat
    simp only [show 2 ^ 1 = 2 by decide, show 2 ^ 3 = 8 by decide,
               show 2 ^ 4 = 16 by decide, show 2 ^ 5 = 32 by decide,
               show 2 ^ 7 = 128 by decide, show 2 ^ 8 = 256 by decide,
               show 2 ^ 10 = 1024 by decide]
    grind

/-- Headline Theorem 4 (`direct_logit_diff_binade_invariance`). -/
theorem direct_logit_diff_binade_invariance :
    (∀ (zNew zOld lseNew lseOld : Rat),
      logProb zNew lseNew - logProb zOld lseOld = directLogitDiff zNew zOld lseNew lseOld) ∧
    (∀ (zNew zOld lseNew lseOld c : Rat),
      directLogitDiff (zNew - c) (zOld - c) lseNew lseOld =
        directLogitDiff zNew zOld lseNew lseOld) ∧
    (∀ (zNew zOld lseNew lseOld c : Rat),
      directLogitDiff zNew zOld (lseNew + c) (lseOld + c) =
        directLogitDiff zNew zOld lseNew lseOld) ∧
    (∀ (k m : Nat) (lpNew lpOld flNew flOld : Rat),
      ratAbs (flNew - lpNew) ≤ binadeUlp k m / 2 →
      ratAbs (flOld - lpOld) ≤ binadeUlp k m / 2 →
      ratAbs ((flNew - flOld) - (lpNew - lpOld)) ≤ binadeUlp k m) ∧
    (∀ (m : Nat) (Δ ΔHat B : Rat),
      ratAbs Δ ≤ B →
      ratAbs (ΔHat - Δ) ≤ invPow2Rat (m + 1) * ratAbs Δ →
      ratAbs (ΔHat - Δ) ≤ invPow2Rat (m + 1) * B) ∧
    (invPow2Rat 8 * (1 / 4 : Rat) = 1 / 1024 ∧
     binadeUlp 4 7 / (1 / 1024 : Rat) = 128 ∧
     binadeUlp 5 7 / (1 / 1024 : Rat) = 256) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro zNew zOld lseNew lseOld
    unfold logProb directLogitDiff
    grind
  · intro zNew zOld lseNew lseOld c
    unfold directLogitDiff
    grind
  · intro zNew zOld lseNew lseOld c
    unfold directLogitDiff
    grind
  · intro k m lpNew lpOld flNew flOld h1 h2
    have hsplit : (flNew - flOld) - (lpNew - lpOld) = (flNew - lpNew) + (-(flOld - lpOld)) := by
      grind
    rw [hsplit]
    have htri := ratAbs_add_le (flNew - lpNew) (-(flOld - lpOld))
    rw [ratAbs_neg] at htri
    have hsum := rat_add_le_add h1 h2
    have hhalf : binadeUlp k m / 2 + binadeUlp k m / 2 = binadeUlp k m := by grind
    rw [hhalf] at hsum
    exact Rat.le_trans htri hsum
  · intro m Δ ΔHat B hB hrel
    have hmul := rat_mul_le_mul_of_nonneg_left hB (Rat.le_of_lt (invPow2Rat_pos (m + 1)))
    exact Rat.le_trans hrel hmul
  · unfold binadeUlp invPow2Rat pow2Rat
    simp only [show 2 ^ 8 = 256 by decide, show 2 ^ 4 = 16 by decide,
               show 2 ^ 5 = 32 by decide, show 2 ^ 7 = 128 by decide]
    grind

end GrpoK3Kl
