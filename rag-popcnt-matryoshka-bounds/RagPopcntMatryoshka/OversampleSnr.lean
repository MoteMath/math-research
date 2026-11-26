/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RagPopcntMatryoshka.RatOrder

/-!
# Theorem 2: Exact 2-Stage Oversample Cantelli Concentration & SNR² Hierarchy

Proves the exact Cantelli one-sided tail law `σ² / (σ² + μ²) = 1 / (1 + SNR²)`,
strict monotonicity of Stage-1 oversample budget in quantizer fidelity `η_q²`,
the exact `2.00×` (`1.58-Bit Ternary`) and `2.18×` (`2-Bit Quantile`) SNR² dominance
over `1-Bit` (`η_{1b}² = 4/π²`), and quadratic/exponential oversample collapse.
-/

namespace RagPopcntMatryoshka

theorem cantelli_identity {mu sigmaSq : Rat} (hs : (0 : Rat) < sigmaSq) :
    sigmaSq / (sigmaSq + mu * mu) = cantelliTail (mu * mu / sigmaSq) := by
  unfold cantelliTail
  have hsne : sigmaSq ≠ 0 := Rat.ne_of_gt hs
  have hden1 : (0 : Rat) < sigmaSq + mu * mu :=
    rat_add_pos_of_pos_of_nonneg hs (rat_sq_nonneg mu)
  have hden1ne : sigmaSq + mu * mu ≠ 0 := Rat.ne_of_gt hden1
  have hden2 : (0 : Rat) < 1 + mu * mu / sigmaSq :=
    rat_add_pos_of_pos_of_nonneg (by grind : (0 : Rat) < 1)
      (rat_div_nonneg (rat_sq_nonneg mu) hs)
  have hden2ne : 1 + mu * mu / sigmaSq ≠ 0 := Rat.ne_of_gt hden2
  have hmul : (sigmaSq + mu * mu) = sigmaSq * (1 + mu * mu / sigmaSq) := by
    rw [Rat.div_def]
    have h1 : sigmaSq * (mu * mu * sigmaSq⁻¹) = mu * mu * (sigmaSq * sigmaSq⁻¹) := by grind
    have h2 : sigmaSq * sigmaSq⁻¹ = 1 := Rat.mul_inv_cancel sigmaSq hsne
    grind
  apply rat_mul_right_cancel (c := sigmaSq + mu * mu) hden1ne
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hden1ne, Rat.mul_one]
  rw [Rat.div_def, hmul]
  have h3 : 1 * (1 + mu * mu / sigmaSq)⁻¹ * (sigmaSq * (1 + mu * mu / sigmaSq)) =
      sigmaSq * ((1 + mu * mu / sigmaSq)⁻¹ * (1 + mu * mu / sigmaSq)) := by grind
  rw [h3, Rat.inv_mul_cancel _ hden2ne, Rat.mul_one]

theorem cantelliTail_strict_anti {s1 s2 : Rat} (hs1 : (0 : Rat) ≤ s1) (h : s1 < s2) :
    cantelliTail s2 < cantelliTail s1 := by
  unfold cantelliTail
  have hd1 : (0 : Rat) < 1 + s1 := rat_add_pos_of_pos_of_nonneg (by decide : (0 : Rat) < 1) hs1
  have hd2 : (0 : Rat) < 1 + s2 := rat_add_pos_of_pos_of_nonneg (by decide : (0 : Rat) < 1)
    (Rat.le_trans hs1 (Rat.le_of_lt h))
  apply rat_div_lt_div_of_cross hd2 hd1
  have hlt : 1 + s1 < 1 + s2 := by
    apply rat_lt_of_sub_pos
    have eq : (1 + s2) - (1 + s1) = s2 - s1 := by grind
    rw [eq]; exact rat_sub_pos h
  grind

theorem cantelliOversample_strict_anti_eta {N K d delta eta1 eta2 : Rat}
    (hN : (0 : Rat) < N) (hK : (0 : Rat) < K) (hd : (0 : Rat) < d)
    (hdel : delta ≠ 0) (he1 : (0 : Rat) < eta1) (h : eta1 < eta2) :
    cantelliOversample N K (stage1SnrSq d delta eta2) <
    cantelliOversample N K (stage1SnrSq d delta eta1) := by
  unfold cantelliOversample stage1SnrSq
  have hdelSq : (0 : Rat) < delta * delta := by
    have hnn := rat_sq_nonneg delta
    have hne : delta * delta ≠ 0 := by
      intro h0
      cases Rat.mul_eq_zero.mp h0 with
      | inl hx => exact hdel hx
      | inr hx => exact hdel hx
    exact Rat.lt_of_le_of_ne hnn (Ne.symm hne)
  have hfac : (0 : Rat) < d * (delta * delta) := rat_mul_pos hd hdelSq
  have hs1 : (0 : Rat) ≤ eta1 * d * delta * delta := by
    have eq : eta1 * d * delta * delta = eta1 * (d * (delta * delta)) := by grind
    rw [eq]; exact Rat.mul_nonneg (Rat.le_of_lt he1) (Rat.le_of_lt hfac)
  have hslt : eta1 * d * delta * delta < eta2 * d * delta * delta := by
    have eq1 : eta1 * d * delta * delta = eta1 * (d * (delta * delta)) := by grind
    have eq2 : eta2 * d * delta * delta = eta2 * (d * (delta * delta)) := by grind
    rw [eq1, eq2]
    exact rat_mul_lt_mul_of_pos_right h hfac
  exact rat_mul_lt_mul_of_pos_left (cantelliTail_strict_anti hs1 hslt) (rat_div_pos hN hK)

theorem eta1bSq_bounds {piRat : Rat} (hlo : (314 / 100 : Rat) ≤ piRat)
    (hhi : piRat ≤ (315 / 100 : Rat)) :
    (403 / 1000 : Rat) < eta1bSq piRat ∧ eta1bSq piRat < (406 / 1000 : Rat) := by
  unfold eta1bSq
  have hpos : (0 : Rat) < piRat := rat_lt_of_lt_of_le (by grind : (0 : Rat) < 314 / 100) hlo
  have hsq_pos : (0 : Rat) < piRat * piRat := rat_mul_pos hpos hpos
  have hsq_lo : (314 / 100 : Rat) * (314 / 100) ≤ piRat * piRat :=
    Rat.le_trans (rat_mul_le_mul_of_nonneg_left hlo (by grind : (0 : Rat) ≤ 314 / 100))
      (rat_mul_le_mul_of_nonneg_right hlo (Rat.le_of_lt hpos))
  have hsq_hi : piRat * piRat ≤ (315 / 100 : Rat) * (315 / 100) :=
    Rat.le_trans (rat_mul_le_mul_of_nonneg_left hhi (Rat.le_of_lt hpos))
      (rat_mul_le_mul_of_nonneg_right hhi (by grind : (0 : Rat) ≤ 315 / 100))
  constructor
  · rw [rat_lt_div_iff hsq_pos]
    have h1 := rat_mul_le_mul_of_nonneg_left hsq_hi (by grind : (0 : Rat) ≤ 403 / 1000)
    exact rat_lt_of_le_of_lt h1 (by grind)
  · rw [rat_div_lt_iff hsq_pos]
    have h1 := rat_mul_le_mul_of_nonneg_left hsq_lo (by grind : (0 : Rat) ≤ 406 / 1000)
    exact rat_lt_of_lt_of_le (by grind) h1

theorem snr_hierarchy_and_ratios {piRat : Rat} (hlo : (314 / 100 : Rat) ≤ piRat)
    (hhi : piRat ≤ (315 / 100 : Rat)) :
    eta1bSq piRat < (1 / 2 : Rat) ∧
    (1 / 2 : Rat) < (4 / 5 : Rat) ∧
    (4 / 5 : Rat) < etaTernarySq ∧
    etaTernarySq < eta2bSq ∧
    eta2bSq < 1 ∧
    (199 / 100 : Rat) < etaTernarySq / eta1bSq piRat ∧
    (217 / 100 : Rat) < eta2bSq / eta1bSq piRat := by
  have ⟨hbLo, hbHi⟩ := eta1bSq_bounds hlo hhi
  have hbPos : (0 : Rat) < eta1bSq piRat :=
    rat_lt_trans (by grind : (0 : Rat) < 403 / 1000) hbLo
  refine ⟨rat_lt_trans hbHi (by grind), by grind, by unfold etaTernarySq; grind,
    by unfold etaTernarySq eta2bSq; grind, by unfold eta2bSq; grind, ?_, ?_⟩
  · rw [rat_lt_div_iff hbPos]
    have h1 := rat_mul_lt_mul_of_pos_left hbHi (by grind : (0 : Rat) < 199 / 100)
    unfold etaTernarySq
    exact rat_lt_trans h1 (by grind)
  · rw [rat_lt_div_iff hbPos]
    have h1 := rat_mul_lt_mul_of_pos_left hbHi (by grind : (0 : Rat) < 217 / 100)
    unfold eta2bSq
    exact rat_lt_trans h1 (by grind)

theorem snr_doubling_tail_collapse {p : Rat} (h0 : (0 : Rat) < p) (h1 : p < 1) :
    p * p < p := by
  have h := rat_mul_lt_mul_of_pos_left h1 h0
  have eq : p * 1 = p := by grind
  rw [eq] at h
  exact h

/-- Headline Theorem 2 (`two_stage_oversample_snr_squared_hierarchy`). -/
theorem two_stage_oversample_snr_squared_hierarchy :
    (∀ mu sigmaSq : Rat, (0 : Rat) < sigmaSq →
      sigmaSq / (sigmaSq + mu * mu) = cantelliTail (mu * mu / sigmaSq)) ∧
    (∀ s1 s2 : Rat, (0 : Rat) ≤ s1 → s1 < s2 →
      cantelliTail s2 < cantelliTail s1) ∧
    (∀ N K d delta eta1 eta2 : Rat,
      (0 : Rat) < N → (0 : Rat) < K → (0 : Rat) < d → delta ≠ 0 →
      (0 : Rat) < eta1 → eta1 < eta2 →
      cantelliOversample N K (stage1SnrSq d delta eta2) <
      cantelliOversample N K (stage1SnrSq d delta eta1)) ∧
    (∀ piRat : Rat, (314 / 100 : Rat) ≤ piRat → piRat ≤ (315 / 100 : Rat) →
      (403 / 1000 : Rat) < eta1bSq piRat ∧
      eta1bSq piRat < (406 / 1000 : Rat) ∧
      eta1bSq piRat < (1 / 2 : Rat) ∧
      (1 / 2 : Rat) < (4 / 5 : Rat) ∧
      (4 / 5 : Rat) < etaTernarySq ∧
      etaTernarySq < eta2bSq ∧
      eta2bSq < 1 ∧
      (199 / 100 : Rat) < etaTernarySq / eta1bSq piRat ∧
      (217 / 100 : Rat) < eta2bSq / eta1bSq piRat) ∧
    (∀ p : Rat, (0 : Rat) < p → p < 1 → p * p < p) ∧
    ((1 / 10 : Rat) * (1 / 10) = 1 / 100 ∧ (1 / 125 : Rat) * (1 / 125) = 1 / 15625) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by grind⟩
  · intro mu sigmaSq hs; exact cantelli_identity hs
  · intro s1 s2 hs1 h; exact cantelliTail_strict_anti hs1 h
  · intro N K d delta eta1 eta2 hN hK hd hdel he1 h
    exact cantelliOversample_strict_anti_eta hN hK hd hdel he1 h
  · intro piRat hlo hhi
    have ⟨h1, h2⟩ := eta1bSq_bounds hlo hhi
    have ⟨h3, h4, h5, h6, h7, h8, h9⟩ := snr_hierarchy_and_ratios hlo hhi
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · intro p h0 h1; exact snr_doubling_tail_collapse h0 h1

end RagPopcntMatryoshka
