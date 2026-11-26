/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RagPopcntMatryoshka.RatOrder

/-!
# Theorem 3: Matryoshka Prefix-Truncation vs Full-Dim Quantized Spectral Crossover

Proves:
1. Exact crossover `iff`: `energyFrac dM h lam < etaSq ↔ prefixEnergy dM h lam < etaSq * totalEnergy lam`.
2. Universal strict monotonicity of `energyFrac dM h lam` under steeper spectral decay
   (whenever `lam2 j / lam1 j` is strictly decreasing, covering all power-law spectra `i^(-β)`).
3. Exact certified rational crossover bounds at equal `192 B/vec` (`D = 1536, d_M = 96`):
   flat (`β = 0`: `1/16 < 4/π²`) vs steep (`Θ(i^{-2})` telescoping spectrum: `1537/1552 > 99/100 > η_{2b}²`).
-/

namespace RagPopcntMatryoshka

theorem totalEnergy_eq_prefix_add_tail {D dM : Nat} (h : dM ≤ D) (lam : Fin D → Rat) :
    totalEnergy lam = prefixEnergy dM h lam + tailEnergy dM h lam := by
  unfold totalEnergy prefixEnergy tailEnergy
  exact finSumRat_split_le h lam

theorem totalEnergy_pos {D : Nat} (hD : 0 < D) {lam : Fin D → Rat}
    (hpos : ∀ i, (0 : Rat) < lam i) : (0 : Rat) < totalEnergy lam :=
  finSumRat_pos hD hpos

theorem energyFrac_crossover_iff {D dM : Nat} (hD : 0 < D) (h : dM ≤ D)
    {lam : Fin D → Rat} (hpos : ∀ i, (0 : Rat) < lam i) (etaSq : Rat) :
    (energyFrac dM h lam < etaSq ↔ prefixEnergy dM h lam < etaSq * totalEnergy lam) ∧
    (etaSq < energyFrac dM h lam ↔ etaSq * totalEnergy lam < prefixEnergy dM h lam) ∧
    (0 : Rat) ≤ energyFrac dM h lam ∧ energyFrac dM h lam ≤ 1 := by
  have htot : (0 : Rat) < totalEnergy lam := totalEnergy_pos hD hpos
  have hpre : (0 : Rat) ≤ prefixEnergy dM h lam :=
    finSumRat_nonneg (fun i => Rat.le_of_lt (hpos _))
  have htail : (0 : Rat) ≤ tailEnergy dM h lam :=
    finSumRat_nonneg (fun i => Rat.le_of_lt (hpos _))
  have hsplit := totalEnergy_eq_prefix_add_tail h lam
  unfold energyFrac
  refine ⟨rat_div_lt_iff htot, rat_lt_div_iff htot, rat_div_nonneg hpre htot, ?_⟩
  rw [rat_div_le_iff htot]
  have h1 : (1 : Rat) * totalEnergy lam = prefixEnergy dM h lam + tailEnergy dM h lam := by
    rw [Rat.one_mul, hsplit]
  rw [h1]
  have h2 := rat_add_le_add (Rat.le_refl (a := prefixEnergy dM h lam)) htail
  have h0 : prefixEnergy dM h lam + 0 = prefixEnergy dM h lam := by grind
  rw [h0] at h2
  exact h2

theorem energyFrac_strict_mono_of_steeper {D dM : Nat} (hdM : 0 < dM) (hlt : dM < D)
    {lam1 lam2 : Fin D → Rat}
    (hpos1 : ∀ i, (0 : Rat) < lam1 i) (hpos2 : ∀ i, (0 : Rat) < lam2 i)
    (hsteep : ∀ i j : Fin D, i.val < j.val → lam2 j * lam1 i < lam2 i * lam1 j) :
    energyFrac dM (Nat.le_of_lt hlt) lam1 < energyFrac dM (Nat.le_of_lt hlt) lam2 := by
  have hD : 0 < D := Nat.lt_trans hdM hlt
  have hle : dM ≤ D := Nat.le_of_lt hlt
  have htot1 : (0 : Rat) < totalEnergy lam1 := totalEnergy_pos hD hpos1
  have htot2 : (0 : Rat) < totalEnergy lam2 := totalEnergy_pos hD hpos2
  apply rat_div_lt_div_of_cross htot1 htot2
  rw [totalEnergy_eq_prefix_add_tail hle lam2, totalEnergy_eq_prefix_add_tail hle lam1]
  have hcross : prefixEnergy dM hle lam1 * tailEnergy dM hle lam2 <
      prefixEnergy dM hle lam2 * tailEnergy dM hle lam1 := by
    unfold prefixEnergy tailEnergy
    rw [finSumRat_mul_finSumRat, finSumRat_mul_finSumRat]
    apply finSumRat_lt_finSumRat hdM
    intro i
    apply finSumRat_lt_finSumRat (by omega : 0 < D - dM)
    intro j
    have hij : i.val < dM + j.val := by omega
    have hstep := hsteep ⟨i.val, Nat.lt_of_lt_of_le i.isLt hle⟩ ⟨dM + j.val, by omega⟩ hij
    rw [Rat.mul_comm (lam1 _)]
    exact hstep
  apply rat_lt_of_sub_pos
  have eq :
      prefixEnergy dM hle lam2 * (prefixEnergy dM hle lam1 + tailEnergy dM hle lam1) -
      prefixEnergy dM hle lam1 * (prefixEnergy dM hle lam2 + tailEnergy dM hle lam2) =
      prefixEnergy dM hle lam2 * tailEnergy dM hle lam1 -
      prefixEnergy dM hle lam1 * tailEnergy dM hle lam2 := by grind
  rw [eq]
  exact rat_sub_pos hcross

theorem flatSpectrum_energyFrac {D dM : Nat} (h : dM ≤ D) :
    energyFrac dM h (flatSpectrum D) = (dM : Rat) / (D : Rat) := by
  unfold energyFrac prefixEnergy totalEnergy flatSpectrum
  rw [finSumRat_const, finSumRat_const, Rat.mul_one, Rat.mul_one]

theorem telescoping_partial_sum (n : Nat) :
    finSumRat (fun i : Fin n =>
      (1 : Rat) / (((i.val + 1 : Nat) : Rat) * ((i.val + 2 : Nat) : Rat))) =
    (n : Rat) / ((n + 1 : Nat) : Rat) := by
  induction n with
  | zero => simp [finSumRat]; grind
  | succ k ih =>
    simp only [finSumRat]
    have hcast : (fun i : Fin k =>
        (1 : Rat) / (((i.castSucc.val + 1 : Nat) : Rat) * ((i.castSucc.val + 2 : Nat) : Rat))) =
        (fun i : Fin k =>
        (1 : Rat) / (((i.val + 1 : Nat) : Rat) * ((i.val + 2 : Nat) : Rat))) := rfl
    rw [hcast, ih]
    have hc1 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
    have hc2 : ((k + 2 : Nat) : Rat) = (k : Rat) + 2 := by grind
    have hk1 : ((k + 1 : Nat) : Rat) ≠ 0 := by grind
    have hk2 : ((k + 2 : Nat) : Rat) ≠ 0 := by grind
    have hlast : (Fin.last k).val = k := rfl
    rw [hlast]
    have hprod : ((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat) ≠ 0 := by
      intro h0
      cases Rat.mul_eq_zero.mp h0 with
      | inl h => exact hk1 h
      | inr h => exact hk2 h
    apply rat_mul_right_cancel (c := ((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat)) hprod
    have hL1 : ((k : Rat) / ((k + 1 : Nat) : Rat)) *
        (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat)) =
        (k : Rat) * ((k + 2 : Nat) : Rat) := by
      rw [Rat.div_def]
      have eq : (k : Rat) * (((k + 1 : Nat) : Rat))⁻¹ * (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat)) =
          (k : Rat) * ((((k + 1 : Nat) : Rat))⁻¹ * ((k + 1 : Nat) : Rat)) * ((k + 2 : Nat) : Rat) := by grind
      rw [eq, Rat.inv_mul_cancel _ hk1, Rat.mul_one]
    have hL2 : ((1 : Rat) / (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat))) *
        (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat)) = 1 := by
      rw [Rat.div_def, Rat.one_mul, Rat.inv_mul_cancel _ hprod]
    have hR : (((k + 1 : Nat) : Rat) / ((k + 2 : Nat) : Rat)) *
        (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat)) =
        ((k + 1 : Nat) : Rat) * ((k + 1 : Nat) : Rat) := by
      rw [Rat.div_def]
      have eq : ((k + 1 : Nat) : Rat) * (((k + 2 : Nat) : Rat))⁻¹ *
          (((k + 1 : Nat) : Rat) * ((k + 2 : Nat) : Rat)) =
          ((k + 1 : Nat) : Rat) * ((k + 1 : Nat) : Rat) *
          ((((k + 2 : Nat) : Rat))⁻¹ * ((k + 2 : Nat) : Rat)) := by grind
      rw [eq, Rat.inv_mul_cancel _ hk2, Rat.mul_one]
    rw [Rat.add_mul, hL1, hL2, hR, hc1, hc2]
    grind

theorem telescopingInvSq_energyFrac {D dM : Nat} (h : dM ≤ D) :
    energyFrac dM h (telescopingInvSqSpectrum D) =
    ((dM : Rat) / ((dM + 1 : Nat) : Rat)) / ((D : Rat) / ((D + 1 : Nat) : Rat)) := by
  unfold energyFrac prefixEnergy totalEnergy telescopingInvSqSpectrum
  rw [telescoping_partial_sum dM, telescoping_partial_sum D]

/-- Headline Theorem 3 (`matryoshka_vs_full_dim_binary_spectral_crossover_exact`). -/
theorem matryoshka_vs_full_dim_binary_spectral_crossover_exact :
    (∀ (D dM : Nat), 0 < D → ∀ (h : dM ≤ D) (lam : Fin D → Rat),
      (∀ i, (0 : Rat) < lam i) →
      ∀ etaSq : Rat,
        (energyFrac dM h lam < etaSq ↔ prefixEnergy dM h lam < etaSq * totalEnergy lam) ∧
        (etaSq < energyFrac dM h lam ↔ etaSq * totalEnergy lam < prefixEnergy dM h lam) ∧
        (0 : Rat) ≤ energyFrac dM h lam ∧ energyFrac dM h lam ≤ 1) ∧
    (∀ (D dM : Nat), 0 < dM → ∀ (hlt : dM < D) (lam1 lam2 : Fin D → Rat),
      (∀ i, (0 : Rat) < lam1 i) →
      (∀ i, (0 : Rat) < lam2 i) →
      (∀ i j : Fin D, i.val < j.val → lam2 j * lam1 i < lam2 i * lam1 j) →
      energyFrac dM (Nat.le_of_lt hlt) lam1 < energyFrac dM (Nat.le_of_lt hlt) lam2) ∧
    (energyFrac 96 (by decide : 96 ≤ 1536) (flatSpectrum 1536) = (1 / 16 : Rat) ∧
     ∀ piRat : Rat, (314 / 100 : Rat) ≤ piRat → piRat ≤ (315 / 100 : Rat) →
       energyFrac 96 (by decide : 96 ≤ 1536) (flatSpectrum 1536) < eta1bSq piRat) ∧
    (energyFrac 96 (by decide : 96 ≤ 1536) (telescopingInvSqSpectrum 1536) = (1537 / 1552 : Rat) ∧
     eta2bSq < energyFrac 96 (by decide : 96 ≤ 1536) (telescopingInvSqSpectrum 1536) ∧
     (99 / 100 : Rat) < energyFrac 96 (by decide : 96 ≤ 1536) (telescopingInvSqSpectrum 1536)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D dM hD h lam hpos etaSq
    exact energyFrac_crossover_iff hD h hpos etaSq
  · intro D dM hdM hlt lam1 lam2 hpos1 hpos2 hsteep
    exact energyFrac_strict_mono_of_steeper hdM hlt hpos1 hpos2 hsteep
  · constructor
    · rw [flatSpectrum_energyFrac]; grind
    · intro piRat hlo hhi
      rw [flatSpectrum_energyFrac]
      have hpos : (0 : Rat) < piRat := rat_lt_of_lt_of_le (by grind : (0 : Rat) < 314 / 100) hlo
      have hsq_pos : (0 : Rat) < piRat * piRat := rat_mul_pos hpos hpos
      have hsq_hi : piRat * piRat ≤ (315 / 100 : Rat) * (315 / 100) :=
        Rat.le_trans (rat_mul_le_mul_of_nonneg_left hhi (Rat.le_of_lt hpos))
          (rat_mul_le_mul_of_nonneg_right hhi (by grind : (0 : Rat) ≤ 315 / 100))
      unfold eta1bSq
      rw [rat_lt_div_iff hsq_pos]
      have h1 := rat_mul_le_mul_of_nonneg_left hsq_hi (by grind : (0 : Rat) ≤ (96 : Rat) / (1536 : Rat))
      exact rat_lt_of_le_of_lt h1 (by grind)
  · have htel : energyFrac 96 (by decide : 96 ≤ 1536) (telescopingInvSqSpectrum 1536) = (1537 / 1552 : Rat) := by
      rw [telescopingInvSq_energyFrac]
      grind
    rw [htel]
    exact ⟨rfl, by unfold eta2bSq; grind, by grind⟩

end RagPopcntMatryoshka
