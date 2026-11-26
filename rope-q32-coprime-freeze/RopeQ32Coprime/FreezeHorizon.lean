/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RopeQ32Coprime.Defs
import RopeQ32Coprime.RatOrder

/-!
# Pillar 1: Exact Binade ULP Freeze Runs, FP16 `+Inf` Overflow Cliff, and High-Frequency Random-Phase Horizon

Proves Theorems 1 and 2 of `RopeQ32CoprimeChallenge` using pure `Init` arithmetic.
-/

namespace RopeQ32Coprime

/-! ### Helper Lemmas on Powers of 2 and `binadeRneNat` -/

theorem pow2_pos (n : Nat) : 0 < 2 ^ n :=
  Nat.pow_pos (by decide)

theorem binadeUlp_mul_pow2 {p k : Nat} (h : p ≤ k) :
    binadeUlp p k * 2 ^ (p + 1) = 2 ^ (k + 1) := by
  unfold binadeUlp
  rw [← Nat.pow_add]
  congr 1
  omega

theorem pow2_div_binadeUlp {p k : Nat} (h : p ≤ k) :
    2 ^ (k + 1) / 2 ^ (p + 1) = binadeUlp p k := by
  rw [← binadeUlp_mul_pow2 h]
  exact Nat.mul_div_cancel (binadeUlp p k) (pow2_pos (p + 1))

theorem binadeUlp_eq_div {p k : Nat} (h : p ≤ k) :
    2 ^ k / 2 ^ p = binadeUlp p k := by
  unfold binadeUlp
  have hmul : 2 ^ (k - p) * 2 ^ p = 2 ^ k := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [← hmul]
  exact Nat.mul_div_cancel (2 ^ (k - p)) (pow2_pos p)

theorem binadeUlp_eq_two_mul_half {p k : Nat} (h : p < k) :
    binadeUlp p k = 2 * 2 ^ (k - p - 1) := by
  unfold binadeUlp
  have hsub : k - p = (k - p - 1) + 1 := by omega
  conv => lhs; rw [hsub, Nat.pow_succ, Nat.mul_comm]

theorem binadeRneNat_exact_of_le {p k m : Nat} (h : k ≤ p) :
    binadeRneNat p k m = m := by
  unfold binadeRneNat
  simp [h]

theorem binadeRneNat_even_run {p k q m : Nat} (hpk : p < k) (hq_pos : 0 < q) (hq_even : q % 2 = 0)
    (hlo : q * binadeUlp p k - 2 ^ (k - p - 1) ≤ m)
    (hhi : m ≤ q * binadeUlp p k + 2 ^ (k - p - 1)) :
    binadeRneNat p k m = q * binadeUlp p k := by
  have hnotle : ¬ k ≤ p := by omega
  unfold binadeRneNat
  simp only [hnotle, ↓reduceIte]
  let u := 2 ^ (k - p)
  let h := 2 ^ (k - p - 1)
  have hu_eq : u = 2 * h := binadeUlp_eq_two_mul_half hpk
  have hh_pos : 0 < h := pow2_pos (k - p - 1)
  have hu_pos : 0 < u := by omega
  have hlo' : q * u - h ≤ m := hlo
  have hhi' : m ≤ q * u + h := hhi
  change (if m % u < h then m / u * u
    else if h < m % u then (m / u + 1) * u
    else if m / u % 2 = 0 then m / u * u
    else (m / u + 1) * u) = q * u
  by_cases hge : q * u ≤ m
  · have hdiv : m / u = q := by
      have h2 : m < (q + 1) * u := by
        have : (q + 1) * u = q * u + u := by rw [Nat.add_mul, Nat.one_mul]
        omega
      have hdiv_ge : q ≤ m / u := (Nat.le_div_iff_mul_le hu_pos).mpr hge
      have hdiv_lt : m / u < q + 1 := (Nat.div_lt_iff_lt_mul hu_pos).mpr h2
      omega
    have hrem : m % u = m - q * u := by
      have hdm := Nat.div_add_mod m u
      rw [hdiv, Nat.mul_comm u q] at hdm
      omega
    rw [hdiv, hrem]
    by_cases hlt : m - q * u < h
    · simp [hlt]
    · have heq : m - q * u = h := by omega
      simp [heq, hq_even]
  · have hq_eq : q * u = (q - 1) * u + u := by
      have : q = (q - 1) + 1 := by omega
      conv => lhs; rw [this]
      rw [Nat.add_mul, Nat.one_mul]
    have hdiv : m / u = q - 1 := by
      have h1 : (q - 1) * u ≤ m := by omega
      have h2 : m < q * u := by omega
      have hdiv_ge : q - 1 ≤ m / u := (Nat.le_div_iff_mul_le hu_pos).mpr h1
      have hdiv_lt : m / u < q := (Nat.div_lt_iff_lt_mul hu_pos).mpr h2
      omega
    have hrem : m % u = m - (q - 1) * u := by
      have hdm := Nat.div_add_mod m u
      rw [hdiv, Nat.mul_comm u (q - 1)] at hdm
      omega
    have hq1_odd : (q - 1) % 2 ≠ 0 := by omega
    have hq_succ : q - 1 + 1 = q := by omega
    rw [hdiv, hrem]
    have hnotlt : ¬ m - (q - 1) * u < h := by omega
    by_cases hgt : h < m - (q - 1) * u
    · simp [hnotlt, hgt, hq_succ]
    · simp [hnotlt, hgt, hq1_odd, hq_succ]

theorem binadeRneNat_odd_run {p k q m : Nat} (hpk : p < k) (hq_odd : q % 2 = 1)
    (hlo : q * binadeUlp p k - 2 ^ (k - p - 1) + 1 ≤ m)
    (hhi : m ≤ q * binadeUlp p k + 2 ^ (k - p - 1) - 1) :
    binadeRneNat p k m = q * binadeUlp p k := by
  have hnotle : ¬ k ≤ p := by omega
  unfold binadeRneNat
  simp only [hnotle, ↓reduceIte]
  let u := 2 ^ (k - p)
  let h := 2 ^ (k - p - 1)
  have hu_eq : u = 2 * h := binadeUlp_eq_two_mul_half hpk
  have hh_pos : 0 < h := pow2_pos (k - p - 1)
  have hu_pos : 0 < u := by omega
  have hq_pos : 0 < q := by omega
  have hlo' : q * u - h + 1 ≤ m := hlo
  have hhi' : m ≤ q * u + h - 1 := hhi
  change (if m % u < h then m / u * u
    else if h < m % u then (m / u + 1) * u
    else if m / u % 2 = 0 then m / u * u
    else (m / u + 1) * u) = q * u
  by_cases hge : q * u ≤ m
  · have hdiv : m / u = q := by
      have h2 : m < (q + 1) * u := by
        have : (q + 1) * u = q * u + u := by rw [Nat.add_mul, Nat.one_mul]
        omega
      have hdiv_ge : q ≤ m / u := (Nat.le_div_iff_mul_le hu_pos).mpr hge
      have hdiv_lt : m / u < q + 1 := (Nat.div_lt_iff_lt_mul hu_pos).mpr h2
      omega
    have hrem : m % u = m - q * u := by
      have hdm := Nat.div_add_mod m u
      rw [hdiv, Nat.mul_comm u q] at hdm
      omega
    have hlt : m - q * u < h := by omega
    rw [hdiv, hrem]
    simp [hlt]
  · have hq_eq : q * u = (q - 1) * u + u := by
      have : q = (q - 1) + 1 := by omega
      conv => lhs; rw [this]
      rw [Nat.add_mul, Nat.one_mul]
    have hdiv : m / u = q - 1 := by
      have h1 : (q - 1) * u ≤ m := by omega
      have h2 : m < q * u := by omega
      have hdiv_ge : q - 1 ≤ m / u := (Nat.le_div_iff_mul_le hu_pos).mpr h1
      have hdiv_lt : m / u < q := (Nat.div_lt_iff_lt_mul hu_pos).mpr h2
      omega
    have hrem : m % u = m - (q - 1) * u := by
      have hdm := Nat.div_add_mod m u
      rw [hdiv, Nat.mul_comm u (q - 1)] at hdm
      omega
    have hgt : h < m - (q - 1) * u := by omega
    have hnotlt : ¬ m - (q - 1) * u < h := by omega
    have hq_succ : q - 1 + 1 = q := by omega
    rw [hdiv, hrem]
    simp [hnotlt, hgt, hq_succ]

theorem fp16_overflow_iff (m : Nat) (hlo : 2 ^ 15 ≤ m) (hhi : m < 2 ^ 16) :
    binadeRneNat 10 15 m = 2 ^ 16 ↔ fp16OverflowThreshold ≤ m := by
  unfold binadeRneNat fp16OverflowThreshold fp16MaxNormal fp16TopUlp binadeUlp
  simp only [show ¬ (15 : Nat) ≤ 10 by decide, ↓reduceIte]
  have hu : (2 ^ (15 - 10) : Nat) = 32 := by decide
  have hh : (2 ^ (15 - 10 - 1) : Nat) = 16 := by decide
  rw [hu, hh]
  constructor
  · intro h
    by_cases hm : 65520 ≤ m
    · exact hm
    · exfalso
      have hlt : m < 65520 := by omega
      by_cases hq2047 : m / 32 = 2047
      · have hr : m % 32 < 16 := by omega
        rw [hq2047] at h
        simp [hr] at h
      · have hq_lt : m / 32 < 2047 := by omega
        split at h <;> try split at h <;> try split at h
        all_goals omega
  · intro hm
    have hq : m / 32 = 2047 := by omega
    have hr : 16 ≤ m % 32 := by omega
    rw [hq]
    have hnotlt : ¬ m % 32 < 16 := by omega
    by_cases hgt : 16 < m % 32
    · simp [hnotlt, hgt]
    · simp [hnotlt, hgt]

/-! ### Headline Theorem 1: `rope_bf16_fp16_consecutive_freeze_run_exact` -/

theorem rope_bf16_fp16_consecutive_freeze_run_exact :
    (∀ p k : Nat, p ≤ k →
      binadeUlp p k * 2 ^ (p + 1) = 2 ^ (k + 1) ∧
      2 ^ (k + 1) / 2 ^ (p + 1) = binadeUlp p k ∧
      2 ^ k / 2 ^ p = binadeUlp p k) ∧
    (∀ p k q : Nat, p < k → 0 < q → q % 2 = 0 →
      (∀ m : Nat, q * binadeUlp p k - 2 ^ (k - p - 1) ≤ m →
        m ≤ q * binadeUlp p k + 2 ^ (k - p - 1) →
        binadeRneNat p k m = q * binadeUlp p k) ∧
      (q * binadeUlp p k + 2 ^ (k - p - 1)) - (q * binadeUlp p k - 2 ^ (k - p - 1)) + 1 =
        binadeUlp p k + 1) ∧
    (∀ p k q : Nat, p < k → q % 2 = 1 →
      (∀ m : Nat, q * binadeUlp p k - 2 ^ (k - p - 1) + 1 ≤ m →
        m ≤ q * binadeUlp p k + 2 ^ (k - p - 1) - 1 →
        binadeRneNat p k m = q * binadeUlp p k) ∧
      (q * binadeUlp p k + 2 ^ (k - p - 1) - 1) - (q * binadeUlp p k - 2 ^ (k - p - 1) + 1) + 1 =
        binadeUlp p k - 1) ∧
    (∀ p k : Nat, p < k → (binadeUlp p k + 1) + (binadeUlp p k - 1) = 2 * binadeUlp p k) ∧
    (binadeUlp 7 12 = 32 ∧ binadeUlp 7 15 = 256 ∧
     binadeUlp 7 17 = 1024 ∧ binadeUlp 7 20 = 8192 ∧
     binadeUlp 10 12 = 4 ∧ binadeUlp 10 15 = 32 ∧
     binadeUlp 23 29 = 64) ∧
    (∀ k m : Nat, k ≤ 23 → binadeRneNat 23 k m = m) ∧
    (fp16MaxNormal = 65504 ∧ fp16TopUlp = 32 ∧ fp16OverflowThreshold = 65520 ∧
     (∀ m : Nat, 2 ^ 15 ≤ m → m < 2 ^ 16 →
       (binadeRneNat 10 15 m = 2 ^ 16 ↔ fp16OverflowThreshold ≤ m)) ∧
     131072 - fp16OverflowThreshold = 65552 ∧
     1048576 - fp16OverflowThreshold = 983056) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k hpk
    exact ⟨binadeUlp_mul_pow2 hpk, pow2_div_binadeUlp hpk, binadeUlp_eq_div hpk⟩
  · intro p k q hpk hq_pos hq_even
    refine ⟨fun m hlo hhi => binadeRneNat_even_run hpk hq_pos hq_even hlo hhi, ?_⟩
    have hu := binadeUlp_eq_two_mul_half hpk
    have hh : 0 < 2 ^ (k - p - 1) := pow2_pos (k - p - 1)
    have hq_ge : 2 ^ (k - p - 1) ≤ q * binadeUlp p k := by
      have : 1 * binadeUlp p k ≤ q * binadeUlp p k := Nat.mul_le_mul_right _ hq_pos
      omega
    omega
  · intro p k q hpk hq_odd
    refine ⟨fun m hlo hhi => binadeRneNat_odd_run hpk hq_odd hlo hhi, ?_⟩
    have hu := binadeUlp_eq_two_mul_half hpk
    have hh : 0 < 2 ^ (k - p - 1) := pow2_pos (k - p - 1)
    have hq_pos : 0 < q := by omega
    have hq_ge : 2 ^ (k - p - 1) ≤ q * binadeUlp p k := by
      have : 1 * binadeUlp p k ≤ q * binadeUlp p k := Nat.mul_le_mul_right _ hq_pos
      omega
    omega
  · intro p k hpk
    have hu := binadeUlp_eq_two_mul_half hpk
    have hh : 0 < 2 ^ (k - p - 1) := pow2_pos (k - p - 1)
    omega
  · decide
  · intro k m hk
    exact binadeRneNat_exact_of_le hk
  · refine ⟨by decide, by decide, by decide, fp16_overflow_iff, by decide, by decide⟩

/-! ### Headline Theorem 2: `rope_high_freq_random_phase_horizon_exact` -/

theorem high_freq_rne_at_horizon (p : Nat) (hp : 1 ≤ p) :
    binadeRneNat p (p + 1) (highFreqRandomPhasePos p) = 2 ^ (p + 1) := by
  have hlt : p < p + 1 := Nat.lt_succ_self p
  have hq_pos : 0 < 2 ^ p := pow2_pos p
  have hq_even : (2 ^ p) % 2 = 0 := by
    have hp1 : p = (p - 1) + 1 := by omega
    rw [hp1, Nat.pow_succ]
    omega
  have hu : binadeUlp p (p + 1) = 2 := by
    unfold binadeUlp
    have : p + 1 - p = 1 := by omega
    rw [this]
  have hh : 2 ^ (p + 1 - p - 1) = 1 := by
    have : p + 1 - p - 1 = 0 := by omega
    rw [this]
  have hmul : 2 ^ p * binadeUlp p (p + 1) = 2 ^ (p + 1) := by
    rw [hu, Nat.pow_succ]
  have h := binadeRneNat_even_run hlt hq_pos hq_even
    (m := highFreqRandomPhasePos p)
    (by unfold highFreqRandomPhasePos; rw [hmul, hh]; omega)
    (by unfold highFreqRandomPhasePos; rw [hmul, hh]; omega)
  rw [hmul] at h
  exact h

theorem rope_high_freq_random_phase_horizon_exact :
    (∀ p k m : Nat, k ≤ p → binadeRneNat p k m = m) ∧
    (highFreqRandomPhasePos 7 = 257 ∧
     highFreqRandomPhasePos 10 = 2049 ∧
     highFreqRandomPhasePos 23 = 16777217) ∧
    (∀ p k : Nat, p + 1 ≤ k → 2 ≤ binadeUlp p k ∧ 1 ≤ 2 ^ (k - p - 1)) ∧
    (∀ p : Nat, 1 ≤ p →
      binadeUlp p (p + 1) = 2 ∧
      binadeRneNat p (p + 1) (highFreqRandomPhasePos p) = 2 ^ (p + 1) ∧
      highFreqRandomPhasePos p - binadeRneNat p (p + 1) (highFreqRandomPhasePos p) = 1) ∧
    (∀ piRat : Rat, piRat ≤ 22 / 7 →
      piRat / 4 < (1 : Rat) ∧ piRat / 2 < (2 : Rat)) ∧
    ((1 : Rat) - 2 * (1 / 8 : Rat) = 3 / 4) := by
  refine ⟨?_, by decide, ?_, ?_, ?_, by grind⟩
  · intro p k m hk
    exact binadeRneNat_exact_of_le hk
  · intro p k hk
    unfold binadeUlp
    have h1 : 1 ≤ k - p := by omega
    have h2 : 2 ^ 1 ≤ 2 ^ (k - p) := Nat.pow_le_pow_right (by decide) h1
    exact ⟨h2, pow2_pos (k - p - 1)⟩
  · intro p hp
    have hu : binadeUlp p (p + 1) = 2 := by
      unfold binadeUlp
      have : p + 1 - p = 1 := by omega
      rw [this]
    have hr := high_freq_rne_at_horizon p hp
    refine ⟨hu, hr, ?_⟩
    rw [hr]
    unfold highFreqRandomPhasePos
    omega
  · intro piRat hpi
    have h4 : piRat / 4 ≤ (22 / 7 : Rat) / 4 := by
      apply rat_div_le_of_mul_le (by decide)
      have : ((22 / 7 : Rat) / 4) * 4 = 22 / 7 := by grind
      rw [this]; exact hpi
    have h2 : piRat / 2 ≤ (22 / 7 : Rat) / 2 := by
      apply rat_div_le_of_mul_le (by decide)
      have : ((22 / 7 : Rat) / 2) * 2 = 22 / 7 := by grind
      rw [this]; exact hpi
    have hlt4 : (22 / 7 : Rat) / 4 < 1 := by
      apply rat_lt_of_sub_pos
      have heq : (1 : Rat) - (22 / 7 : Rat) / 4 = 6 / 28 := by grind
      rw [heq]
      have hpos : (0 : Rat) < 6 / 28 := by
        apply rat_lt_of_sub_pos
        have h0 : (6 / 28 : Rat) - 0 = 6 / 28 := by grind
        rw [h0]
        have hmul : (0 : Rat) * 28 < (6 / 28 : Rat) * 28 := by
          rw [Rat.zero_mul, rat_div_mul_cancel (by decide)]; decide
        cases Rat.le_total (a := (0 : Rat)) (b := (6 / 28 : Rat)) with
        | inl hge =>
          have hne : (6 / 28 : Rat) ≠ 0 := by intro h0; rw [h0, Rat.zero_mul] at hmul; exact Rat.not_le.mpr hmul Rat.le_refl
          exact Rat.lt_of_le_of_ne hge (Ne.symm hne)
        | inr hle =>
          exact False.elim (Rat.not_le.mpr hmul (rat_mul_le_mul_of_nonneg_right hle (by decide)))
      exact hpos
    have hlt2 : (22 / 7 : Rat) / 2 < 2 := by
      have heq : (22 / 7 : Rat) / 2 = 2 * ((22 / 7 : Rat) / 4) := by grind
      rw [heq]
      have hmul := rat_mul_lt_mul_of_pos_left hlt4 (by decide : (0 : Rat) < 2)
      rw [Rat.mul_one] at hmul
      exact hmul
    exact ⟨rat_lt_of_le_of_lt h4 hlt4, rat_lt_of_le_of_lt h2 hlt2⟩

end RopeQ32Coprime
