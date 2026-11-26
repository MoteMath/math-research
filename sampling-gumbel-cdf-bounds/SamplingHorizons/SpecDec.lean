/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SamplingHorizons.RatOrder

/-!
# Pillar 2: Speculative Decoding Exact Losslessness, Zero-Residual Crash, and `Q32` Exact Fix

Proves:
- Headline Theorem 2 (`specdec_exact_losslessness_vs_finite_residual_crash`):
  Exact Leviathan et al. (2023) losslessness `specDecOut p q v = p v` and `tvDist = 0` over `Rat`,
  universal finite-precision zero-residual crash (`Z_fl = 0` -> `0/0 = NaN`) & exact TV leak,
  plus bit-exact `FP8-E4M3` (`V = 64`) and `BF16` (`V = 2`) RNE witnesses where `Z_exact > 0`
  yet `Z_fl = 0`.
- Headline Theorem 3 (`specdec_q32_integer_exact_zero_leak`):
  Exact fixed-point integer `Q_B` (and `Q32`, `D = 2^32`) conservation, exact division-free
  cross-multiplication acceptance test with zero over-accepts, zero `Z = 0` NaN crashes
  whenever `P ≠ Q`, and exact `0` TV leak.
-/

namespace SamplingHorizons

theorem specDecAcceptProb_add_Z {n : Nat} (p q : Fin n → Rat) (hp : finSum p = 1) :
    specDecAcceptProb p q + specDecZ p q = 1 := by
  unfold specDecAcceptProb specDecZ specDecRes
  rw [← finSum_add]
  have hcongr : finSum (fun v : Fin n => ratMin (p v) (q v) + ratMax 0 (p v - q v)) = finSum p := by
    apply finSum_congr
    intro v
    exact ratMin_add_ratMax_sub (p v) (q v)
  rw [hcongr, hp]

theorem specDecOut_exact_of_pos {n : Nat} (p q : Fin n → Rat)
    (hp : finSum p = 1) (hZ : 0 < specDecZ p q) (v : Fin n) :
    specDecOut p q v = p v := by
  have hsum := specDecAcceptProb_add_Z p q hp
  have h1sub : 1 - specDecAcceptProb p q = specDecZ p q := by grind
  have hZne : specDecZ p q ≠ 0 := Rat.ne_of_gt hZ
  unfold specDecOut
  simp only [hZne, ite_false]
  rw [h1sub, rat_mul_div_cancel hZne]
  exact ratMin_add_ratMax_sub (p v) (q v)

theorem tvDist_self {n : Nat} (p : Fin n → Rat) : tvDist p p = 0 := by
  unfold tvDist
  have h0 : finSum (fun i : Fin n => ratAbs (p i - p i)) = 0 := by
    have hc : finSum (fun i : Fin n => ratAbs (p i - p i)) = finSum (fun _ : Fin n => (0 : Rat)) := by
      apply finSum_congr
      intro i
      have : p i - p i = 0 := by grind
      rw [this]; decide
    rw [hc, finSum_zero]
  rw [h0, Rat.mul_zero]

theorem specDecFlZ_zero_of_le {n : Nat} (fl : Rat → Rat) (p q : Fin n → Rat)
    (hle : ∀ v : Fin n, fl (p v) ≤ fl (q v)) :
    specDecFlZ fl p q = 0 := by
  unfold specDecFlZ
  have hc : finSum (fun v : Fin n => ratMax 0 (fl (p v) - fl (q v))) =
      finSum (fun _ : Fin n => (0 : Rat)) := by
    apply finSum_congr
    intro v
    have hsub : fl (p v) - fl (q v) ≤ 0 := by
      have := rat_sub_nonneg (hle v)
      grind
    unfold ratMax
    split
    · rename_i hge
      exact Rat.le_antisymm hsub hge
    · rfl
  rw [hc, finSum_zero]

theorem tvDist_crashed_unnorm {n : Nat} (p q : Fin n → Rat) :
    tvDist (specDecCrashedUnnorm p q) p = (1 / 2 : Rat) * specDecZ p q := by
  unfold tvDist specDecCrashedUnnorm specDecZ specDecRes
  congr 1
  apply finSum_congr
  intro v
  have hdecomp := ratMin_add_ratMax_sub (p v) (q v)
  have hdiff : ratMin (p v) (q v) - p v = -ratMax 0 (p v - q v) := by grind
  rw [hdiff]
  have hnonneg : (0 : Rat) ≤ ratMax 0 (p v - q v) := ratMax_zero_nonneg (p v - q v)
  have hnonpos : -ratMax 0 (p v - q v) ≤ 0 := by
    have := rat_sub_nonneg hnonneg
    grind
  rw [ratAbs_of_nonpos hnonpos]
  grind

theorem tvDist_fallback_dist {n : Nat} (p q : Fin n → Rat) (v0 : Fin n)
    (hp : finSum p = 1) (hv0 : p v0 ≤ q v0) :
    tvDist (specDecFallbackDist p q v0) p = specDecZ p q := by
  have hsum := specDecAcceptProb_add_Z p q hp
  have h1sub : 1 - specDecAcceptProb p q = specDecZ p q := by grind
  have hZnonneg : (0 : Rat) ≤ specDecZ p q := by
    unfold specDecZ specDecRes
    exact finSum_nonneg (fun v => ratMax_zero_nonneg (p v - q v))
  unfold tvDist specDecFallbackDist
  have hcongr : finSum (fun v : Fin n =>
      ratAbs (ratMin (p v) (q v) + (if v = v0 then 1 - specDecAcceptProb p q else 0) - p v)) =
      finSum (fun v : Fin n =>
        (if v = v0 then specDecZ p q else 0) + ratMax 0 (p v - q v)) := by
    apply finSum_congr
    intro v
    by_cases hv : v = v0
    · rw [hv]
      simp only [ite_true]
      have hmin : ratMin (p v0) (q v0) = p v0 := by
        unfold ratMin
        simp [hv0]
      have hres0 : ratMax 0 (p v0 - q v0) = 0 := by
        unfold ratMax
        have hsub : p v0 - q v0 ≤ 0 := by
          have := rat_sub_nonneg hv0
          grind
        split
        · rename_i hge
          exact Rat.le_antisymm hsub hge
        · rfl
      rw [hmin, h1sub, hres0, Rat.add_zero]
      have hsimp : p v0 + specDecZ p q - p v0 = specDecZ p q := by grind
      rw [hsimp, ratAbs_of_nonneg hZnonneg]
    · simp only [hv, ite_false, Rat.add_zero, Rat.zero_add]
      have hdecomp := ratMin_add_ratMax_sub (p v) (q v)
      have hdiff : ratMin (p v) (q v) - p v = -ratMax 0 (p v - q v) := by grind
      rw [hdiff]
      have hnonneg : (0 : Rat) ≤ ratMax 0 (p v - q v) := ratMax_zero_nonneg (p v - q v)
      have hnonpos : -ratMax 0 (p v - q v) ≤ 0 := by
        have := rat_sub_nonneg hnonneg
        grind
      rw [ratAbs_of_nonpos hnonpos]
      grind
  rw [hcongr, finSum_add, finSum_single]
  change (1 / 2 : Rat) * (specDecZ p q + specDecZ p q) = specDecZ p q
  grind

/-- Headline Theorem 2 (`specdec_exact_losslessness_vs_finite_residual_crash`). -/
theorem specdec_exact_losslessness_vs_finite_residual_crash :
    (∀ (n : Nat) (p q : Fin n → Rat), finSum p = 1 → 0 < specDecZ p q →
      specDecAcceptProb p q + specDecZ p q = 1 ∧
      (∀ v : Fin n, specDecOut p q v = p v) ∧
      tvDist (specDecOut p q) p = 0) ∧
    (∀ (n : Nat) (fl : Rat → Rat) (p q : Fin n → Rat), finSum p = 1 →
      (∀ v : Fin n, fl (p v) ≤ fl (q v)) →
      specDecFlZ fl p q = 0 ∧
      tvDist (specDecCrashedUnnorm p q) p = (1 / 2 : Rat) * specDecZ p q ∧
      (∀ v0 : Fin n, p v0 ≤ q v0 → tvDist (specDecFallbackDist p q v0) p = specDecZ p q)) ∧
    (let pE4M3 : Fin 64 → Rat := fun v => if v.val = 0 then 1 - 63 * invPow2Rat 11 else invPow2Rat 11
     let qE4M3 : Fin 64 → Rat := fun v => if v.val = 0 then 1 else 0
     let flE4M3 : Rat → Rat := fun x =>
       if ratAbs x ≤ invPow2Rat 10 then 0
       else if ratAbs (x - 1) < invPow2Rat 5 then 1 else x
     finSum pE4M3 = 1 ∧ finSum qE4M3 = 1 ∧
     specDecZ pE4M3 qE4M3 = 63 / 2048 ∧ (0 : Rat) < specDecZ pE4M3 qE4M3 ∧
     rneRoundsToGrid (invPow2Rat 4) 16 (pE4M3 ⟨0, by decide⟩) ∧
     (∀ v : Fin 64, v.val ≠ 0 → rneRoundsToGrid (invPow2Rat 9) 0 (pE4M3 v)) ∧
     specDecFlZ flE4M3 pE4M3 qE4M3 = 0 ∧
     tvDist (specDecFallbackDist pE4M3 qE4M3 ⟨0, by decide⟩) pE4M3 = 63 / 2048) ∧
    (let pBF16 : Fin 2 → Rat := fun v =>
       if v.val = 0 then (1 / 2 : Rat) + invPow2Rat 10 else (1 / 2 : Rat) - invPow2Rat 10
     let qBF16 : Fin 2 → Rat := fun _ => 1 / 2
     let flBF16 : Rat → Rat := fun x =>
       if ratAbs (x - 1 / 2) ≤ invPow2Rat 10 then 1 / 2 else x
     finSum pBF16 = 1 ∧ finSum qBF16 = 1 ∧
     specDecZ pBF16 qBF16 = 1 / 1024 ∧ (0 : Rat) < specDecZ pBF16 qBF16 ∧
     rneRoundsToGrid (invPow2Rat 8) 128 (pBF16 ⟨0, by decide⟩) ∧
     rneRoundsToGrid (invPow2Rat 9) 256 (pBF16 ⟨1, by decide⟩) ∧
     specDecFlZ flBF16 pBF16 qBF16 = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n p q hp hZ
    have hout := specDecOut_exact_of_pos p q hp hZ
    refine ⟨specDecAcceptProb_add_Z p q hp, hout, ?_⟩
    have hfun : specDecOut p q = p := funext hout
    rw [hfun]
    exact tvDist_self p
  · intro n fl p q hp hle
    exact ⟨specDecFlZ_zero_of_le fl p q hle,
           tvDist_crashed_unnorm p q,
           fun v0 hv0 => tvDist_fallback_dist p q v0 hp hv0⟩
  · -- Bit-exact FP8-E4M3 (V = 64) PeakedHead-LongTail witness
    dsimp only
    let pE4M3 : Fin 64 → Rat := fun v => if v.val = 0 then 1 - 63 * invPow2Rat 11 else invPow2Rat 11
    let qE4M3 : Fin 64 → Rat := fun v => if v.val = 0 then 1 else 0
    let flE4M3 : Rat → Rat := fun x =>
      if ratAbs x ≤ invPow2Rat 10 then 0
      else if ratAbs (x - 1) < invPow2Rat 5 then 1 else x
    have hpSum : finSum pE4M3 = 1 := by
      have hdecomp : finSum pE4M3 =
          finSum (fun v : Fin 64 =>
            (if v = ⟨0, by decide⟩ then 1 - 64 * invPow2Rat 11 else 0) + invPow2Rat 11) := by
        apply finSum_congr
        intro v
        by_cases hv : v.val = 0
        · have heq : v = ⟨0, by decide⟩ := Fin.ext hv
          simp only [pE4M3, heq, ite_true]
          grind
        · have hne : v ≠ ⟨0, by decide⟩ := fun h => hv (congrArg Fin.val h)
          simp only [pE4M3, hv, hne, ite_false, Rat.zero_add]
      rw [hdecomp, finSum_add, finSum_single, finSum_const]
      grind
    have hqSum : finSum qE4M3 = 1 := by
      have hc : finSum qE4M3 = finSum (fun v : Fin 64 => if v = ⟨0, by decide⟩ then (1 : Rat) else 0) := by
        apply finSum_congr
        intro v
        by_cases hv : v.val = 0
        · have heq : v = ⟨0, by decide⟩ := Fin.ext hv
          simp [qE4M3, heq]
        · simp [qE4M3]
      rw [hc, finSum_single]
    have hinv11_pos : (0 : Rat) < invPow2Rat 11 := invPow2Rat_pos 11
    have hZeq : specDecZ pE4M3 qE4M3 = 63 / 2048 := by
      unfold specDecZ specDecRes
      have hdecomp : finSum (fun v : Fin 64 => ratMax 0 (pE4M3 v - qE4M3 v)) =
          finSum (fun v : Fin 64 =>
            (if v = ⟨0, by decide⟩ then -invPow2Rat 11 else 0) + invPow2Rat 11) := by
        apply finSum_congr
        intro v
        by_cases hv : v.val = 0
        · have heq : v = ⟨0, by decide⟩ := Fin.ext hv
          simp only [pE4M3, qE4M3, heq, ite_true]
          have hneg : 1 - 63 * invPow2Rat 11 - 1 < 0 := by
            have h1 : 1 - 63 * invPow2Rat 11 - 1 = -(63 * invPow2Rat 11) := by grind
            rw [h1]
            exact rat_neg_of_pos (rat_mul_pos (by decide) hinv11_pos)
          have h0 : ratMax 0 (1 - 63 * invPow2Rat 11 - 1) = 0 := by
            unfold ratMax
            have hnot : ¬ ((0 : Rat) ≤ 1 - 63 * invPow2Rat 11 - 1) := Rat.not_le.mpr hneg
            simp [hnot]
          rw [h0]; grind
        · have hne : v ≠ ⟨0, by decide⟩ := fun h => hv (congrArg Fin.val h)
          simp only [pE4M3, qE4M3, hv, hne, ite_false, Rat.zero_add]
          have hpos : (0 : Rat) ≤ invPow2Rat 11 - 0 := by
            have : invPow2Rat 11 - 0 = invPow2Rat 11 := by grind
            rw [this]; exact Rat.le_of_lt hinv11_pos
          unfold ratMax
          simp [hpos]; grind
      rw [hdecomp, finSum_add, finSum_single, finSum_const]
      unfold invPow2Rat pow2Rat
      have h2048 : ((2 ^ 11 : Nat) : Rat) = (2048 : Rat) := by decide
      rw [h2048]
      grind
    have hflLe : ∀ v : Fin 64, flE4M3 (pE4M3 v) ≤ flE4M3 (qE4M3 v) := by
      have h_inv11_le_10 : invPow2Rat 11 ≤ invPow2Rat 10 := by
        have h := invPow2Rat_succ 10
        have hp := invPow2Rat_pos 11
        apply rat_le_of_sub_nonneg
        have : invPow2Rat 10 - invPow2Rat 11 = invPow2Rat 11 := by grind
        rw [this]; exact Rat.le_of_lt hp
      have h_abs0_gt : ¬ (ratAbs (1 - 63 * invPow2Rat 11) ≤ invPow2Rat 10) := by
        apply Rat.not_le.mpr
        have hpos0 : (0 : Rat) ≤ 1 - 63 * invPow2Rat 11 := by
          apply rat_le_of_mul_pos_right (c := (2048 : Rat)) (by decide)
          unfold invPow2Rat pow2Rat
          have h2048 : ((2 ^ 11 : Nat) : Rat) = (2048 : Rat) := by decide
          rw [h2048]
          have hL : (0 : Rat) * 2048 = 0 := by grind
          have hR : (1 - 63 * ((1 : Rat) / 2048)) * 2048 = 2048 - 63 * (((1 : Rat) / 2048) * 2048) := by grind
          rw [hL, hR, rat_div_mul_cancel (by decide)]
          have heq : (2048 : Rat) - 63 * 1 = ((1985 : Nat) : Rat) := by grind
          rw [heq]; exact rat_natCast_le (m := 0) (n := 1985) (by decide)
        rw [ratAbs_of_nonneg hpos0]
        apply rat_lt_of_mul_pos_right (c := (2048 : Rat)) (by decide)
        unfold invPow2Rat pow2Rat
        have h2048 : ((2 ^ 11 : Nat) : Rat) = (2048 : Rat) := by decide
        have h1024 : ((2 ^ 10 : Nat) : Rat) = (1024 : Rat) := by decide
        rw [h2048, h1024]
        have hL : ((1 : Rat) / 1024) * 2048 = (((1 : Rat) / 1024) * 1024) * 2 := by grind
        have hR : (1 - 63 * ((1 : Rat) / 2048)) * 2048 = 2048 - 63 * (((1 : Rat) / 2048) * 2048) := by grind
        rw [hL, hR, rat_div_mul_cancel (by decide), rat_div_mul_cancel (by decide)]
        have heqL : (1 : Rat) * 2 = ((2 : Nat) : Rat) := by grind
        have heqR : (2048 : Rat) - 63 * 1 = ((1985 : Nat) : Rat) := by grind
        rw [heqL, heqR]; exact rat_natCast_lt (m := 2) (n := 1985) (by decide)
      have h_diff0_lt : ratAbs (1 - 63 * invPow2Rat 11 - 1) < invPow2Rat 5 := by
        have hneg : 1 - 63 * invPow2Rat 11 - 1 = -(63 * invPow2Rat 11) := by grind
        rw [hneg]
        have hpos63 : (0 : Rat) ≤ 63 * invPow2Rat 11 := Rat.mul_nonneg (by decide) (Rat.le_of_lt hinv11_pos)
        have hnp : -(63 * invPow2Rat 11) ≤ 0 := by
          have := rat_sub_nonneg hpos63; grind
        rw [ratAbs_of_nonpos hnp]
        have hnn : - -(63 * invPow2Rat 11) = 63 * invPow2Rat 11 := by grind
        rw [hnn]
        apply rat_lt_of_mul_pos_right (c := (2048 : Rat)) (by decide)
        unfold invPow2Rat pow2Rat
        have h2048 : ((2 ^ 11 : Nat) : Rat) = (2048 : Rat) := by decide
        have h32 : ((2 ^ 5 : Nat) : Rat) = (32 : Rat) := by decide
        rw [h2048, h32]
        have hL : 63 * ((1 : Rat) / 2048) * 2048 = 63 * (((1 : Rat) / 2048) * 2048) := by grind
        have hR : ((1 : Rat) / 32) * 2048 = (((1 : Rat) / 32) * 32) * 64 := by grind
        rw [hL, hR, rat_div_mul_cancel (by decide), rat_div_mul_cancel (by decide)]
        have heqL : (63 : Rat) * 1 = ((63 : Nat) : Rat) := by grind
        have heqR : (1 : Rat) * 64 = ((64 : Nat) : Rat) := by grind
        rw [heqL, heqR]; exact rat_natCast_lt (m := 63) (n := 64) (by decide)
      have h_1_gt : ¬ (ratAbs (1 : Rat) ≤ invPow2Rat 10) := by
        apply Rat.not_le.mpr
        rw [ratAbs_of_nonneg (by decide)]
        apply rat_lt_of_mul_pos_right (c := (1024 : Rat)) (by decide)
        unfold invPow2Rat pow2Rat
        have h1024 : ((2 ^ 10 : Nat) : Rat) = (1024 : Rat) := by decide
        rw [h1024, rat_div_mul_cancel (by decide)]
        have heqR : (1 : Rat) * 1024 = ((1024 : Nat) : Rat) := by grind
        rw [heqR]; exact rat_natCast_lt (m := 1) (n := 1024) (by decide)
      have h_0_lt : ratAbs ((1 : Rat) - 1) < invPow2Rat 5 := by
        have h0 : (1 : Rat) - 1 = 0 := by grind
        rw [h0, ratAbs_of_nonneg Rat.le_refl]
        exact invPow2Rat_pos 5
      intro v
      by_cases hv : v.val = 0
      · simp only [pE4M3, qE4M3, flE4M3, hv, ite_true, h_abs0_gt, h_diff0_lt, h_1_gt, h_0_lt, ite_false]
        exact Rat.le_refl
      · simp only [pE4M3, qE4M3, flE4M3, hv, ite_false]
        have h_abs11 : ratAbs (invPow2Rat 11) ≤ invPow2Rat 10 := by
          rw [ratAbs_of_nonneg (Rat.le_of_lt hinv11_pos)]
          exact h_inv11_le_10
        have h_abs0 : ratAbs (0 : Rat) ≤ invPow2Rat 10 := by
          rw [ratAbs_of_nonneg Rat.le_refl]
          exact Rat.le_of_lt (invPow2Rat_pos 10)
        simp only [h_abs11, h_abs0, ite_true]
        exact Rat.le_refl
    have hflZ : specDecFlZ flE4M3 pE4M3 qE4M3 = 0 := specDecFlZ_zero_of_le flE4M3 pE4M3 qE4M3 hflLe
    have hp0_le_q0 : pE4M3 ⟨0, by decide⟩ ≤ qE4M3 ⟨0, by decide⟩ := by
      simp only [pE4M3, qE4M3, ite_true]
      apply rat_le_of_sub_nonneg
      have : 1 - (1 - 63 * invPow2Rat 11) = 63 * invPow2Rat 11 := by grind
      rw [this]
      exact Rat.mul_nonneg (by decide) (Rat.le_of_lt hinv11_pos)
    have htv : tvDist (specDecFallbackDist pE4M3 qE4M3 ⟨0, by decide⟩) pE4M3 = 63 / 2048 := by
      rw [tvDist_fallback_dist pE4M3 qE4M3 ⟨0, by decide⟩ hpSum hp0_le_q0, hZeq]
    refine ⟨hpSum, hqSum, hZeq, ?_, ?_, ?_, hflZ, htv⟩
    · rw [hZeq]; exact rat_div_pos (by decide) (by decide)
    · left
      simp only [ite_true]
      rw [invPow2Rat_div_two 4]
      have h16 : ((16 : Nat) : Rat) * invPow2Rat 4 = 1 := by
        unfold invPow2Rat pow2Rat
        have h : ((2 ^ 4 : Nat) : Rat) = (16 : Rat) := by decide
        rw [h]; exact rat_mul_div_cancel (by decide)
      rw [h16]
      have hneg : 1 - 63 * invPow2Rat 11 - 1 = -(63 * invPow2Rat 11) := by grind
      rw [hneg]
      have hpos63 : (0 : Rat) ≤ 63 * invPow2Rat 11 := Rat.mul_nonneg (by decide) (Rat.le_of_lt hinv11_pos)
      have hnp : -(63 * invPow2Rat 11) ≤ 0 := by have := rat_sub_nonneg hpos63; grind
      rw [ratAbs_of_nonpos hnp]
      have hnn : - -(63 * invPow2Rat 11) = 63 * invPow2Rat 11 := by grind
      rw [hnn]
      apply rat_lt_of_mul_pos_right (c := (2048 : Rat)) (by decide)
      unfold invPow2Rat pow2Rat
      have h2048 : ((2 ^ 11 : Nat) : Rat) = (2048 : Rat) := by decide
      have h32 : ((2 ^ 5 : Nat) : Rat) = (32 : Rat) := by decide
      rw [h2048, h32]
      have hL : 63 * ((1 : Rat) / 2048) * 2048 = 63 * (((1 : Rat) / 2048) * 2048) := by grind
      have hR : ((1 : Rat) / 32) * 2048 = (((1 : Rat) / 32) * 32) * 64 := by grind
      rw [hL, hR, rat_div_mul_cancel (by decide), rat_div_mul_cancel (by decide)]
      have heqL : (63 : Rat) * 1 = ((63 : Nat) : Rat) := by grind
      have heqR : (1 : Rat) * 64 = ((64 : Nat) : Rat) := by grind
      rw [heqL, heqR]; exact rat_natCast_lt (m := 63) (n := 64) (by decide)
    · intro v hv
      simp only [hv, ite_false]
      left
      rw [invPow2Rat_div_two 9]
      have hsub : invPow2Rat 11 - ((0 : Nat) : Rat) * invPow2Rat 9 = invPow2Rat 11 := by grind
      rw [hsub, ratAbs_of_nonneg (Rat.le_of_lt hinv11_pos)]
      have h := invPow2Rat_succ 10
      apply rat_lt_of_sub_pos
      have : invPow2Rat 10 - invPow2Rat 11 = invPow2Rat 11 := by grind
      rw [this]; exact hinv11_pos
  · -- Bit-exact BF16 (V = 2) NearEqual-Cancel witness
    dsimp only
    let pBF16 : Fin 2 → Rat := fun v =>
      if v.val = 0 then (1 / 2 : Rat) + invPow2Rat 10 else (1 / 2 : Rat) - invPow2Rat 10
    let qBF16 : Fin 2 → Rat := fun _ => 1 / 2
    let flBF16 : Rat → Rat := fun x =>
      if ratAbs (x - 1 / 2) ≤ invPow2Rat 10 then 1 / 2 else x
    have hinv10_pos : (0 : Rat) < invPow2Rat 10 := invPow2Rat_pos 10
    have hpSum : finSum pBF16 = 1 := by
      rw [finSum_two]
      simp only [pBF16]
      have h10 : (1 : Nat) ≠ 0 := by decide
      simp only [ite_true, h10, ite_false]
      grind
    have hqSum : finSum qBF16 = 1 := by
      rw [finSum_two]
      simp only [qBF16]
      grind
    have hZeq : specDecZ pBF16 qBF16 = 1 / 1024 := by
      unfold specDecZ specDecRes
      rw [finSum_two]
      simp only [pBF16, qBF16]
      have h10 : (1 : Nat) ≠ 0 := by decide
      simp only [ite_true, h10, ite_false]
      have h0 : (1 / 2 : Rat) + invPow2Rat 10 - 1 / 2 = invPow2Rat 10 := by grind
      have h1 : (1 / 2 : Rat) - invPow2Rat 10 - 1 / 2 = -invPow2Rat 10 := by grind
      rw [h0, h1]
      have hm0 : ratMax 0 (invPow2Rat 10) = invPow2Rat 10 := by
        unfold ratMax; simp [Rat.le_of_lt hinv10_pos]
      have hm1 : ratMax 0 (-invPow2Rat 10) = 0 := by
        unfold ratMax
        have hnot : ¬ ((0 : Rat) ≤ -invPow2Rat 10) := Rat.not_le.mpr (rat_neg_of_pos hinv10_pos)
        simp [hnot]
      rw [hm0, hm1, Rat.add_zero]
      unfold invPow2Rat pow2Rat
      have h1024 : ((2 ^ 10 : Nat) : Rat) = (1024 : Rat) := by decide
      rw [h1024]
    have hflLe : ∀ v : Fin 2, flBF16 (pBF16 v) ≤ flBF16 (qBF16 v) := by
      have hq : ratAbs ((1 / 2 : Rat) - 1 / 2) ≤ invPow2Rat 10 := by
        have : (1 / 2 : Rat) - 1 / 2 = 0 := by grind
        rw [this, ratAbs_of_nonneg Rat.le_refl]
        exact Rat.le_of_lt hinv10_pos
      intro v
      by_cases hv : v.val = 0
      · simp only [pBF16, qBF16, flBF16, hv, ite_true]
        have hp : ratAbs ((1 / 2 : Rat) + invPow2Rat 10 - 1 / 2) ≤ invPow2Rat 10 := by
          have : (1 / 2 : Rat) + invPow2Rat 10 - 1 / 2 = invPow2Rat 10 := by grind
          rw [this, ratAbs_of_nonneg (Rat.le_of_lt hinv10_pos)]
          exact Rat.le_refl
        simp only [hp, hq, ite_true]
        exact Rat.le_refl
      · simp only [pBF16, qBF16, flBF16, hv, ite_false]
        have hp : ratAbs ((1 / 2 : Rat) - invPow2Rat 10 - 1 / 2) ≤ invPow2Rat 10 := by
          have : (1 / 2 : Rat) - invPow2Rat 10 - 1 / 2 = -invPow2Rat 10 := by grind
          rw [this]
          have hnp : -invPow2Rat 10 ≤ 0 := Rat.le_of_lt (rat_neg_of_pos hinv10_pos)
          rw [ratAbs_of_nonpos hnp]
          have hnn : - -invPow2Rat 10 = invPow2Rat 10 := by grind
          rw [hnn]; exact Rat.le_refl
        simp only [hp, hq, ite_true]
        exact Rat.le_refl
    refine ⟨hpSum, hqSum, hZeq, ?_, ?_, ?_, specDecFlZ_zero_of_le flBF16 pBF16 qBF16 hflLe⟩
    · rw [hZeq]; exact rat_div_pos (by decide) (by decide)
    · left
      simp only [ite_true]
      rw [invPow2Rat_div_two 8]
      have h128 : ((128 : Nat) : Rat) * invPow2Rat 8 = 1 / 2 := by
        unfold invPow2Rat pow2Rat
        have h : ((2 ^ 8 : Nat) : Rat) = (256 : Rat) := by decide
        rw [h]
        apply Eq.symm
        apply (rat_div_eq_iff (by decide)).mpr
        have : ((128 : Nat) : Rat) * ((1 : Rat) / 256) * 2 = ((1 : Rat) / 256) * 256 := by grind
        rw [this, rat_div_mul_cancel (by decide)]
      rw [h128]
      have hsub : (1 / 2 : Rat) + invPow2Rat 10 - 1 / 2 = invPow2Rat 10 := by grind
      rw [hsub, ratAbs_of_nonneg (Rat.le_of_lt hinv10_pos)]
      have h := invPow2Rat_succ 9
      apply rat_lt_of_sub_pos
      have : invPow2Rat 9 - invPow2Rat 10 = invPow2Rat 10 := by grind
      rw [this]; exact hinv10_pos
    · right
      have h10 : (1 : Nat) ≠ 0 := by decide
      simp only [h10, ite_false]
      rw [invPow2Rat_div_two 9]
      have h256 : ((256 : Nat) : Rat) * invPow2Rat 9 = 1 / 2 := by
        unfold invPow2Rat pow2Rat
        have h : ((2 ^ 9 : Nat) : Rat) = (512 : Rat) := by decide
        rw [h]
        apply Eq.symm
        apply (rat_div_eq_iff (by decide)).mpr
        have : ((256 : Nat) : Rat) * ((1 : Rat) / 512) * 2 = ((1 : Rat) / 512) * 512 := by grind
        rw [this, rat_div_mul_cancel (by decide)]
      rw [h256]
      have hsub : (1 / 2 : Rat) - invPow2Rat 10 - 1 / 2 = -invPow2Rat 10 := by grind
      rw [hsub]
      have hnp : -invPow2Rat 10 ≤ 0 := Rat.le_of_lt (rat_neg_of_pos hinv10_pos)
      rw [ratAbs_of_nonpos hnp]
      refine ⟨by grind, by decide⟩

/-! ### Headline Theorem 3: Exact `Q_B` / `Q32` Integer Fixed-Point Speculative Decoding -/

theorem specDecInt_conservation {n : Nat} (P Q : Fin n → Int) (D : Int)
    (hP : finSumInt P = D) :
    specDecIntAccept P Q + specDecIntZ P Q = D := by
  unfold specDecIntAccept specDecIntZ specDecIntRes
  rw [← finSumInt_add]
  have hc : finSumInt (fun v : Fin n => intMin (P v) (Q v) + intMax 0 (P v - Q v)) = finSumInt P := by
    apply finSumInt_congr
    intro v
    exact intMin_add_intMax_sub (P v) (Q v)
  rw [hc, hP]

theorem specDecIntZ_pos_of_ne {n : Nat} (P Q : Fin n → Int) (D : Int)
    (hP : finSumInt P = D) (hQ : finSumInt Q = D)
    (hne : ∃ v : Fin n, P v ≠ Q v) :
    0 < specDecIntZ P Q := by
  have hnonneg : ∀ v : Fin n, 0 ≤ specDecIntRes P Q v := by
    intro v; unfold specDecIntRes intMax; split <;> omega
  have hZnonneg : 0 ≤ specDecIntZ P Q := finSumInt_nonneg hnonneg
  by_cases hZ0 : specDecIntZ P Q = 0
  · have hall0 : ∀ v : Fin n, specDecIntRes P Q v = 0 :=
      (finSumInt_eq_zero_iff_all_zero hnonneg).mp hZ0
    have hle : ∀ v : Fin n, P v ≤ Q v := by
      intro v
      have hv := hall0 v
      unfold specDecIntRes intMax at hv
      split at hv <;> omega
    have hdiff_nonneg : ∀ v : Fin n, 0 ≤ Q v - P v := fun v => Int.sub_nonneg.mpr (hle v)
    have hdiff_sum : finSumInt (fun v : Fin n => Q v - P v) = 0 := by
      rw [finSumInt_sub, hQ, hP]; omega
    have hdiff_all0 : ∀ v : Fin n, Q v - P v = 0 :=
      (finSumInt_eq_zero_iff_all_zero hdiff_nonneg).mp hdiff_sum
    rcases hne with ⟨v, hvne⟩
    have hv0 := hdiff_all0 v
    omega
  · omega

theorem qAcceptTest_iff_rat {B : Nat} {u Pv Qv : Int} (hQ : 0 < Qv) :
    qAcceptTest B u Pv Qv ↔ (u : Rat) / pow2Rat B < (Pv : Rat) / (Qv : Rat) := by
  unfold qAcceptTest qDenom
  have hDpos : (0 : Rat) < pow2Rat B := pow2Rat_pos B
  have hQpos : (0 : Rat) < (Qv : Rat) := rat_intCast_pos hQ
  have hDQpos : (0 : Rat) < pow2Rat B * (Qv : Rat) := rat_mul_pos hDpos hQpos
  have hDne : pow2Rat B ≠ 0 := Rat.ne_of_gt hDpos
  have hQne : (Qv : Rat) ≠ 0 := Rat.ne_of_gt hQpos
  have hcast : (((2 ^ B : Nat) : Int) : Rat) = pow2Rat B := by
    unfold pow2Rat
    rfl
  constructor
  · intro hlt
    have hrat : ((u * Qv : Int) : Rat) < ((Pv * ((2 ^ B : Nat) : Int) : Int) : Rat) :=
      rat_intCast_lt hlt
    rw [Rat.intCast_mul, Rat.intCast_mul, hcast] at hrat
    apply rat_lt_of_mul_pos_right hDQpos
    have hL : ((u : Rat) / pow2Rat B) * (pow2Rat B * (Qv : Rat)) = (u : Rat) * (Qv : Rat) := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel hDne]
    have hR : ((Pv : Rat) / (Qv : Rat)) * (pow2Rat B * (Qv : Rat)) = (Pv : Rat) * pow2Rat B := by
      rw [Rat.mul_comm (pow2Rat B) (Qv : Rat), ← Rat.mul_assoc, rat_div_mul_cancel hQne]
    rw [hL, hR]
    exact hrat
  · intro hrat
    have hmul := rat_mul_lt_mul_of_pos_right hrat hDQpos
    have hL : ((u : Rat) / pow2Rat B) * (pow2Rat B * (Qv : Rat)) = (u : Rat) * (Qv : Rat) := by
      rw [← Rat.mul_assoc, rat_div_mul_cancel hDne]
    have hR : ((Pv : Rat) / (Qv : Rat)) * (pow2Rat B * (Qv : Rat)) = (Pv : Rat) * pow2Rat B := by
      rw [Rat.mul_comm (pow2Rat B) (Qv : Rat), ← Rat.mul_assoc, rat_div_mul_cancel hQne]
    rw [hL, hR] at hmul
    rw [← hcast, ← Rat.intCast_mul, ← Rat.intCast_mul] at hmul
    by_cases h : u * Qv < Pv * ((2 ^ B : Nat) : Int)
    · exact h
    · have hge : Pv * ((2 ^ B : Nat) : Int) ≤ u * Qv := by omega
      exact False.elim (Rat.not_le.mpr hmul (rat_intCast_le hge))

theorem qToRat_finSum {B n : Nat} (P : Fin n → Int) (hP : finSumInt P = qDenom B) :
    finSum (qToRat B P) = 1 := by
  unfold qToRat
  have hDne : pow2Rat B ≠ 0 := pow2Rat_ne_zero B
  have hmul : finSum (fun v : Fin n => (P v : Rat) / pow2Rat B) =
      finSum (fun v : Fin n => (P v : Rat)) * (pow2Rat B)⁻¹ := by
    rw [← finSum_mul_right]
    apply finSum_congr
    intro v
    rw [Rat.div_def]
  rw [hmul, finSum_intCast, hP]
  have hcast : (qDenom B : Rat) = pow2Rat B := by
    unfold qDenom pow2Rat; rfl
  rw [hcast, Rat.mul_inv_cancel _ hDne]

theorem qToRat_specDecZ {B n : Nat} (P Q : Fin n → Int) :
    specDecZ (qToRat B P) (qToRat B Q) = (specDecIntZ P Q : Rat) / pow2Rat B := by
  unfold specDecZ specDecRes specDecIntZ specDecIntRes qToRat
  have hDpos : (0 : Rat) < pow2Rat B := pow2Rat_pos B
  have hinv_pos : (0 : Rat) < (pow2Rat B)⁻¹ := rat_inv_pos hDpos
  have hcongr : finSum (fun v : Fin n => ratMax 0 ((P v : Rat) / pow2Rat B - (Q v : Rat) / pow2Rat B)) =
      finSum (fun v : Fin n => ((intMax 0 (P v - Q v) : Int) : Rat) * (pow2Rat B)⁻¹) := by
    apply finSum_congr
    intro v
    have hsub : (P v : Rat) / pow2Rat B - (Q v : Rat) / pow2Rat B =
        ((P v - Q v : Int) : Rat) * (pow2Rat B)⁻¹ := by
      rw [Rat.div_def, Rat.div_def, Rat.intCast_sub]
      grind
    rw [hsub]
    unfold ratMax intMax
    by_cases hle : 0 ≤ P v - Q v
    · have hrat : (0 : Rat) ≤ ((P v - Q v : Int) : Rat) * (pow2Rat B)⁻¹ :=
        Rat.mul_nonneg (rat_intCast_nonneg hle) (Rat.le_of_lt hinv_pos)
      simp only [hrat, hle, ite_true]
    · have hlt : P v - Q v < 0 := by omega
      have hrat_lt : ((P v - Q v : Int) : Rat) * (pow2Rat B)⁻¹ < 0 := by
        have h1 : ((P v - Q v : Int) : Rat) < 0 := rat_intCast_lt hlt
        have h2 := rat_mul_lt_mul_of_pos_right h1 hinv_pos
        rw [Rat.zero_mul] at h2
        exact h2
      have hnot : ¬ ((0 : Rat) ≤ ((P v - Q v : Int) : Rat) * (pow2Rat B)⁻¹) :=
        Rat.not_le.mpr hrat_lt
      simp only [hnot, hle, ite_false]
      grind
  rw [hcongr, finSum_mul_right, finSum_intCast, Rat.div_def]

/-- Headline Theorem 3 (`specdec_q32_integer_exact_zero_leak`). -/
theorem specdec_q32_integer_exact_zero_leak :
    (qDenom 32 = 4294967296) ∧
    (∀ (B n : Nat) (P Q : Fin n → Int),
      finSumInt P = qDenom B → finSumInt Q = qDenom B →
      specDecIntAccept P Q + specDecIntZ P Q = qDenom B ∧
      ((∃ v : Fin n, P v ≠ Q v) → 0 < specDecIntZ P Q) ∧
      finSum (qToRat B P) = 1 ∧
      (∀ v : Fin n, specDecOut (qToRat B P) (qToRat B Q) v = qToRat B P v) ∧
      tvDist (specDecOut (qToRat B P) (qToRat B Q)) (qToRat B P) = 0) ∧
    (∀ (B : Nat) (u Pv Qv : Int), 0 < Qv →
      (qAcceptTest B u Pv Qv ↔ (u : Rat) / pow2Rat B < (Pv : Rat) / (Qv : Rat)) ∧
      (Qv ≤ Pv → u < qDenom B → qAcceptTest B u Pv Qv) ∧
      (Pv < Qv → ¬ qAcceptTest B (qDenom B) Pv Qv)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro B n P Q hP hQ
    have hcons := specDecInt_conservation P Q (qDenom B) hP
    have hpSum := qToRat_finSum P hP
    have hpos_of_ne : (∃ v : Fin n, P v ≠ Q v) → 0 < specDecIntZ P Q :=
      specDecIntZ_pos_of_ne P Q (qDenom B) hP hQ
    have hout : ∀ v : Fin n, specDecOut (qToRat B P) (qToRat B Q) v = qToRat B P v := by
      by_cases hne : ∃ v : Fin n, P v ≠ Q v
      · have hZint : 0 < specDecIntZ P Q := hpos_of_ne hne
        have hZrat : (0 : Rat) < specDecZ (qToRat B P) (qToRat B Q) := by
          rw [qToRat_specDecZ]
          exact rat_div_pos (rat_intCast_pos hZint) (pow2Rat_pos B)
        exact specDecOut_exact_of_pos (qToRat B P) (qToRat B Q) hpSum hZrat
      · have heq : ∀ v : Fin n, P v = Q v := by
          intro v
          by_cases hv : P v = Q v
          · exact hv
          · exact False.elim (hne ⟨v, hv⟩)
        have hZ0 : specDecZ (qToRat B P) (qToRat B Q) = 0 := by
          rw [qToRat_specDecZ]
          have hZint0 : specDecIntZ P Q = 0 := by
            unfold specDecIntZ specDecIntRes
            have hc : finSumInt (fun v : Fin n => intMax 0 (P v - Q v)) =
                finSumInt (fun _ : Fin n => (0 : Int)) := by
              apply finSumInt_congr
              intro v
              rw [heq v]
              simp [intMax]
            rw [hc, finSumInt_zero]
          rw [hZint0]
          simp [Rat.div_def]
        intro v
        unfold specDecOut
        simp only [hZ0, ite_true]
        have hqv : qToRat B Q v = qToRat B P v := by
          unfold qToRat; rw [heq v]
        rw [hqv]
        unfold ratMin
        simp
    refine ⟨hcons, hpos_of_ne, hpSum, hout, ?_⟩
    have hfun : specDecOut (qToRat B P) (qToRat B Q) = qToRat B P := funext hout
    rw [hfun]
    exact tvDist_self _
  · intro B u Pv Qv hQ
    refine ⟨qAcceptTest_iff_rat hQ, ?_, ?_⟩
    · intro hle hu
      unfold qAcceptTest
      have h1 : u * Qv < qDenom B * Qv := Int.mul_lt_mul_of_pos_right hu hQ
      have hDpos : 0 < qDenom B := by
        unfold qDenom
        have hpow : 0 < 2 ^ B := Nat.pow_pos (by decide)
        omega
      have h2 : qDenom B * Qv ≤ qDenom B * Pv := Int.mul_le_mul_of_nonneg_left hle (Int.le_of_lt hDpos)
      rw [Int.mul_comm (qDenom B) Pv] at h2
      omega
    · intro hlt hacc
      unfold qAcceptTest at hacc
      have hDpos : 0 < qDenom B := by
        unfold qDenom
        have hpow : 0 < 2 ^ B := Nat.pow_pos (by decide)
        omega
      have h1 : Pv * qDenom B < Qv * qDenom B := Int.mul_lt_mul_of_pos_right hlt hDpos
      rw [Int.mul_comm Qv (qDenom B)] at h1
      omega

end SamplingHorizons
