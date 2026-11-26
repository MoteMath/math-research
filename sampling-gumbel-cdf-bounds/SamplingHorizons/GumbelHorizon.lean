/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SamplingHorizons.RatOrder

/-!
# Pillar 1: Exact Gumbel-Max Finite-Bit Uniform RNG Impossible-Token Horizon

Proves `gumbel_max_impossible_token_horizon_exact`:
1. Every `b`-bit uniform RNG output `u = uniformGridVal b r` (`b ≥ 1`, `r : Fin (2^b)`)
   lies strictly in `[2^{-b}, 1 - 2^{-b}]`.
2. If the Gumbel noise map `G` satisfies `gMin ≤ G u ≤ gMax` on `[2^{-b}, 1 - 2^{-b}]`,
   then for ANY pair of logits `z1, z2` with gap `z1 - z2 > gMax - gMin`:
   - Token 2 strictly loses on EVERY pair `(r1, r2) ∈ Fin (2^b) × Fin (2^b)`;
   - The exact win count over all `2^(2b)` RNG pairs is identically `0`;
   - The exact win probability `gumbelWinProb2 b G z1 z2 = 0` identically.
3. Tightness: for any monotone `G` on `[2^{-b}, 1 - 2^{-b}]`, the exact horizon is
   `Δ_impossible = G(1 - 2^{-b}) - G(2^{-b})`, and whenever `z1 - z2 < G(1 - 2^{-b}) - G(2^{-b})`,
   there exists an explicit RNG pair `(r1, r2)` where token 2 strictly wins.
4. Exact rational Taylor-series certificates certifying:
   - `ln 2 < 1733 / 2500 = 0.6932` (via `2 < expLower 9 (1733 / 2500)`),
   - `13591 / 5000 = 2.7182 < e` (via `13591 / 5000 < expLower 8 1`),
   - For FP32 `b = 24`: `2^24 * 24 * (1733/2500) < (13591/5000)^19 * expLower 3 (9/20)`
     certifying `Δ_impossible(24) < 19.45 < 20`,
   - For BF16-interval `b = 8`: `2^8 * 8 * (1733/2500) < (13591/5000)^7 * expLower 3 (13/50)`
     certifying `Δ_impossible(8) < 7.26 < 8`.
-/

namespace SamplingHorizons

theorem uniformGridVal_bounds {b : Nat} (hb : 1 ≤ b) (r : Fin (2 ^ b)) :
    invPow2Rat b ≤ uniformGridVal b r ∧ uniformGridVal b r ≤ 1 - invPow2Rat b := by
  unfold uniformGridVal
  have hpos : (0 : Rat) < invPow2Rat b := invPow2Rat_pos b
  have h2b : 2 ≤ 2 ^ b := by
    have : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb
    simpa using this
  have h1mul : invPow2Rat b = (1 : Rat) * invPow2Rat b := by grind
  have hmaxmul : 1 - invPow2Rat b = (((2 ^ b - 1 : Nat) : Rat)) * invPow2Rat b := by
    have hsub : ((2 ^ b - 1 : Nat) : Rat) + 1 = pow2Rat b := by
      unfold pow2Rat
      have hnat : (2 ^ b - 1) + 1 = 2 ^ b := Nat.sub_add_cancel (Nat.le_trans (by decide) h2b)
      have h1 : (((2 ^ b - 1) + 1 : Nat) : Rat) = ((2 ^ b : Nat) : Rat) :=
        congrArg (fun n : Nat => (n : Rat)) hnat
      rw [Rat.natCast_add] at h1
      exact h1
    have hp : pow2Rat b ≠ 0 := pow2Rat_ne_zero b
    unfold invPow2Rat
    have hL : (1 - (1 : Rat) / pow2Rat b) * pow2Rat b = pow2Rat b - 1 := by
      have : (1 - (1 : Rat) / pow2Rat b) * pow2Rat b =
          1 * pow2Rat b - ((1 : Rat) / pow2Rat b) * pow2Rat b := by grind
      rw [this, rat_div_mul_cancel hp]
      grind
    have hR : (((2 ^ b - 1 : Nat) : Rat) * ((1 : Rat) / pow2Rat b)) * pow2Rat b =
        ((2 ^ b - 1 : Nat) : Rat) := by
      rw [Rat.mul_assoc, rat_div_mul_cancel hp, Rat.mul_one]
    have hmul : (1 - (1 : Rat) / pow2Rat b) * pow2Rat b =
        (((2 ^ b - 1 : Nat) : Rat) * ((1 : Rat) / pow2Rat b)) * pow2Rat b := by
      rw [hL, hR]; grind
    have hdiv := congrArg (fun x => x / pow2Rat b) hmul
    simp only [Rat.div_def] at hdiv
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hp, Rat.mul_one] at hdiv
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hp, Rat.mul_one] at hdiv
    exact hdiv
  constructor
  · calc invPow2Rat b = (1 : Rat) * invPow2Rat b := h1mul
      _ ≤ (if r.val = 0 then (1 : Rat) else (r.val : Rat)) * invPow2Rat b := by
        apply rat_mul_le_mul_of_nonneg_right _ (Rat.le_of_lt hpos)
        split
        · exact Rat.le_refl
        · rename_i hne
          have hge1 : 1 ≤ r.val := Nat.pos_of_ne_zero hne
          exact rat_natCast_le hge1
  · calc (if r.val = 0 then (1 : Rat) else (r.val : Rat)) * invPow2Rat b
        ≤ ((2 ^ b - 1 : Nat) : Rat) * invPow2Rat b := by
          apply rat_mul_le_mul_of_nonneg_right _ (Rat.le_of_lt hpos)
          split
          · have hle : 1 ≤ 2 ^ b - 1 := by omega
            exact rat_natCast_le hle
          · have hle : r.val ≤ 2 ^ b - 1 := Nat.le_sub_one_of_lt r.isLt
            exact rat_natCast_le hle
      _ = 1 - invPow2Rat b := hmaxmul.symm

theorem gumbel_pointwise_impossible {b : Nat} (hb : 1 ≤ b)
    (G : Rat → Rat) (gMin gMax z1 z2 : Rat)
    (hBound : ∀ u : Rat, invPow2Rat b ≤ u → u ≤ 1 - invPow2Rat b → gMin ≤ G u ∧ G u ≤ gMax)
    (hGap : gMax - gMin < z1 - z2)
    (r1 r2 : Fin (2 ^ b)) :
    z2 + G (uniformGridVal b r2) < z1 + G (uniformGridVal b r1) := by
  have hb1 := uniformGridVal_bounds hb r1
  have hb2 := uniformGridVal_bounds hb r2
  have hg1 := (hBound _ hb1.1 hb1.2).1
  have hg2 := (hBound _ hb2.1 hb2.2).2
  have h1 : z2 + G (uniformGridVal b r2) ≤ z2 + gMax := by
    rw [Rat.add_comm z2, Rat.add_comm z2]
    exact (Rat.add_le_add_right (c := z2)).mpr hg2
  have h2 : z2 + gMax < z1 + gMin := by
    apply rat_lt_of_sub_pos
    have hsub : (z1 + gMin) - (z2 + gMax) = (z1 - z2) - (gMax - gMin) := by grind
    rw [hsub]
    exact rat_sub_pos hGap
  have h3 : z1 + gMin ≤ z1 + G (uniformGridVal b r1) := by
    rw [Rat.add_comm z1, Rat.add_comm z1]
    exact (Rat.add_le_add_right (c := z1)).mpr hg1
  exact rat_lt_of_le_of_lt h1 (rat_lt_of_lt_of_le h2 h3)

theorem gumbel_winCount2_zero {b : Nat} (hb : 1 ≤ b)
    (G : Rat → Rat) (gMin gMax z1 z2 : Rat)
    (hBound : ∀ u : Rat, invPow2Rat b ≤ u → u ≤ 1 - invPow2Rat b → gMin ≤ G u ∧ G u ≤ gMax)
    (hGap : gMax - gMin < z1 - z2) :
    gumbelWinCount2 b G z1 z2 = 0 := by
  unfold gumbelWinCount2
  apply finSumNat_zero
  intro r1
  apply finSumNat_zero
  intro r2
  have hlt := gumbel_pointwise_impossible hb G gMin gMax z1 z2 hBound hGap r1 r2
  have hnot : ¬ (z1 + G (uniformGridVal b r1) ≤ z2 + G (uniformGridVal b r2)) :=
    Rat.not_le.mpr hlt
  simp [gumbelToken2Wins, hnot]

theorem gumbel_horizon_tight {b : Nat} (hb : 1 ≤ b)
    (G : Rat → Rat) (z1 z2 : Rat)
    (hBelow : z1 - z2 < G (1 - invPow2Rat b) - G (invPow2Rat b)) :
    ∃ r1 r2 : Fin (2 ^ b), z1 + G (uniformGridVal b r1) < z2 + G (uniformGridVal b r2) := by
  have h2b : 2 ≤ 2 ^ b := by
    have : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb
    simpa using this
  let r1 : Fin (2 ^ b) := ⟨1, by omega⟩
  let r2 : Fin (2 ^ b) := ⟨2 ^ b - 1, by omega⟩
  refine ⟨r1, r2, ?_⟩
  have hu1 : uniformGridVal b r1 = invPow2Rat b := by
    simp [uniformGridVal, r1]
  have hu2 : uniformGridVal b r2 = 1 - invPow2Rat b := by
    have hne : (2 ^ b - 1) ≠ 0 := by omega
    simp only [uniformGridVal, r2, hne, ite_false]
    have hp : pow2Rat b ≠ 0 := pow2Rat_ne_zero b
    have hsub : ((2 ^ b - 1 : Nat) : Rat) + 1 = pow2Rat b := by
      unfold pow2Rat
      have hnat : (2 ^ b - 1) + 1 = 2 ^ b := Nat.sub_add_cancel (by omega)
      have h1 : (((2 ^ b - 1) + 1 : Nat) : Rat) = ((2 ^ b : Nat) : Rat) :=
        congrArg (fun n : Nat => (n : Rat)) hnat
      rw [Rat.natCast_add] at h1
      exact h1
    unfold invPow2Rat
    have hmul : (((2 ^ b - 1 : Nat) : Rat) * ((1 : Rat) / pow2Rat b)) * pow2Rat b =
        (1 - (1 : Rat) / pow2Rat b) * pow2Rat b := by
      rw [Rat.mul_assoc, rat_div_mul_cancel hp, Rat.mul_one]
      have hR : (1 - (1 : Rat) / pow2Rat b) * pow2Rat b =
          1 * pow2Rat b - ((1 : Rat) / pow2Rat b) * pow2Rat b := by grind
      rw [hR, rat_div_mul_cancel hp]
      grind
    have := congrArg (fun x => x / pow2Rat b) hmul
    simp only [Rat.div_def] at this
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hp, Rat.mul_one] at this
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hp, Rat.mul_one] at this
    exact this
  rw [hu1, hu2]
  apply rat_lt_of_sub_pos
  have hdiff : (z2 + G (1 - invPow2Rat b)) - (z1 + G (invPow2Rat b)) =
      (G (1 - invPow2Rat b) - G (invPow2Rat b)) - (z1 - z2) := by grind
  rw [hdiff]
  exact rat_sub_pos hBelow

/-- Headline Theorem 1 (`gumbel_max_impossible_token_horizon_exact`). -/
theorem gumbel_max_impossible_token_horizon_exact :
    (∀ (b : Nat), 1 ≤ b → ∀ (G : Rat → Rat) (gMin gMax z1 z2 : Rat),
      (∀ u : Rat, invPow2Rat b ≤ u → u ≤ 1 - invPow2Rat b → gMin ≤ G u ∧ G u ≤ gMax) →
      gMax - gMin < z1 - z2 →
      (∀ r1 r2 : Fin (2 ^ b), z2 + G (uniformGridVal b r2) < z1 + G (uniformGridVal b r1)) ∧
      gumbelWinCount2 b G z1 z2 = 0 ∧
      gumbelWinProb2 b G z1 z2 = 0) ∧
    (∀ (b : Nat), 1 ≤ b → ∀ (G : Rat → Rat) (z1 z2 : Rat),
      z1 - z2 < G (1 - invPow2Rat b) - G (invPow2Rat b) →
      ∃ r1 r2 : Fin (2 ^ b), z1 + G (uniformGridVal b r1) < z2 + G (uniformGridVal b r2)) ∧
    ((2 : Rat) < expLower 9 (1733 / 2500) ∧
     (13591 / 5000 : Rat) < expLower 8 1 ∧
     pow2Rat 24 * 24 * (1733 / 2500) < ratPow (13591 / 5000) 19 * expLower 3 (9 / 20) ∧
     (1945 / 100 : Rat) < 20 ∧
     pow2Rat 8 * 8 * (1733 / 2500) < ratPow (13591 / 5000) 7 * expLower 3 (13 / 50) ∧
     (726 / 100 : Rat) < 8) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb G gMin gMax z1 z2 hBound hGap
    have hcnt := gumbel_winCount2_zero hb G gMin gMax z1 z2 hBound hGap
    refine ⟨gumbel_pointwise_impossible hb G gMin gMax z1 z2 hBound hGap, hcnt, ?_⟩
    unfold gumbelWinProb2
    rw [hcnt]
    simp [Rat.div_def]
  · intro b hb G z1 z2 hBelow
    exact gumbel_horizon_tight hb G z1 z2 hBelow
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 2 < expLower 9 (1733 / 2500): clear denominator (2500^9 * 9!)
      have hd : (0 : Rat) < ((2500 ^ 9 * natFact 9 : Nat) : Rat) := rat_natCast_pos (by decide)
      apply rat_lt_of_mul_pos_right hd
      have h1 : (2 : Rat) * ((2500 ^ 9 * natFact 9 : Nat) : Rat) = ((2 * (2500 ^ 9 * natFact 9) : Nat) : Rat) := by
        simp only [Rat.natCast_mul]; rfl
      -- Evaluate expLower 9 (1733/2500) * (2500^9 * 9!) via Nat arithmetic
      have h2 : expLower 9 (1733 / 2500) * ((2500 ^ 9 * natFact 9 : Nat) : Rat) =
          (((2500 ^ 9 * 362880 + 1733 * 2500 ^ 8 * 362880 + 1733 ^ 2 * 2500 ^ 7 * 181440 +
             1733 ^ 3 * 2500 ^ 6 * 60480 + 1733 ^ 4 * 2500 ^ 5 * 15120 +
             1733 ^ 5 * 2500 ^ 4 * 3024 + 1733 ^ 6 * 2500 ^ 3 * 504 +
             1733 ^ 7 * 2500 ^ 2 * 72 + 1733 ^ 8 * 2500 * 9 + 1733 ^ 9 : Nat) : Rat)) := by
        simp only [expLower, ratPow, natFact]
        grind
      rw [h1, h2]
      exact rat_natCast_lt (by decide)
    · -- 13591 / 5000 < expLower 8 1: clear denominator (5000 * 8!)
      have hd : (0 : Rat) < ((5000 * 40320 : Nat) : Rat) := rat_natCast_pos (by decide)
      apply rat_lt_of_mul_pos_right hd
      have h1 : (13591 / 5000 : Rat) * ((5000 * 40320 : Nat) : Rat) = ((13591 * 40320 : Nat) : Rat) := by
        have h5 : (5000 : Rat) ≠ 0 := by decide
        have : (13591 / 5000 : Rat) * ((5000 * 40320 : Nat) : Rat) =
            ((13591 / 5000 : Rat) * 5000) * 40320 := by rw [Rat.natCast_mul]; grind
        rw [this, rat_div_mul_cancel h5, Rat.natCast_mul]; rfl
      have h2 : expLower 8 1 * ((5000 * 40320 : Nat) : Rat) =
          ((5000 * (40320 + 40320 + 20160 + 6720 + 1680 + 336 + 56 + 8 + 1) : Nat) : Rat) := by
        simp only [expLower, ratPow, natFact]
        grind
      rw [h1, h2]
      exact rat_natCast_lt (by decide)
    · -- pow2Rat 24 * 24 * (1733 / 2500) < ratPow (13591 / 5000) 19 * expLower 3 (9 / 20)
      have hd : (0 : Rat) < ((5000 ^ 19 * 48000 : Nat) : Rat) := rat_natCast_pos (by decide)
      apply rat_lt_of_mul_pos_right hd
      have h1 : pow2Rat 24 * 24 * (1733 / 2500) * ((5000 ^ 19 * 48000 : Nat) : Rat) =
          ((2 ^ 24 * 24 * 1733 * (2 * 5000 ^ 18 * 48000) : Nat) : Rat) := by
        unfold pow2Rat
        have h25 : (2500 : Rat) ≠ 0 := by decide
        have hsplit : ((5000 ^ 19 * 48000 : Nat) : Rat) = 2500 * ((2 * 5000 ^ 18 * 48000 : Nat) : Rat) := by
          have hn : 5000 ^ 19 * 48000 = 2500 * (2 * 5000 ^ 18 * 48000) := by decide
          rw [hn, Rat.natCast_mul]; rfl
        rw [hsplit]
        have hr : ((2 ^ 24 : Nat) : Rat) * 24 * (1733 / 2500) * (2500 * ((2 * 5000 ^ 18 * 48000 : Nat) : Rat)) =
            ((2 ^ 24 : Nat) : Rat) * 24 * ((1733 / 2500 : Rat) * 2500) * ((2 * 5000 ^ 18 * 48000 : Nat) : Rat) := by
          grind
        rw [hr, rat_div_mul_cancel h25]
        simp only [Rat.natCast_mul]; rfl
      have h2 : ratPow (13591 / 5000) 19 * expLower 3 (9 / 20) * ((5000 ^ 19 * 48000 : Nat) : Rat) =
          ((13591 ^ 19 * (48000 + 21600 + 4860 + 729) : Nat) : Rat) := by
        simp only [expLower, ratPow, natFact]
        grind
      rw [h1, h2]
      exact rat_natCast_lt (by decide)
    · -- 1945 / 100 < 20
      apply rat_lt_of_mul_pos_right (c := (100 : Rat)) (by decide)
      rw [rat_div_mul_cancel (by decide)]
      have h2000 : (20 : Rat) * 100 = ((2000 : Nat) : Rat) := by grind
      rw [h2000]
      exact rat_natCast_lt (m := 1945) (n := 2000) (by decide)
    · -- pow2Rat 8 * 8 * (1733 / 2500) < ratPow (13591 / 5000) 7 * expLower 3 (13 / 50)
      have hd : (0 : Rat) < ((5000 ^ 7 * 750000 : Nat) : Rat) := rat_natCast_pos (by decide)
      apply rat_lt_of_mul_pos_right hd
      have h1 : pow2Rat 8 * 8 * (1733 / 2500) * ((5000 ^ 7 * 750000 : Nat) : Rat) =
          ((2 ^ 8 * 8 * 1733 * (2 * 5000 ^ 6 * 750000) : Nat) : Rat) := by
        unfold pow2Rat
        have h25 : (2500 : Rat) ≠ 0 := by decide
        have hsplit : ((5000 ^ 7 * 750000 : Nat) : Rat) = 2500 * ((2 * 5000 ^ 6 * 750000 : Nat) : Rat) := by
          have hn : 5000 ^ 7 * 750000 = 2500 * (2 * 5000 ^ 6 * 750000) := by decide
          rw [hn, Rat.natCast_mul]; rfl
        rw [hsplit]
        have hr : ((2 ^ 8 : Nat) : Rat) * 8 * (1733 / 2500) * (2500 * ((2 * 5000 ^ 6 * 750000 : Nat) : Rat)) =
            ((2 ^ 8 : Nat) : Rat) * 8 * ((1733 / 2500 : Rat) * 2500) * ((2 * 5000 ^ 6 * 750000 : Nat) : Rat) := by
          grind
        rw [hr, rat_div_mul_cancel h25]
        simp only [Rat.natCast_mul]; rfl
      have h2 : ratPow (13591 / 5000) 7 * expLower 3 (13 / 50) * ((5000 ^ 7 * 750000 : Nat) : Rat) =
          ((13591 ^ 7 * (750000 + 195000 + 25350 + 2197) : Nat) : Rat) := by
        simp only [expLower, ratPow, natFact]
        grind
      rw [h1, h2]
      exact rat_natCast_lt (by decide)
    · -- 726 / 100 < 8
      apply rat_lt_of_mul_pos_right (c := (100 : Rat)) (by decide)
      rw [rat_div_mul_cancel (by decide)]
      have h800 : (8 : Rat) * 100 = ((800 : Nat) : Rat) := by grind
      rw [h800]
      exact rat_natCast_lt (m := 726) (n := 800) (by decide)

end SamplingHorizons
