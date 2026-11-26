/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mrope3dCoprime.RatOrder

/-!
# Theorems 3 & 4: Contiguous `mRoPE` `BF16` Width Freeze & Interleaved Resolution Gap

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
3. `contiguous_mrope_bf16_width_freeze_exact`: for base `b = 10^6`, every contiguous Width
   pair `k ∈ [40, 63]` satisfies `θ_k < 2^{-12}`, and for every patch offset `ΔW ∈ [1, 63]`,
   `1 - (1/2)(ΔW · θ_k)^2 > 1 - 2^{-13} > 1 - 2^{-9}`, proving 100% `BF16` cosine freeze
   (`bf16SnapsToOne c`) across all 24 Width pairs and all 63 patch offsets.
4. `interleaved_vs_contiguous_mrope_resolution_gap`: exact closed-form geometric series
   separation between contiguous Width (`pairs 40..63`) and interleaved Width (both stride-3
   round-robin `2, 5, ..., 71` and Qwen3-VL 64-pair interleaved), proving the exact
   `b^{76/64}` power law and `> 10^6×` local spatial resolution gain for `b = 10^6`.
-/

namespace Mrope3dCoprime

/-! ### Part 1: Contiguous `mRoPE` `BF16` Width Freeze (Theorem 3) -/

theorem pow2_48_lt_pow10_15 : (2 ^ 48 : Nat) < 10 ^ 15 := by decide

theorem pow2_12_pow64_lt_base1M_pow40 :
    ratPow (pow2Rat 12) 64 < ratPow (1000000 : Rat) 40 := by
  have h1 : ratPow (pow2Rat 12) 4 < ratPow ((10 : Nat) : Rat) 15 := by
    unfold pow2Rat
    rw [ratPow_natCast, ratPow_natCast]
    have h48 : (2 ^ 12) ^ 4 = 2 ^ 48 := by decide
    rw [h48]
    exact rat_natCast_lt pow2_48_lt_pow10_15
  have h16 : ratPow (ratPow (pow2Rat 12) 4) 16 < ratPow (ratPow ((10 : Nat) : Rat) 15) 16 :=
    ratPow_lt_ratPow (ratPow_nonneg (Rat.le_of_lt (pow2Rat_pos 12)) 4) h1 (by decide)
  rw [← ratPow_mul, ← ratPow_mul] at h16
  have heq : ratPow ((10 : Nat) : Rat) (15 * 16) = ratPow (1000000 : Rat) 40 := by
    have h1M : (1000000 : Rat) = ratPow ((10 : Nat) : Rat) 6 := by
      rw [ratPow_natCast]; decide
    rw [h1M, ← ratPow_mul]
  rw [heq] at h16
  exact h16

/-- For base `b = 10^6` and any Width pair `k ≥ 40`, `θ^{64} * (10^6)^k ≤ 1` forces `θ < 2^{-12}`. -/
theorem width_pair_freq_lt_invPow2_12 {k : Nat} (hk : 40 ≤ k) {θ : Rat} (hθ0 : (0 : Rat) ≤ θ)
    (hθ : ratPow θ 64 * ratPow (1000000 : Rat) k ≤ 1) :
    θ < invPow2Rat 12 := by
  have hbase_le : ratPow (1000000 : Rat) 40 ≤ ratPow (1000000 : Rat) k := by
    have hkd : k = 40 + (k - 40) := by omega
    rw [hkd, ratPow_add]
    have hge1 : (1 : Rat) ≤ ratPow (1000000 : Rat) (k - 40) := by
      have h1 : ratPow (1 : Rat) (k - 40) ≤ ratPow (1000000 : Rat) (k - 40) :=
        ratPow_le_ratPow (by decide) (by decide) (k - 40)
      rw [ratPow_one] at h1
      exact h1
    have hmul := rat_mul_le_mul_of_nonneg_left hge1 (ratPow_nonneg (by decide : (0 : Rat) ≤ 1000000) 40)
    rw [Rat.mul_one] at hmul
    exact hmul
  have hθ40 : ratPow θ 64 * ratPow (1000000 : Rat) 40 ≤ 1 :=
    Rat.le_trans (rat_mul_le_mul_of_nonneg_left hbase_le (ratPow_nonneg hθ0 64)) hθ
  have hlt_pow : ratPow θ 64 < ratPow (invPow2Rat 12) 64 := by
    have hbase_pos : (0 : Rat) < ratPow (1000000 : Rat) 40 := ratPow_pos (by decide) 40
    have hpow2_lt := pow2_12_pow64_lt_base1M_pow40
    have hinv_eq : ratPow (invPow2Rat 12) 64 * ratPow (pow2Rat 12) 64 = 1 :=
      ratPow_div_one (pow2Rat_ne_zero 12) 64
    apply rat_lt_of_mul_pos_right hbase_pos
    have h1 : ratPow (invPow2Rat 12) 64 * ratPow (pow2Rat 12) 64 <
        ratPow (invPow2Rat 12) 64 * ratPow (1000000 : Rat) 40 :=
      rat_mul_lt_mul_of_pos_left hpow2_lt (ratPow_pos (invPow2Rat_pos 12) 64)
    rw [hinv_eq] at h1
    exact rat_lt_of_le_of_lt hθ40 h1
  exact rat_lt_of_ratPow_lt hθ0 (Rat.le_of_lt (invPow2Rat_pos 12)) (by decide) hlt_pow

/-- **Theorem 3 (`contiguous_mrope_bf16_width_freeze_exact`)**:
    Proves that in contiguous `mRoPE` (`pairs 40..63`, base `b = 10^6`), every Width pair
    satisfies `θ_k < 2^{-12}`, and for every patch offset `ΔW ∈ [1, 63]`:
    `(1/2)(ΔW · θ_k)^2 < 2^{-13} < 2^{-9}`, so `1 - (1/2)(ΔW · θ_k)^2 > 1 - 2^{-9}`,
    forcing `bf16SnapsToOne c` (`fl_BF16(c) = 1.0`) for every `c ∈ [1 - (1/2)(ΔW · θ_k)^2, 1]`. -/
theorem contiguous_mrope_bf16_width_freeze_exact :
    (ratPow (pow2Rat 12) 64 < ratPow (1000000 : Rat) 40) ∧
    (∀ (k : Nat) (θ : Rat), 40 ≤ k → k ≤ 63 → (0 : Rat) ≤ θ →
      ratPow θ 64 * ratPow (1000000 : Rat) k ≤ 1 →
      θ < invPow2Rat 12) ∧
    (∀ (dW : Nat) (θ : Rat), 1 ≤ dW → dW ≤ 63 → (0 : Rat) ≤ θ → θ ≤ invPow2Rat 12 →
      (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) < invPow2Rat 13 ∧
      (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) < invPow2Rat 9 ∧
      1 - invPow2Rat 9 < 1 - (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ)) ∧
    (∀ (k dW : Nat) (θ c : Rat),
      40 ≤ k → k ≤ 63 → 1 ≤ dW → dW ≤ 63 →
      (0 : Rat) ≤ θ → ratPow θ 64 * ratPow (1000000 : Rat) k ≤ 1 →
      1 - (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) ≤ c → c ≤ 1 →
      bf16SnapsToOne c) := by
  have hquad : ∀ (dW : Nat) (θ : Rat), 1 ≤ dW → dW ≤ 63 → (0 : Rat) ≤ θ → θ ≤ invPow2Rat 12 →
      (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) < invPow2Rat 13 ∧
      (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) < invPow2Rat 9 ∧
      1 - invPow2Rat 9 < 1 - (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) := by
    intro dW θ _ hdW hθ0 hθle
    have hdW_le : (dW : Rat) ≤ (63 : Rat) := rat_natCast_le hdW
    have hdW_nn : (0 : Rat) ≤ (dW : Rat) := rat_natCast_nonneg dW
    have hprod_le : (dW : Rat) * θ ≤ (63 : Rat) * invPow2Rat 12 := by
      have h1 := rat_mul_le_mul_of_nonneg_right hdW_le hθ0
      have h2 := rat_mul_le_mul_of_nonneg_left hθle (by decide : (0 : Rat) ≤ (63 : Rat))
      exact Rat.le_trans h1 h2
    have hprod_nn : (0 : Rat) ≤ (dW : Rat) * θ := Rat.mul_nonneg hdW_nn hθ0
    have hsq_le : ((dW : Rat) * θ) * ((dW : Rat) * θ) ≤
        ((63 : Rat) * invPow2Rat 12) * ((63 : Rat) * invPow2Rat 12) := by
      have h1 := rat_mul_le_mul_of_nonneg_right hprod_le hprod_nn
      have h2 := rat_mul_le_mul_of_nonneg_left hprod_le
        (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 63) (Rat.le_of_lt (invPow2Rat_pos 12)))
      exact Rat.le_trans h1 h2
    have hhalf_pos : (0 : Rat) < (1 / 2 : Rat) := rat_div_pos (by decide) (by decide)
    have hhalf_le : (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) ≤
        (1 / 2 : Rat) * (((63 : Rat) * invPow2Rat 12) * ((63 : Rat) * invPow2Rat 12)) := by
      have heq : (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) =
          (1 / 2 : Rat) * (((dW : Rat) * θ) * ((dW : Rat) * θ)) := by grind
      rw [heq]
      exact rat_mul_le_mul_of_nonneg_left hsq_le (Rat.le_of_lt hhalf_pos)
    have hnum13 : (1 / 2 : Rat) * (((63 : Rat) * invPow2Rat 12) * ((63 : Rat) * invPow2Rat 12)) <
        invPow2Rat 13 := by
      -- Multiply both sides by `2 * 2^24 = 2^25`
      apply rat_lt_of_mul_pos_right (pow2Rat_pos 25)
      have hp12 : pow2Rat 12 = 4096 := by unfold pow2Rat; rfl
      have hp13 : pow2Rat 13 = 8192 := by unfold pow2Rat; rfl
      have hp25 : pow2Rat 25 = 33554432 := by unfold pow2Rat; rfl
      have hl : (1 / 2 : Rat) * (((63 : Rat) * invPow2Rat 12) * ((63 : Rat) * invPow2Rat 12)) * pow2Rat 25 = 3969 := by
        unfold invPow2Rat; rw [hp12, hp25]; grind
      have hr : invPow2Rat 13 * pow2Rat 25 = 4096 := by
        unfold invPow2Rat; rw [hp13, hp25]; grind
      rw [hl, hr]; decide
    have h13_lt_9 : invPow2Rat 13 < invPow2Rat 9 := by
      apply rat_lt_of_mul_pos_right (pow2Rat_pos 13)
      have hp13 : pow2Rat 13 = 8192 := by unfold pow2Rat; rfl
      have hp9 : pow2Rat 9 = 512 := by unfold pow2Rat; rfl
      have hl : invPow2Rat 13 * pow2Rat 13 = 1 := by unfold invPow2Rat; rw [hp13]; grind
      have hr : invPow2Rat 9 * pow2Rat 13 = 16 := by unfold invPow2Rat; rw [hp9, hp13]; grind
      rw [hl, hr]; decide
    have hlt13 : (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) < invPow2Rat 13 :=
      rat_lt_of_le_of_lt hhalf_le hnum13
    have hlt9 : (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) < invPow2Rat 9 :=
      rat_lt_trans hlt13 h13_lt_9
    have hsub : 1 - invPow2Rat 9 < 1 - (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) := by
      apply rat_lt_of_sub_pos
      have heq : (1 - (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ)) - (1 - invPow2Rat 9) =
          invPow2Rat 9 - (1 / 2 : Rat) * ((dW : Rat) * θ) * ((dW : Rat) * θ) := by grind
      rw [heq]
      exact rat_sub_pos hlt9
    exact ⟨hlt13, hlt9, hsub⟩
  refine ⟨pow2_12_pow64_lt_base1M_pow40, ?_, hquad, ?_⟩
  · intro k θ hk _ hθ0 hθ
    exact width_pair_freq_lt_invPow2_12 hk hθ0 hθ
  · intro k dW θ c hk _ hdW1 hdW63 hθ0 hθ hc1 hc2
    have hθlt : θ < invPow2Rat 12 := width_pair_freq_lt_invPow2_12 hk hθ0 hθ
    have hq := (hquad dW θ hdW1 hdW63 hθ0 (Rat.le_of_lt hθlt)).2.2
    unfold bf16SnapsToOne rneSnapsToOne
    exact ⟨Rat.le_trans (Rat.le_of_lt hq) hc1, hc2⟩

/-! ### Part 2: Interleaved vs Contiguous `mRoPE` Resolution Gap (Theorem 4) -/

theorem geomResContigW_closed_form (θ0sq q : Rat) :
    geomResContigW θ0sq q * (1 - q) =
      (1 / 2 : Rat) * θ0sq * ratPow q 40 * (1 - ratPow q 24) := by
  unfold geomResContigW
  have hcongr : finSum (fun j : Fin 24 => θ0sq * ratPow q (40 + j.val)) =
      (θ0sq * ratPow q 40) * finSum (fun j : Fin 24 => ratPow q j.val) := by
    rw [← finSum_mul_left]
    apply finSum_congr
    intro j
    rw [ratPow_add, Rat.mul_assoc]
  rw [hcongr]
  have hgeom := finSum_geom_mul q 24
  have hmul : (1 / 2 : Rat) * (θ0sq * ratPow q 40 * finSum (fun j : Fin 24 => ratPow q j.val)) *
      (1 - q) =
      (1 / 2 : Rat) * θ0sq * ratPow q 40 *
        (finSum (fun j : Fin 24 => ratPow q j.val) * (1 - q)) := by grind
  rw [hmul, hgeom]

theorem geomResInterleavedStride3_closed_form (θ0sq q : Rat) :
    geomResInterleavedStride3 θ0sq q * (1 - ratPow q 3) =
      (1 / 2 : Rat) * θ0sq * ratPow q 2 * (1 - ratPow q 72) := by
  unfold geomResInterleavedStride3
  have hcongr : finSum (fun j : Fin 24 => θ0sq * ratPow q (2 + 3 * j.val)) =
      (θ0sq * ratPow q 2) * finSum (fun j : Fin 24 => ratPow (ratPow q 3) j.val) := by
    rw [← finSum_mul_left]
    apply finSum_congr
    intro j
    rw [ratPow_add, ratPow_mul, Rat.mul_assoc]
  rw [hcongr]
  have hgeom := finSum_geom_mul (ratPow q 3) 24
  rw [← ratPow_mul] at hgeom
  have hmul : (1 / 2 : Rat) * (θ0sq * ratPow q 2 *
        finSum (fun j : Fin 24 => ratPow (ratPow q 3) j.val)) * (1 - ratPow q 3) =
      (1 / 2 : Rat) * θ0sq * ratPow q 2 *
        (finSum (fun j : Fin 24 => ratPow (ratPow q 3) j.val) * (1 - ratPow q 3)) := by grind
  rw [hmul, hgeom]

/-- Lower bound: Qwen3-VL interleaved `(16, 24, 24)` Width resolution is at least its leading
    pair `k = 2`, i.e. `(1/2) * θ0sq * q^2`. -/
theorem geomResQwen3InterleavedW_ge_lead {θ0sq q : Rat} (hθ : (0 : Rat) ≤ θ0sq) (hq : (0 : Rat) ≤ q) :
    (1 / 2 : Rat) * θ0sq * ratPow q 2 ≤ geomResQwen3InterleavedW θ0sq q := by
  unfold geomResQwen3InterleavedW
  have hterm_nn : ∀ j : Fin 24, (0 : Rat) ≤ θ0sq * ratPow q (qwen3InterleavedWIdx j) :=
    fun j => Rat.mul_nonneg hθ (ratPow_nonneg hq _)
  -- Extract the `j = 0` term (`qwen3InterleavedWIdx 0 = 2`) from `finSum`.
  have hge0 : θ0sq * ratPow q 2 ≤
      finSum (fun j : Fin 24 => θ0sq * ratPow q (qwen3InterleavedWIdx j)) := by
    have haux : ∀ (k : Nat) (hk : 0 < k) (f : Fin k → Rat),
        (∀ j, (0 : Rat) ≤ f j) → f ⟨0, hk⟩ ≤ finSum f := by
      intro k
      induction k with
      | zero => intro hk; exact absurd hk (by decide)
      | succ k ih =>
        intro _ f hf
        unfold finSum
        simp only [finSumAux]
        cases k with
        | zero =>
          simp only [finSumAux, Rat.zero_add]
          exact Rat.le_refl
        | succ k' =>
          have hih := ih (Nat.succ_pos k') (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
            (fun j => hf ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
          unfold finSum at hih
          have hadd := rat_add_le_add hih (hf ⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩)
          rw [Rat.add_zero] at hadd
          exact hadd
    have h0 := haux 24 (by decide) (fun j : Fin 24 => θ0sq * ratPow q (qwen3InterleavedWIdx j)) hterm_nn
    have hidx0 : qwen3InterleavedWIdx ⟨0, by decide⟩ = 2 := by decide
    rw [hidx0] at h0
    exact h0
  have hmul := rat_mul_le_mul_of_nonneg_left hge0
    (Rat.le_of_lt (rat_div_pos (by decide : (0 : Rat) < 1) (by decide : (0 : Rat) < 2)))
  have heq : (1 / 2 : Rat) * (θ0sq * ratPow q 2) = (1 / 2 : Rat) * θ0sq * ratPow q 2 := by grind
  rw [← heq]
  exact hmul

/-- **Theorem 4 (`interleaved_vs_contiguous_mrope_resolution_gap`)**:
    Proves the exact closed-form geometric resolution formulas for contiguous Width (`pairs 40..63`)
    and stride-3 interleaved Width (`pairs 2, 5, ..., 71`), their exact ratio
    `(1 / q^{38}) * (1 + q^{24} + q^{48}) / (1 + q + q^2)`, the exact `b^{76/64}` power law
    `(1 / q^{38})^{16} = b^{19}` when `q^{32} * b = 1`, and for `b = 10^6` proves strictly
    `> 10^7×` leading-pair gain and `> 10^6×` full-sum local spatial resolution gain for both
    stride-3 round-robin and Qwen3-VL 64-pair interleaved `mRoPE`. -/
theorem interleaved_vs_contiguous_mrope_resolution_gap :
    (∀ (θ0sq q : Rat),
      geomResContigW θ0sq q * (1 - q) =
        (1 / 2 : Rat) * θ0sq * ratPow q 40 * (1 - ratPow q 24) ∧
      geomResInterleavedStride3 θ0sq q * (1 - ratPow q 3) =
        (1 / 2 : Rat) * θ0sq * ratPow q 2 * (1 - ratPow q 72)) ∧
    (∀ (θ0sq q : Rat), (0 : Rat) < θ0sq → (0 : Rat) < q → q < 1 →
      (θ0sq * ratPow q 2) / (θ0sq * ratPow q 40) = 1 / ratPow q 38 ∧
      geomResInterleavedStride3 θ0sq q / geomResContigW θ0sq q =
        (1 / ratPow q 38) * ((1 + ratPow q 24 + ratPow q 48) / (1 + q + q * q))) ∧
    (∀ (q b : Rat), (0 : Rat) < q → (0 : Rat) < b → ratPow q 32 * b = 1 →
      ratPow (1 / ratPow q 38) 16 = ratPow b 19) ∧
    (∀ (θ0sq q : Rat), (0 : Rat) < θ0sq → (0 : Rat) < q → q < 1 →
      ratPow q 32 * (1000000 : Rat) = 1 →
      (10000000 : Rat) < 1 / ratPow q 38 ∧
      (1000000 : Rat) < geomResInterleavedStride3 θ0sq q / geomResContigW θ0sq q ∧
      (1000000 : Rat) < geomResQwen3InterleavedW θ0sq q / geomResContigW θ0sq q) := by
  have hratio : ∀ (θ0sq q : Rat), (0 : Rat) < θ0sq → (0 : Rat) < q → q < 1 →
      (θ0sq * ratPow q 2) / (θ0sq * ratPow q 40) = 1 / ratPow q 38 ∧
      geomResInterleavedStride3 θ0sq q / geomResContigW θ0sq q =
        (1 / ratPow q 38) * ((1 + ratPow q 24 + ratPow q 48) / (1 + q + q * q)) := by
    intro θ0sq q hθ hq0 hq1
    have hθ_ne : θ0sq ≠ 0 := Rat.ne_of_gt hθ
    have hq38_ne : ratPow q 38 ≠ 0 := ratPow_ne_zero hq0 38
    have hq40_ne : ratPow q 40 ≠ 0 := ratPow_ne_zero hq0 40
    have h1mq_pos : (0 : Rat) < 1 - q := rat_sub_pos hq1
    have h1mq_ne : 1 - q ≠ 0 := Rat.ne_of_gt h1mq_pos
    have h1mq24_pos : (0 : Rat) < 1 - ratPow q 24 :=
      rat_sub_pos (ratPow_one_lt_of_lt_one hq0 hq1 (by decide))
    have h1mq24_ne : 1 - ratPow q 24 ≠ 0 := Rat.ne_of_gt h1mq24_pos
    have hq3_lt1 : ratPow q 3 < 1 := ratPow_one_lt_of_lt_one hq0 hq1 (by decide)
    have h1mq3_pos : (0 : Rat) < 1 - ratPow q 3 := rat_sub_pos hq3_lt1
    have h1mq3_ne : 1 - ratPow q 3 ≠ 0 := Rat.ne_of_gt h1mq3_pos
    have h1qq_pos : (0 : Rat) < 1 + q + q * q :=
      rat_add_pos (rat_add_pos (by decide) hq0) (rat_mul_pos hq0 hq0)
    have h1qq_ne : 1 + q + q * q ≠ 0 := Rat.ne_of_gt h1qq_pos
    have hq40_eq : ratPow q 40 = ratPow q 2 * ratPow q 38 := by
      have h : (40 : Nat) = 2 + 38 := by decide
      rw [h, ratPow_add]
    have hlead : (θ0sq * ratPow q 2) / (θ0sq * ratPow q 40) = 1 / ratPow q 38 := by
      have hden_ne : θ0sq * ratPow q 40 ≠ 0 := Rat.ne_of_gt (rat_mul_pos hθ (ratPow_pos hq0 40))
      apply (rat_div_eq_iff hden_ne).mpr
      rw [hq40_eq]
      have h1 : (1 / ratPow q 38) * (θ0sq * (ratPow q 2 * ratPow q 38)) =
          θ0sq * ratPow q 2 * ((1 / ratPow q 38) * ratPow q 38) := by grind
      rw [h1, rat_div_mul_cancel hq38_ne, Rat.mul_one]
    have hcontig_pos : (0 : Rat) < geomResContigW θ0sq q := by
      have hc := geomResContigW_closed_form θ0sq q
      have hhalf_pos : (0 : Rat) < (1 / 2 : Rat) := rat_div_pos (by decide) (by decide)
      have hrhs_pos : (0 : Rat) < (1 / 2 : Rat) * θ0sq * ratPow q 40 * (1 - ratPow q 24) :=
        rat_mul_pos (rat_mul_pos (rat_mul_pos hhalf_pos hθ) (ratPow_pos hq0 40)) h1mq24_pos
      rw [← hc] at hrhs_pos
      apply rat_lt_of_mul_pos_right h1mq_pos
      rw [Rat.zero_mul]; exact hrhs_pos
    have hcontig_ne : geomResContigW θ0sq q ≠ 0 := Rat.ne_of_gt hcontig_pos
    have hfull : geomResInterleavedStride3 θ0sq q / geomResContigW θ0sq q =
        (1 / ratPow q 38) * ((1 + ratPow q 24 + ratPow q 48) / (1 + q + q * q)) := by
      -- Cross-multiply by `geomResContigW * (1 - q^3) * (1 - q) * q^38`
      have hfactor3 : 1 - ratPow q 3 = (1 - q) * (1 + q + q * q) := by
        simp only [ratPow]; grind
      have hfactor72 : 1 - ratPow q 72 = (1 - ratPow q 24) * (1 + ratPow q 24 + ratPow q 48) := by
        have h48 : ratPow q 48 = ratPow q 24 * ratPow q 24 := by
          have h : (48 : Nat) = 24 + 24 := by decide
          rw [h, ratPow_add]
        have h72 : ratPow q 72 = ratPow q 24 * ratPow q 48 := by
          have h : (72 : Nat) = 24 + 48 := by decide
          rw [h, ratPow_add]
        rw [h72, h48]; grind
      have hc := geomResContigW_closed_form θ0sq q
      have hi := geomResInterleavedStride3_closed_form θ0sq q
      apply (rat_div_eq_iff hcontig_ne).mpr
      -- Multiply both sides by `(1 - q^3) = (1 - q) * (1 + q + q^2)`
      have hmul_eq : geomResInterleavedStride3 θ0sq q * (1 - ratPow q 3) =
          ((1 / ratPow q 38) * ((1 + ratPow q 24 + ratPow q 48) / (1 + q + q * q)) *
            geomResContigW θ0sq q) * (1 - ratPow q 3) := by
        rw [hi, hfactor72, hfactor3]
        have hrearr : ((1 / ratPow q 38) * ((1 + ratPow q 24 + ratPow q 48) / (1 + q + q * q)) *
              geomResContigW θ0sq q) * ((1 - q) * (1 + q + q * q)) =
            (1 / ratPow q 38) *
              (((1 + ratPow q 24 + ratPow q 48) / (1 + q + q * q)) * (1 + q + q * q)) *
              (geomResContigW θ0sq q * (1 - q)) := by grind
        rw [hrearr, rat_div_mul_cancel h1qq_ne, hc, hq40_eq]
        have hrearr2 : (1 / ratPow q 38) * (1 + ratPow q 24 + ratPow q 48) *
              ((1 / 2 : Rat) * θ0sq * (ratPow q 2 * ratPow q 38) * (1 - ratPow q 24)) =
            (1 / 2 : Rat) * θ0sq * ratPow q 2 * ((1 - ratPow q 24) * (1 + ratPow q 24 + ratPow q 48)) *
              ((1 / ratPow q 38) * ratPow q 38) := by grind
        rw [hrearr2, rat_div_mul_cancel hq38_ne, Rat.mul_one]
      have hcancel : ∀ a b c : Rat, c ≠ 0 → a * c = b * c → a = b := by
        intro a b c hcne heq
        have h1 : (a * c) / c = (b * c) / c := congrArg (· / c) heq
        rw [Rat.div_def, Rat.div_def, Rat.mul_assoc, Rat.mul_assoc,
            Rat.mul_inv_cancel c hcne, Rat.mul_one, Rat.mul_one] at h1
        exact h1
      exact hcancel _ _ (1 - ratPow q 3) h1mq3_ne hmul_eq
    exact ⟨hlead, hfull⟩
  have hpowlaw : ∀ (q b : Rat), (0 : Rat) < q → (0 : Rat) < b → ratPow q 32 * b = 1 →
      ratPow (1 / ratPow q 38) 16 = ratPow b 19 := by
    intro q b hq0 _ hqb
    have hq38_ne : ratPow q 38 ≠ 0 := ratPow_ne_zero hq0 38
    have hprod1 : ratPow (1 / ratPow q 38) 16 * ratPow q (38 * 16) = 1 := by
      rw [ratPow_mul]
      exact ratPow_div_one hq38_ne 16
    have hprod2 : ratPow b 19 * ratPow q (32 * 19) = 1 := by
      rw [ratPow_mul, Rat.mul_comm, ← ratPow_mul_distrib, hqb]
      induction (19 : Nat) with
      | zero => rfl
      | succ n ih => rw [ratPow, ih, Rat.mul_one]
    have h608 : (38 * 16 : Nat) = 32 * 19 := by decide
    rw [h608] at hprod1
    have hq608_ne : ratPow q (32 * 19) ≠ 0 := ratPow_ne_zero hq0 (32 * 19)
    have heq : ratPow (1 / ratPow q 38) 16 * ratPow q (32 * 19) =
        ratPow b 19 * ratPow q (32 * 19) := hprod1.trans hprod2.symm
    have h1 := congrArg (· * (ratPow q (32 * 19))⁻¹) heq
    rw [Rat.mul_assoc, Rat.mul_assoc, Rat.mul_inv_cancel _ hq608_ne, Rat.mul_one, Rat.mul_one] at h1
    exact h1
  refine ⟨fun θ0sq q => ⟨geomResContigW_closed_form θ0sq q, geomResInterleavedStride3_closed_form θ0sq q⟩,
    hratio, hpowlaw, ?_⟩
  intro θ0sq q hθ hq0 hq1 hq1M
  have hq38_pos : (0 : Rat) < ratPow q 38 := ratPow_pos hq0 38
  have hinv_pos : (0 : Rat) < 1 / ratPow q 38 := rat_div_pos (by decide) hq38_pos
  have hpow19 : ratPow (1 / ratPow q 38) 16 = ratPow (1000000 : Rat) 19 :=
    hpowlaw q 1000000 hq0 (by decide) hq1M
  -- Prove `10^7 < 1 / q^38` via `(10^7)^16 = 10^112 < 10^114 = (10^6)^19 = (1 / q^38)^16`.
  have hgt10M : (10000000 : Rat) < 1 / ratPow q 38 := by
    apply rat_lt_of_ratPow_lt (by decide) (Rat.le_of_lt hinv_pos) (by decide : 0 < 16)
    rw [hpow19]
    have h10_112 : ratPow (10000000 : Rat) 16 = ratPow ((10 : Nat) : Rat) 112 := by
      have h : (10000000 : Rat) = ratPow ((10 : Nat) : Rat) 7 := by rw [ratPow_natCast]; decide
      rw [h, ← ratPow_mul]
    have h10_114 : ratPow (1000000 : Rat) 19 = ratPow ((10 : Nat) : Rat) 114 := by
      have h : (1000000 : Rat) = ratPow ((10 : Nat) : Rat) 6 := by rw [ratPow_natCast]; decide
      rw [h, ← ratPow_mul]
    rw [h10_112, h10_114]
    have h114 : (114 : Nat) = 112 + 2 := by decide
    rw [h114, ratPow_add]
    have h100 : (1 : Rat) < ratPow ((10 : Nat) : Rat) 2 := by rw [ratPow_natCast]; decide
    have hmul := rat_mul_lt_mul_of_pos_left h100 (ratPow_pos (by decide : (0 : Rat) < ((10 : Nat) : Rat)) 112)
    rw [Rat.mul_one] at hmul
    exact hmul
  -- Prove `10^6 < geomResInterleavedStride3 / geomResContigW`
  have hstride3_gt : (1000000 : Rat) < geomResInterleavedStride3 θ0sq q / geomResContigW θ0sq q := by
    rw [(hratio θ0sq q hθ hq0 hq1).2]
    have hnum_gt1 : (1 : Rat) < 1 + ratPow q 24 + ratPow q 48 := by
      have hpos := rat_add_pos (ratPow_pos hq0 24) (ratPow_pos hq0 48)
      apply rat_lt_of_sub_pos
      have heq : 1 + ratPow q 24 + ratPow q 48 - 1 = ratPow q 24 + ratPow q 48 := by grind
      rw [heq]; exact hpos
    have hden_lt3 : 1 + q + q * q < (3 : Rat) := by
      have hq2_lt1 : q * q < 1 := by
        have h1 := rat_mul_lt_mul_of_pos_right hq1 hq0
        rw [Rat.one_mul] at h1
        exact rat_lt_trans h1 hq1
      have h1 : q + q * q ≤ 2 := by
        have h1' := rat_add_le_add (Rat.le_of_lt hq1) (Rat.le_of_lt hq2_lt1)
        have h2 : (1 : Rat) + 1 = 2 := by grind
        rw [h2] at h1'; exact h1'
      have hne : q + q * q ≠ (2 : Rat) := by
        intro heq
        have hsub : (0 : Rat) < (1 - q) + (1 - q * q) :=
          rat_add_pos (rat_sub_pos hq1) (rat_sub_pos hq2_lt1)
        have hz : (1 - q) + (1 - q * q) = 0 := by grind
        rw [hz] at hsub
        exact Rat.not_le.mpr hsub Rat.le_refl
      have hlt2 : q + q * q < 2 := Rat.lt_of_le_of_ne h1 hne
      apply rat_lt_of_sub_pos
      have heq : (3 : Rat) - (1 + q + q * q) = 2 - (q + q * q) := by grind
      rw [heq]; exact rat_sub_pos hlt2
    have hden_pos : (0 : Rat) < 1 + q + q * q :=
      rat_add_pos (rat_add_pos (by decide) hq0) (rat_mul_pos hq0 hq0)
    have h1_3_pos : (0 : Rat) < (1 / 3 : Rat) := rat_div_pos (by decide) (by decide)
    have hfrac_gt : (1 / 3 : Rat) < (1 + ratPow q 24 + ratPow q 48) / (1 + q + q * q) := by
      apply rat_lt_div_of_mul_lt hden_pos
      have h1 : (1 / 3 : Rat) * (1 + q + q * q) < (1 / 3 : Rat) * 3 :=
        rat_mul_lt_mul_of_pos_left hden_lt3 h1_3_pos
      have h3 : (1 / 3 : Rat) * 3 = 1 := by grind
      rw [h3] at h1
      exact rat_lt_trans h1 hnum_gt1
    have hprod := rat_mul_lt_mul_of_pos_left hfrac_gt hinv_pos
    have hprod2 := rat_mul_lt_mul_of_pos_right hgt10M h1_3_pos
    have h3M : (1000000 : Rat) < (10000000 : Rat) * (1 / 3 : Rat) := by
      apply rat_lt_of_mul_pos_right (by decide : (0 : Rat) < 3)
      have hr : (10000000 : Rat) * (1 / 3 : Rat) * 3 = 10000000 := by grind
      have hl : (1000000 : Rat) * 3 = 3000000 := by grind
      rw [hr, hl]; decide
    have hfinal : (1000000 : Rat) < (1 / ratPow q 38) * (1 / 3 : Rat) :=
      rat_lt_trans h3M hprod2
    exact rat_lt_trans hfinal hprod
  -- Prove `10^6 < geomResQwen3InterleavedW / geomResContigW`
  -- First show `q < 7/10` from `q^{32} = 10^{-6} < (7/10)^{32}` (since `7^{32} > 10^{26}`).
  have hq_lt_7_10 : q < (7 / 10 : Rat) := by
    have h7_10_nn : (0 : Rat) ≤ (7 / 10 : Rat) :=
      Rat.le_of_lt (rat_div_pos (by decide) (by decide))
    apply rat_lt_of_ratPow_lt (Rat.le_of_lt hq0) h7_10_nn (by decide : 0 < 32)
    have h7_32 : (10 ^ 26 : Nat) < 7 ^ 32 := by decide
    have hq32_eq : ratPow q 32 = (1 : Rat) / (1000000 : Rat) :=
      ((rat_div_eq_iff (by decide : (1000000 : Rat) ≠ 0)).mpr hq1M.symm).symm
    rw [hq32_eq]
    have h710_eq : ratPow (7 / 10 : Rat) 32 = ((7 ^ 32 : Nat) : Rat) / ((10 ^ 32 : Nat) : Rat) := by
      have hdiv : (7 / 10 : Rat) = ((7 : Nat) : Rat) * ((1 : Rat) / ((10 : Nat) : Rat)) := by grind
      rw [hdiv, ratPow_mul_distrib, ratPow_natCast]
      have h10_ne : ((10 ^ 32 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (Nat.pow_pos (by decide)))
      apply Eq.symm
      apply (rat_div_eq_iff h10_ne).mpr
      rw [Rat.mul_assoc, ← ratPow_natCast 10 32, ratPow_div_one (by decide : ((10 : Nat) : Rat) ≠ 0) 32, Rat.mul_one]
    rw [h710_eq]
    have h10_32_pos : (0 : Rat) < ((10 ^ 32 : Nat) : Rat) :=
      rat_natCast_pos (Nat.pow_pos (by decide))
    apply rat_lt_div_of_mul_lt h10_32_pos
    have hmul_eq : ((1 : Rat) / (1000000 : Rat)) * ((10 ^ 32 : Nat) : Rat) = ((10 ^ 26 : Nat) : Rat) := by
      have h10 : (10 ^ 32 : Nat) = 10 ^ 26 * 1000000 := by decide
      rw [h10, Rat.natCast_mul]
      have h1Mcast : ((1000000 : Nat) : Rat) = (1000000 : Rat) := rfl
      rw [h1Mcast]
      have heq : ((1 : Rat) / (1000000 : Rat)) * (((10 ^ 26 : Nat) : Rat) * (1000000 : Rat)) =
          ((10 ^ 26 : Nat) : Rat) * (((1 : Rat) / (1000000 : Rat)) * (1000000 : Rat)) := by grind
      rw [heq, rat_div_mul_cancel (by decide : (1000000 : Rat) ≠ 0), Rat.mul_one]
    rw [hmul_eq]
    exact rat_natCast_lt h7_32
  have hqwen3_gt : (1000000 : Rat) < geomResQwen3InterleavedW θ0sq q / geomResContigW θ0sq q := by
    have h1mq_pos : (0 : Rat) < 1 - q := rat_sub_pos hq1
    have h1mq_gt : (3 / 10 : Rat) < 1 - q := by
      apply rat_lt_of_sub_pos
      have heq : (1 - q) - (3 / 10 : Rat) = (7 / 10 : Rat) - q := by grind
      rw [heq]; exact rat_sub_pos hq_lt_7_10
    have h1mq24_pos : (0 : Rat) < 1 - ratPow q 24 :=
      rat_sub_pos (ratPow_one_lt_of_lt_one hq0 hq1 (by decide))
    have hhalf_pos : (0 : Rat) < (1 / 2 : Rat) := rat_div_pos (by decide) (by decide)
    have hc_pos : (0 : Rat) < geomResContigW θ0sq q := by
      have hc := geomResContigW_closed_form θ0sq q
      have hrhs : (0 : Rat) < (1 / 2 : Rat) * θ0sq * ratPow q 40 * (1 - ratPow q 24) :=
        rat_mul_pos (rat_mul_pos (rat_mul_pos hhalf_pos hθ) (ratPow_pos hq0 40)) h1mq24_pos
      rw [← hc] at hrhs
      apply rat_lt_of_mul_pos_right h1mq_pos
      rw [Rat.zero_mul]; exact hrhs
    apply rat_lt_div_of_mul_lt hc_pos
    have hlead_le : (1 / 2 : Rat) * θ0sq * ratPow q 2 ≤ geomResQwen3InterleavedW θ0sq q :=
      geomResQwen3InterleavedW_ge_lead (Rat.le_of_lt hθ) (Rat.le_of_lt hq0)
    -- Show `10^6 * geomResContigW < (1/2) * θ0sq * q^2` by multiplying by `(1 - q) > 0`.
    have hstrict : (1000000 : Rat) * geomResContigW θ0sq q < (1 / 2 : Rat) * θ0sq * ratPow q 2 := by
      apply rat_lt_of_mul_pos_right h1mq_pos
      rw [Rat.mul_assoc, geomResContigW_closed_form]
      have hq40_eq : ratPow q 40 = ratPow q 2 * ratPow q 38 := by
        have h : (40 : Nat) = 2 + 38 := by decide
        rw [h, ratPow_add]
      rw [hq40_eq]
      have h1mq24_lt1 : 1 - ratPow q 24 < 1 := by
        apply rat_lt_of_sub_pos
        have heq : 1 - (1 - ratPow q 24) = ratPow q 24 := by grind
        rw [heq]; exact ratPow_pos hq0 24
      have hcoeff_pos : (0 : Rat) < (1 / 2 : Rat) * θ0sq * ratPow q 2 :=
        rat_mul_pos (rat_mul_pos hhalf_pos hθ) (ratPow_pos hq0 2)
      -- Compare `10^6 * q^38 * (1 - q^24) < 1 - q`:
      have hq38_lt : (1000000 : Rat) * ratPow q 38 < (1 / 10 : Rat) := by
        have h1 : (10000000 : Rat) * ratPow q 38 < (1 / ratPow q 38) * ratPow q 38 :=
          rat_mul_lt_mul_of_pos_right hgt10M hq38_pos
        rw [rat_div_mul_cancel (Rat.ne_of_gt hq38_pos)] at h1
        have h2 : (1000000 : Rat) * ratPow q 38 = ((10000000 : Rat) * ratPow q 38) / (10 : Rat) := by grind
        rw [h2]
        exact rat_div_lt_of_mul_lt (by decide) (by
          have heq : (1 / 10 : Rat) * 10 = 1 := by grind
          rw [heq]; exact h1)
      have h1_10_lt_3_10 : (1 / 10 : Rat) < (3 / 10 : Rat) := by
        apply rat_lt_of_mul_pos_right (by decide : (0 : Rat) < 10)
        have hl : (1 / 10 : Rat) * 10 = 1 := by grind
        have hr : (3 / 10 : Rat) * 10 = 3 := by grind
        rw [hl, hr]; decide
      have hlt_1mq : (1000000 : Rat) * ratPow q 38 * (1 - ratPow q 24) < 1 - q := by
        have h1 := rat_mul_lt_mul_of_pos_left h1mq24_lt1 (rat_mul_pos (by decide : (0 : Rat) < 1000000) hq38_pos)
        rw [Rat.mul_one] at h1
        exact rat_lt_trans h1 (rat_lt_trans hq38_lt (rat_lt_trans h1_10_lt_3_10 h1mq_gt))
      have hfinal := rat_mul_lt_mul_of_pos_left hlt_1mq hcoeff_pos
      have hlhs_eq : (1000000 : Rat) * ((1 / 2 : Rat) * θ0sq * (ratPow q 2 * ratPow q 38) * (1 - ratPow q 24)) =
          ((1 / 2 : Rat) * θ0sq * ratPow q 2) * ((1000000 : Rat) * ratPow q 38 * (1 - ratPow q 24)) := by grind
      rw [hlhs_eq]
      exact hfinal
    exact rat_lt_of_lt_of_le hstrict hlead_le
  exact ⟨hgt10M, hstride3_gt, hqwen3_gt⟩

end Mrope3dCoprime
