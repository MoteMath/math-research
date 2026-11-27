/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CeLseHorizon.CeConservation

/-!
# FP16 Loss-Scale Empty-Window Collapse, LogSumExp Swamping vs Pairwise Tree, & Label Smoothing Erasure

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
4. `fp16_loss_scale_empty_window_collapse_exact`
5. `lse_naive_swamping_vs_pairwise_tree_exact`
6. `label_smoothing_fp8_total_erasure_exact`
-/

namespace CeLseHorizon

/-! ### Theorem 4: FP16 Dynamic Loss-Scaling Empty-Window Collapse -/

theorem fp16_normal_window_empty {gMax pMin : Rat} (hg : (0 : Rat) < gMax) (hp : (0 : Rat) < pMin)
    (hratio : (1073479680 : Rat) ≤ gMax / pMin) (S : Rat) (_hS : (0 : Rat) < S) :
    ¬fp16NormalSafe S gMax pMin := by
  intro ⟨hovf, hnorm⟩
  unfold fp16OverflowThresh at hovf
  unfold fp16MinNorm at hnorm
  have h1 : (1 : Rat) ≤ S * pMin * pow2Rat 14 := by
    have hm := rat_mul_le_mul_of_nonneg_right hnorm (Rat.le_of_lt (pow2Rat_pos 14))
    rw [invPow2Rat_mul_pow2Rat 14] at hm
    exact hm
  have h2 : gMax ≤ S * gMax * (pMin * pow2Rat 14) := by
    have hm := rat_mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hg)
    have eq1 : S * pMin * pow2Rat 14 * gMax = S * gMax * (pMin * pow2Rat 14) := by grind
    rw [Rat.one_mul, eq1] at hm
    exact hm
  have h3 : S * gMax * (pMin * pow2Rat 14) < (65520 : Rat) * (pMin * pow2Rat 14) :=
    rat_mul_lt_mul_of_pos_right hovf (rat_mul_pos hp (pow2Rat_pos 14))
  have h4 : gMax < (65520 : Rat) * pow2Rat 14 * pMin := by
    have eq2 : (65520 : Rat) * (pMin * pow2Rat 14) = (65520 : Rat) * pow2Rat 14 * pMin := by grind
    rw [← eq2]
    exact rat_lt_of_le_of_lt h2 h3
  have h5 : gMax / pMin < (65520 : Rat) * pow2Rat 14 := rat_div_lt_of_mul_lt hp h4
  have hconst : (65520 : Rat) * pow2Rat 14 = (1073479680 : Rat) := by
    unfold pow2Rat
    have hpow : (2 ^ 14 : Nat) = 16384 := by decide
    rw [hpow]
    grind
  rw [hconst] at h5
  exact Rat.not_le.mpr h5 hratio

theorem fp16_subnormal_window_empty {gMax pMin : Rat} (hg : (0 : Rat) < gMax) (hp : (0 : Rat) < pMin)
    (hratio : (2198486384640 : Rat) ≤ gMax / pMin) (S : Rat) (_hS : (0 : Rat) < S) :
    ¬fp16SubnormalSafe S gMax pMin := by
  intro ⟨hovf, hsub⟩
  unfold fp16OverflowThresh at hovf
  unfold fp16MinSubRneThresh at hsub
  have h1 : (1 : Rat) < S * pMin * pow2Rat 25 := by
    have hm := rat_mul_lt_mul_of_pos_right hsub (pow2Rat_pos 25)
    rw [invPow2Rat_mul_pow2Rat 25] at hm
    exact hm
  have h2 : gMax < S * gMax * (pMin * pow2Rat 25) := by
    have hm := rat_mul_lt_mul_of_pos_right h1 hg
    have eq1 : S * pMin * pow2Rat 25 * gMax = S * gMax * (pMin * pow2Rat 25) := by grind
    rw [Rat.one_mul, eq1] at hm
    exact hm
  have h3 : S * gMax * (pMin * pow2Rat 25) < (65520 : Rat) * (pMin * pow2Rat 25) :=
    rat_mul_lt_mul_of_pos_right hovf (rat_mul_pos hp (pow2Rat_pos 25))
  have h4 : gMax < (65520 : Rat) * pow2Rat 25 * pMin := by
    have eq2 : (65520 : Rat) * (pMin * pow2Rat 25) = (65520 : Rat) * pow2Rat 25 * pMin := by grind
    rw [← eq2]
    exact rat_lt_trans h2 h3
  have h5 : gMax / pMin < (65520 : Rat) * pow2Rat 25 := rat_div_lt_of_mul_lt hp h4
  have hconst : (65520 : Rat) * pow2Rat 25 = (2198486384640 : Rat) := by
    unfold pow2Rat
    have hpow : (2 ^ 25 : Nat) = 33554432 := by decide
    rw [hpow]
    grind
  rw [hconst] at h5
  exact Rat.not_le.mpr h5 hratio

theorem fp16_loss_scale_empty_window_collapse_exact :
    ((65520 : Rat) * pow2Rat 14 = (1073479680 : Rat) ∧
     (65520 : Nat) * 2 ^ 14 = 2 ^ 30 - 2 ^ 18 ∧
     (65520 : Nat) * 2 ^ 14 = 1073479680) ∧
    ((65520 : Rat) * pow2Rat 25 = (2198486384640 : Rat) ∧
     (65520 : Nat) * 2 ^ 25 = 2 ^ 41 - 2 ^ 29 ∧
     (65520 : Nat) * 2 ^ 25 = 2198486384640) ∧
    (∀ (gMax pMin : Rat), (0 : Rat) < gMax → (0 : Rat) < pMin →
      (1073479680 : Rat) ≤ gMax / pMin →
      (∀ S : Rat, (0 : Rat) < S → ¬fp16NormalSafe S gMax pMin) ∧
      (∀ k : Int, ¬fp16NormalSafe (pow2IntRat k) gMax pMin)) ∧
    (∀ (gMax pMin : Rat), (0 : Rat) < gMax → (0 : Rat) < pMin →
      (2198486384640 : Rat) ≤ gMax / pMin →
      (∀ S : Rat, (0 : Rat) < S → ¬fp16SubnormalSafe S gMax pMin) ∧
      (∀ k : Int, ¬fp16SubnormalSafe (pow2IntRat k) gMax pMin)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, by decide, by decide⟩
    unfold pow2Rat
    have h : (2 ^ 14 : Nat) = 16384 := by decide
    rw [h]
    grind
  · refine ⟨?_, by decide, by decide⟩
    unfold pow2Rat
    have h : (2 ^ 25 : Nat) = 33554432 := by decide
    rw [h]
    grind
  · intro gMax pMin hg hp hratio
    exact ⟨fun S hS => fp16_normal_window_empty hg hp hratio S hS,
      fun k => fp16_normal_window_empty hg hp hratio (pow2IntRat k) (pow2IntRat_pos k)⟩
  · intro gMax pMin hg hp hratio
    exact ⟨fun S hS => fp16_subnormal_window_empty hg hp hratio S hS,
      fun k => fp16_subnormal_window_empty hg hp hratio (pow2IntRat k) (pow2IntRat_pos k)⟩

/-! ### Theorem 5: LogSumExp Naive Swamping & Sequential Stall vs Pairwise Binary Tree -/

theorem naiveAccum_swamped (p : Nat) {t : Rat} (ht : t ≤ invPow2Rat p) (n : Nat) :
    naiveAccum p t n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [naiveAccum]
    rw [ih, Rat.one_mul]
    simp [ht]

theorem seqSplitAccum_before_stall (p : Nat) {t : Rat} (ht : (0 : Rat) < t) :
    ∀ n : Nat, n ≤ 2 ^ p → seqSplitAccum p t n = (n : Rat) * t := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [seqSplitAccum]
  | succ k ih =>
    intro hk
    have hklt : k < 2 ^ p := Nat.lt_of_succ_le hk
    have hprev : seqSplitAccum p t k = (k : Rat) * t := ih (Nat.le_of_lt hklt)
    simp only [seqSplitAccum]
    rw [hprev]
    have hnot : ¬((0 : Rat) < (k : Rat) * t ∧ t ≤ (k : Rat) * t * invPow2Rat p) := by
      intro ⟨_, hle⟩
      have hm := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt (pow2Rat_pos p))
      have heq : (k : Rat) * t * invPow2Rat p * pow2Rat p = (k : Rat) * t := by
        have h1 : (k : Rat) * t * invPow2Rat p * pow2Rat p =
            (k : Rat) * t * (invPow2Rat p * pow2Rat p) := by grind
        rw [h1, invPow2Rat_mul_pow2Rat p, Rat.mul_one]
      rw [heq] at hm
      have h1 : pow2Rat p * t ≤ (k : Rat) * t := by
        rw [Rat.mul_comm] at hm
        exact hm
      have h2 : pow2Rat p ≤ (k : Rat) := rat_le_of_mul_pos_right ht h1
      unfold pow2Rat at h2
      have hnat : 2 ^ p ≤ k := rat_natCast_le_iff.mp h2
      omega
    simp only [hnot, ite_false]
    rw [Rat.natCast_add]
    grind

theorem seqSplitAccum_stalled (p : Nat) {t : Rat} (ht : (0 : Rat) < t) :
    ∀ n : Nat, 2 ^ p ≤ n → seqSplitAccum p t n = pow2Rat p * t := by
  intro n
  induction n with
  | zero =>
    intro h
    have hp : 0 < 2 ^ p := Nat.pow_pos (by decide)
    omega
  | succ k ih =>
    intro hk
    by_cases hkeq : k < 2 ^ p
    · have hk1 : k + 1 = 2 ^ p := by omega
      rw [hk1]
      exact seqSplitAccum_before_stall p ht (2 ^ p) (Nat.le_refl _)
    · have hge : 2 ^ p ≤ k := by omega
      have hprev : seqSplitAccum p t k = pow2Rat p * t := ih hge
      simp only [seqSplitAccum]
      rw [hprev]
      have hcond : (0 : Rat) < pow2Rat p * t ∧ t ≤ pow2Rat p * t * invPow2Rat p := by
        refine ⟨rat_mul_pos (pow2Rat_pos p) ht, ?_⟩
        have heq : pow2Rat p * t * invPow2Rat p = t := by
          have h1 : pow2Rat p * t * invPow2Rat p = (pow2Rat p * invPow2Rat p) * t := by grind
          rw [h1, pow2Rat_mul_invPow2Rat p, Rat.one_mul]
        rw [heq]
        exact Rat.le_refl
      simp [hcond]

theorem treeSum_exact (k : Nat) (t : Rat) : treeSum k t = pow2Rat k * t := by
  induction k with
  | zero =>
    simp [treeSum, pow2Rat]
  | succ m ih =>
    simp only [treeSum]
    rw [ih, pow2Rat_succ]
    grind

theorem lse_naive_swamping_vs_pairwise_tree_exact :
    (invPow2Rat 8 = 1 / 256 ∧ invPow2Rat 11 = 1 / 2048 ∧ invPow2Rat 3 = 1 / 8) ∧
    (∀ (p n : Nat) (t : Rat), (0 : Rat) ≤ t → t ≤ invPow2Rat p →
      rneAddSwamps p 1 t ∧ naiveAccum p t n = 1) ∧
    (∀ (p n : Nat) (t : Rat), (0 : Rat) < t → (∃ j : Int, t = pow2IntRat j) →
      rneAddSwamps p (pow2Rat p * t) t ∧
      (n ≤ 2 ^ p → seqSplitAccum p t n = (n : Rat) * t) ∧
      (2 ^ p ≤ n →
        seqSplitAccum p t n = pow2Rat p * t ∧
        (n : Rat) * t - seqSplitAccum p t n = ((n - 2 ^ p : Nat) : Rat) * t)) ∧
    (∀ (k : Nat) (t : Rat), treeSum k t = pow2Rat k * t) ∧
    (∀ (p k : Nat) (t : Rat), p < k → (0 : Rat) < t → (∃ j : Int, t = pow2IntRat j) →
      seqSplitAccum p t (2 ^ k) < treeSum k t ∧
      treeSum k t / seqSplitAccum p t (2 ^ k) = pow2Rat (k - p)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold invPow2Rat pow2Rat
    have h8 : (2 ^ 8 : Nat) = 256 := by decide
    have h11 : (2 ^ 11 : Nat) = 2048 := by decide
    have h3 : (2 ^ 3 : Nat) = 8 := by decide
    rw [h8, h11, h3]
    grind
  · intro p n t ht0 htle
    refine ⟨⟨by decide, ht0, by rw [Rat.one_mul]; exact htle⟩, naiveAccum_swamped p htle n⟩
  · intro p n t ht _
    refine ⟨?_, seqSplitAccum_before_stall p ht n, ?_⟩
    · refine ⟨rat_mul_pos (pow2Rat_pos p) ht, Rat.le_of_lt ht, ?_⟩
      have heq : pow2Rat p * t * invPow2Rat p = t := by
        have h1 : pow2Rat p * t * invPow2Rat p = (pow2Rat p * invPow2Rat p) * t := by grind
        rw [h1, pow2Rat_mul_invPow2Rat p, Rat.one_mul]
      rw [heq]; exact Rat.le_refl
    · intro hge
      have hst := seqSplitAccum_stalled p ht n hge
      refine ⟨hst, ?_⟩
      rw [hst]
      have hn : n = (n - 2 ^ p) + 2 ^ p := (Nat.sub_add_cancel hge).symm
      have hcast : (n : Rat) = ((n - 2 ^ p : Nat) : Rat) + pow2Rat p := by
        have h1 : (n : Rat) = (((n - 2 ^ p) + 2 ^ p : Nat) : Rat) := congrArg (fun j : Nat => (j : Rat)) hn
        rw [h1, Rat.natCast_add]
        rfl
      rw [hcast]
      grind
  · exact treeSum_exact
  · intro p k t hpk ht _
    have hpowle : 2 ^ p ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hpk)
    have hpowlt : 2 ^ p < 2 ^ k := Nat.pow_lt_pow_right (by decide) hpk
    rw [seqSplitAccum_stalled p ht (2 ^ k) hpowle, treeSum_exact k t]
    refine ⟨rat_mul_lt_mul_of_pos_right (rat_natCast_lt hpowlt) ht, ?_⟩
    have hne : pow2Rat p * t ≠ 0 := Rat.ne_of_gt (rat_mul_pos (pow2Rat_pos p) ht)
    apply (rat_div_eq_iff hne).mpr
    have hadd : k = (k - p) + p := (Nat.sub_add_cancel (Nat.le_of_lt hpk)).symm
    have hp2 : pow2Rat k = pow2Rat ((k - p) + p) := congrArg pow2Rat hadd
    rw [hp2, pow2Rat_add]
    grind

/-! ### Theorem 6: Label Smoothing Total FP8 Erasure at Modern LLM Vocab Sizes -/

theorem label_smoothing_lt_e5m2_mid {ε : Rat} {V : Nat}
    (hεpos : (0 : Rat) < ε) (hεle : ε ≤ 1 / 8) (hV : 131072 ≤ V) :
    (0 : Rat) < labelSmoothOffTarget ε V ∧ labelSmoothOffTarget ε V < e5m2RneMid := by
  unfold labelSmoothOffTarget e5m2RneMid invPow2Rat pow2Rat
  have hVp : (0 : Rat) < (V : Rat) := rat_natCast_pos (by omega)
  refine ⟨rat_div_pos hεpos hVp, ?_⟩
  apply rat_div_lt_of_mul_lt hVp
  have h18lt1 : (1 / 8 : Rat) < 1 := by
    apply rat_div_lt_of_mul_lt (by decide)
    rw [Rat.one_mul]; decide
  have h1 : ε < (1 : Rat) := rat_lt_of_le_of_lt hεle h18lt1
  have h2 : ((131072 : Nat) : Rat) ≤ (V : Rat) := rat_natCast_le hV
  have h3 : (1 : Rat) ≤ (1 : Rat) / ((2 ^ 17 : Nat) : Rat) * (V : Rat) := by
    have h17 : (2 ^ 17 : Nat) = 131072 := by decide
    rw [h17]
    have hpos17 : (0 : Rat) ≤ (1 : Rat) / ((131072 : Nat) : Rat) :=
      Rat.le_of_lt (rat_div_pos (by decide) (rat_natCast_pos (by decide)))
    have hm := rat_mul_le_mul_of_nonneg_left h2 hpos17
    have heq : (1 : Rat) / ((131072 : Nat) : Rat) * ((131072 : Nat) : Rat) = 1 := by grind
    rw [heq] at hm
    exact hm
  exact rat_lt_of_lt_of_le h1 h3

theorem label_smoothing_fp8_total_erasure_exact :
    (∀ (ε : Rat) (V : Nat), (0 : Rat) < ε → ε ≤ 1 / 8 → 131072 ≤ V →
      (0 : Rat) < labelSmoothOffTarget ε V ∧
      labelSmoothOffTarget ε V < e5m2RneMid ∧
      subnormalQuantRNE e4m3MinSub (labelSmoothOffTarget ε V) = 0 ∧
      subnormalQuantRTZ e4m3MinSub (labelSmoothOffTarget ε V) = 0 ∧
      subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget ε V) = 0 ∧
      subnormalQuantRTZ e5m2MinSub (labelSmoothOffTarget ε V) = 0) ∧
    (subnormalQuantRNE e4m3MinSub (labelSmoothOffTarget (1 / 100) 131072) = 0 ∧
     subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget (1 / 100) 131072) = 0 ∧
     subnormalQuantRNE e4m3MinSub (labelSmoothOffTarget (1 / 20) 131072) = 0 ∧
     subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget (1 / 20) 131072) = 0 ∧
     subnormalQuantRNE e4m3MinSub (labelSmoothOffTarget (1 / 10) 131072) = 0 ∧
     subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget (1 / 10) 131072) = 0 ∧
     subnormalQuantRNE e4m3MinSub (labelSmoothOffTarget (1 / 10) 262144) = 0 ∧
     subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget (1 / 10) 262144) = 0) := by
  have hall : ∀ (ε : Rat) (V : Nat), (0 : Rat) < ε → ε ≤ 1 / 8 → 131072 ≤ V →
      (0 : Rat) < labelSmoothOffTarget ε V ∧
      labelSmoothOffTarget ε V < e5m2RneMid ∧
      subnormalQuantRNE e4m3MinSub (labelSmoothOffTarget ε V) = 0 ∧
      subnormalQuantRTZ e4m3MinSub (labelSmoothOffTarget ε V) = 0 ∧
      subnormalQuantRNE e5m2MinSub (labelSmoothOffTarget ε V) = 0 ∧
      subnormalQuantRTZ e5m2MinSub (labelSmoothOffTarget ε V) = 0 := by
    intro ε V hεpos hεle hV
    have ⟨hpos, hlt⟩ := label_smoothing_lt_e5m2_mid hεpos hεle hV
    have h9 : (2 ^ 9 : Nat) = 512 := by decide
    have h16 : (2 ^ 16 : Nat) = 65536 := by decide
    have h17 : (2 ^ 17 : Nat) = 131072 := by decide
    have h1 : e5m2RneMid ≤ e4m3MinSub / 2 := by
      unfold e5m2RneMid e4m3MinSub invPow2Rat pow2Rat
      rw [h9, h17]
      have hle : (1 : Rat) / ((131072 : Nat) : Rat) ≤ (1 : Rat) / ((1024 : Nat) : Rat) :=
        (inv_nat_le_inv_nat_iff (by decide) (by decide)).mpr (by decide)
      have heq : (1 : Rat) / ((512 : Nat) : Rat) / 2 = (1 : Rat) / ((1024 : Nat) : Rat) := by grind
      rw [heq]; exact hle
    have h2 : e5m2RneMid ≤ e4m3MinSub := by
      unfold e5m2RneMid e4m3MinSub invPow2Rat pow2Rat
      rw [h9, h17]
      exact (inv_nat_le_inv_nat_iff (by decide) (by decide)).mpr (by decide)
    have h3 : e5m2RneMid = e5m2MinSub / 2 := by
      unfold e5m2RneMid e5m2MinSub invPow2Rat pow2Rat
      rw [h16, h17]; grind
    have h4 : e5m2RneMid ≤ e5m2MinSub := by
      unfold e5m2RneMid e5m2MinSub invPow2Rat pow2Rat
      rw [h16, h17]
      exact (inv_nat_le_inv_nat_iff (by decide) (by decide)).mpr (by decide)
    refine ⟨hpos, hlt, ?_, ?_, ?_, ?_⟩
    · unfold subnormalQuantRNE
      have hle : labelSmoothOffTarget ε V ≤ e4m3MinSub / 2 :=
        Rat.le_trans (Rat.le_of_lt hlt) h1
      simp [hle]
    · unfold subnormalQuantRTZ
      have hlt2 : labelSmoothOffTarget ε V < e4m3MinSub := rat_lt_of_lt_of_le hlt h2
      simp [hlt2]
    · unfold subnormalQuantRNE
      have hle : labelSmoothOffTarget ε V ≤ e5m2MinSub / 2 := by
        rw [← h3]; exact Rat.le_of_lt hlt
      simp [hle]
    · unfold subnormalQuantRTZ
      have hlt2 : labelSmoothOffTarget ε V < e5m2MinSub := rat_lt_of_lt_of_le hlt h4
      simp [hlt2]
  have h100p : (0 : Rat) < 1 / 100 := rat_div_pos (by decide) (by decide)
  have h100le : (1 / 100 : Rat) ≤ 1 / 8 := (inv_nat_le_inv_nat_iff (by decide) (by decide)).mpr (by decide)
  have h20p : (0 : Rat) < 1 / 20 := rat_div_pos (by decide) (by decide)
  have h20le : (1 / 20 : Rat) ≤ 1 / 8 := (inv_nat_le_inv_nat_iff (by decide) (by decide)).mpr (by decide)
  have h10p : (0 : Rat) < 1 / 10 := rat_div_pos (by decide) (by decide)
  have h10le : (1 / 10 : Rat) ≤ 1 / 8 := (inv_nat_le_inv_nat_iff (by decide) (by decide)).mpr (by decide)
  refine ⟨hall, ?_⟩
  refine ⟨
    (hall (1 / 100) 131072 h100p h100le (by omega)).2.2.1,
    (hall (1 / 100) 131072 h100p h100le (by omega)).2.2.2.2.1,
    (hall (1 / 20) 131072 h20p h20le (by omega)).2.2.1,
    (hall (1 / 20) 131072 h20p h20le (by omega)).2.2.2.2.1,
    (hall (1 / 10) 131072 h10p h10le (by omega)).2.2.1,
    (hall (1 / 10) 131072 h10p h10le (by omega)).2.2.2.2.1,
    (hall (1 / 10) 262144 h10p h10le (by omega)).2.2.1,
    (hall (1 / 10) 262144 h10p h10le (by omega)).2.2.2.2.1⟩

end CeLseHorizon
