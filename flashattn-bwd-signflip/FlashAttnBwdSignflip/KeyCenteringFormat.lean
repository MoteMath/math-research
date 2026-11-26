/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FlashAttnBwdSignflip.RatOrder

/-!
# Theorems 5 & 6: Key-Centering `dQ = dS (K - 1 K_bar^T)` Invariance &
# Unsigned 4-Bit `U-E3M1` vs Signed `MXFP4-E2M1` 16× Dynamic-Range Law

Pure `Init` (zero Mathlib, zero `native_decide`) proofs.
-/

namespace FlashAttnBwdSignflip

/-! ### Theorem 5 Helpers -/

theorem dqEntry_sub_centered {n d : Nat} (dS : Fin n → Rat) (K : Fin n → Fin d → Rat)
    (kBar : Fin d → Rat) (c : Fin d) :
    dqEntry dS K c - dqEntry dS (centeredKey K kBar) c = finSum dS * kBar c := by
  unfold dqEntry centeredKey
  have hlin : finSum (fun j => dS j * (K j c - kBar c)) =
      finSum (fun j => dS j * K j c - dS j * kBar c) := by
    apply finSum_congr
    intro j; grind
  rw [hlin, finSum_sub, finSum_mul_right]
  grind

theorem l2NormSq_add_orth {d : Nat} (u v : Fin d → Rat) (horth : dotProd u v = 0) :
    l2NormSq (fun c => u c + v c) = l2NormSq u + l2NormSq v := by
  unfold l2NormSq
  have hlin : finSum (fun c => (u c + v c) * (u c + v c)) =
      finSum (fun c => (u c * u c + v c * v c) + 2 * (u c * v c)) := by
    apply finSum_congr
    intro c; grind
  rw [hlin, finSum_add, finSum_add, finSum_mul_left]
  change l2NormSq u + l2NormSq v + 2 * dotProd u v = l2NormSq u + l2NormSq v
  rw [horth]
  grind

theorem l2NormSq_scale {d : Nat} (a : Rat) (v : Fin d → Rat) :
    l2NormSq (fun c => a * v c) = (a * a) * l2NormSq v := by
  unfold l2NormSq
  have hlin : finSum (fun c => (a * v c) * (a * v c)) =
      finSum (fun c => (a * a) * (v c * v c)) := by
    apply finSum_congr
    intro c; grind
  rw [hlin, finSum_mul_left]

theorem dotProd_scale_right {d : Nat} (u v : Fin d → Rat) (a : Rat) :
    dotProd u (fun c => a * v c) = a * dotProd u v := by
  unfold dotProd
  have hlin : finSum (fun c => u c * (a * v c)) = finSum (fun c => a * (u c * v c)) := by
    apply finSum_congr
    intro c; grind
  rw [hlin, finSum_mul_left]

theorem dotProd_add_right {d : Nat} (u v w : Fin d → Rat) :
    dotProd u (fun c => v c + w c) = dotProd u v + dotProd u w := by
  unfold dotProd
  have hlin : finSum (fun c => u c * (v c + w c)) = finSum (fun c => u c * v c + u c * w c) := by
    apply finSum_congr
    intro c; grind
  rw [hlin, finSum_add]

/-- **Theorem 5** (`key_centering_dq_invariance_exact`):
    Universal exact algebraic theorem for `dQ = dS K` and key-centering `K ↦ K - 1 K_bar^T`:
    1. Exact decomposition: `(dS K)_c - (dS (K - 1 K_bar^T))_c = (∑_j dS_j) * K_bar_c`.
    2. Zero-bias invariance: whenever `∑_j dS_j = 0`, `dS (K - 1 K_bar^T) = dS K` identically.
    3. Exact bias elimination under drift `∑_j dSHat_j = δ_S`: centering `K = K_0 + 1 K_bar^T`
       recovers `dSHat K_0` exactly while uncentered `dSHat K = dSHat K_0 + δ_S K_bar^T`.
    4. Exact squared cosine-similarity collapse law: for orthogonal bias `⟨dQ_0, K_bar⟩ = 0`,
       `cos^2(dQ_0, dQ_0 + δ_S K_bar) = ||dQ_0||_2^2 / (||dQ_0||_2^2 + δ_S^2 ||K_bar||_2^2)`,
       which collapses strictly below any `ε > 0` for large key shift `s K_bar`. -/
theorem key_centering_dq_invariance_exact :
    (∀ (n d : Nat) (dS : Fin n → Rat) (K : Fin n → Fin d → Rat) (kBar : Fin d → Rat) (c : Fin d),
      dqEntry dS K c - dqEntry dS (centeredKey K kBar) c = finSum dS * kBar c) ∧
    (∀ (n d : Nat) (dS : Fin n → Rat) (K : Fin n → Fin d → Rat) (kBar : Fin d → Rat) (c : Fin d),
      finSum dS = 0 → dqEntry dS (centeredKey K kBar) c = dqEntry dS K c) ∧
    (∀ (n d : Nat) (dSHat : Fin n → Rat) (K0 : Fin n → Fin d → Rat) (kBar : Fin d → Rat) (δS : Rat),
      finSum dSHat = δS →
      let K : Fin n → Fin d → Rat := fun j c => K0 j c + kBar c
      (∀ c : Fin d, dqEntry dSHat (centeredKey K kBar) c = dqEntry dSHat K0 c) ∧
      (∀ c : Fin d, dqEntry dSHat K c = dqEntry dSHat K0 c + δS * kBar c)) ∧
    (∀ (d : Nat) (dQ0 kBar : Fin d → Rat) (δS : Rat),
      dotProd dQ0 kBar = 0 →
      0 < l2NormSq dQ0 →
      δS ≠ 0 →
      0 < l2NormSq kBar →
      let dQ_biased : Fin d → Rat := fun c => dQ0 c + δS * kBar c
      dotProd dQ0 dQ_biased = l2NormSq dQ0 ∧
      l2NormSq dQ_biased = l2NormSq dQ0 + (δS * δS) * l2NormSq kBar ∧
      (dotProd dQ0 dQ_biased * dotProd dQ0 dQ_biased) / (l2NormSq dQ0 * l2NormSq dQ_biased) =
        l2NormSq dQ0 / (l2NormSq dQ0 + (δS * δS) * l2NormSq kBar) ∧
      (∀ (ε s : Rat), 0 < ε →
        l2NormSq dQ0 < ε * ((δS * δS) * (s * s) * l2NormSq kBar) →
        let dQ_s : Fin d → Rat := fun c => dQ0 c + δS * (s * kBar c)
        (dotProd dQ0 dQ_s * dotProd dQ0 dQ_s) / (l2NormSq dQ0 * l2NormSq dQ_s) < ε)) := by
  refine ⟨fun _ _ => dqEntry_sub_centered, ?_, ?_, ?_⟩
  · intro n d dS K kBar c hzero
    have h := dqEntry_sub_centered dS K kBar c
    rw [hzero] at h
    grind
  · intro n d dSHat K0 kBar δS hdrift
    dsimp only
    have hcenter : ∀ c : Fin d,
        dqEntry dSHat (centeredKey (fun j c => K0 j c + kBar c) kBar) c = dqEntry dSHat K0 c := by
      intro c
      unfold dqEntry centeredKey
      apply finSum_congr
      intro j; grind
    refine ⟨hcenter, ?_⟩
    intro c
    have hsub := dqEntry_sub_centered dSHat (fun j c => K0 j c + kBar c) kBar c
    rw [hcenter c, hdrift] at hsub
    grind
  · intro d dQ0 kBar δS horth hQpos hδne hKpos
    dsimp only
    have hdot : dotProd dQ0 (fun c => dQ0 c + δS * kBar c) = l2NormSq dQ0 := by
      rw [dotProd_add_right, dotProd_scale_right, horth]
      unfold dotProd l2NormSq
      grind
    have horthScaled : dotProd dQ0 (fun c => δS * kBar c) = 0 := by
      rw [dotProd_scale_right, horth]; grind
    have hl2 : l2NormSq (fun c => dQ0 c + δS * kBar c) =
        l2NormSq dQ0 + (δS * δS) * l2NormSq kBar := by
      rw [l2NormSq_add_orth dQ0 (fun c => δS * kBar c) horthScaled, l2NormSq_scale]
    have hdenPos : (0 : Rat) < l2NormSq dQ0 + (δS * δS) * l2NormSq kBar :=
      rat_add_pos hQpos (rat_mul_pos (rat_sq_pos_of_ne_zero hδne) hKpos)
    have hcos :
        (dotProd dQ0 (fun c => dQ0 c + δS * kBar c) *
          dotProd dQ0 (fun c => dQ0 c + δS * kBar c)) /
        (l2NormSq dQ0 * l2NormSq (fun c => dQ0 c + δS * kBar c)) =
        l2NormSq dQ0 / (l2NormSq dQ0 + (δS * δS) * l2NormSq kBar) := by
      rw [hdot, hl2]
      have hQne : l2NormSq dQ0 ≠ 0 := Rat.ne_of_gt hQpos
      have hDne : l2NormSq dQ0 + (δS * δS) * l2NormSq kBar ≠ 0 := Rat.ne_of_gt hdenPos
      have hPne : l2NormSq dQ0 * (l2NormSq dQ0 + (δS * δS) * l2NormSq kBar) ≠ 0 :=
        Rat.ne_of_gt (rat_mul_pos hQpos hdenPos)
      apply (rat_div_eq_iff hPne).mpr
      have hrearr :
          l2NormSq dQ0 / (l2NormSq dQ0 + (δS * δS) * l2NormSq kBar) *
            (l2NormSq dQ0 * (l2NormSq dQ0 + (δS * δS) * l2NormSq kBar)) =
          l2NormSq dQ0 *
            ((l2NormSq dQ0 / (l2NormSq dQ0 + (δS * δS) * l2NormSq kBar)) *
              (l2NormSq dQ0 + (δS * δS) * l2NormSq kBar)) := by grind
      rw [hrearr, rat_div_mul_cancel hDne]
    refine ⟨hdot, hl2, hcos, ?_⟩
    intro ε s hε hbig
    have horthS : dotProd dQ0 (fun c => δS * (s * kBar c)) = 0 := by
      rw [dotProd_scale_right, dotProd_scale_right, horth]; grind
    have hdotS : dotProd dQ0 (fun c => dQ0 c + δS * (s * kBar c)) = l2NormSq dQ0 := by
      rw [dotProd_add_right, horthS]
      unfold dotProd l2NormSq
      grind
    have hl2S : l2NormSq (fun c => dQ0 c + δS * (s * kBar c)) =
        l2NormSq dQ0 + (δS * δS) * (s * s) * l2NormSq kBar := by
      rw [l2NormSq_add_orth dQ0 (fun c => δS * (s * kBar c)) horthS,
          l2NormSq_scale, l2NormSq_scale]
      grind
    rw [hdotS, hl2S]
    have htermNN : (0 : Rat) ≤ (δS * δS) * (s * s) * l2NormSq kBar :=
      Rat.mul_nonneg (Rat.mul_nonneg (rat_sq_nonneg δS) (rat_sq_nonneg s)) (Rat.le_of_lt hKpos)
    have hdenSPos : (0 : Rat) < l2NormSq dQ0 + (δS * δS) * (s * s) * l2NormSq kBar :=
      rat_add_pos_of_pos_of_nonneg hQpos htermNN
    have hprodPos : (0 : Rat) < l2NormSq dQ0 * (l2NormSq dQ0 + (δS * δS) * (s * s) * l2NormSq kBar) :=
      rat_mul_pos hQpos hdenSPos
    apply rat_div_lt_of_mul_lt hprodPos
    have hlt1 : l2NormSq dQ0 < ε * (l2NormSq dQ0 + (δS * δS) * (s * s) * l2NormSq kBar) := by
      have haddPos : (0 : Rat) < ε * l2NormSq dQ0 := rat_mul_pos hε hQpos
      have hle : ε * ((δS * δS) * (s * s) * l2NormSq kBar) <
          ε * (l2NormSq dQ0 + (δS * δS) * (s * s) * l2NormSq kBar) := by
        apply rat_lt_of_sub_pos
        have hsub : ε * (l2NormSq dQ0 + (δS * δS) * (s * s) * l2NormSq kBar) -
            ε * ((δS * δS) * (s * s) * l2NormSq kBar) = ε * l2NormSq dQ0 := by grind
        rw [hsub]; exact haddPos
      exact rat_lt_trans hbig hle
    have hmul := rat_mul_lt_mul_of_pos_left hlt1 hQpos
    have hrhs : l2NormSq dQ0 * (ε * (l2NormSq dQ0 + (δS * δS) * (s * s) * l2NormSq kBar)) =
        ε * (l2NormSq dQ0 * (l2NormSq dQ0 + (δS * δS) * (s * s) * l2NormSq kBar)) := by grind
    rw [hrhs] at hmul
    exact hmul

/-! ### Theorem 6 Helpers -/

theorem rat_div_eq_of_mul_rat {a b c : Rat} (hb : b ≠ 0) (h : a = c * b) : a / b = c :=
  (rat_div_eq_iff hb).mpr h

/-- **Theorem 6** (`unsigned_ue3m1_vs_mxfp4_dynamic_range_16x_exact`):
    Exact bit-level theorem proving:
    1. Unsigned 4-bit `U-E3M1` and signed 4-bit `MXFP4-E2M1` have identical 4-bit width
       and identical 1-bit mantissa precision (`u = 1/4`).
    2. `U-E3M1` achieves an exact **`16×` wider dynamic range** than `MXFP4-E2M1` on both
       full (`192 / 12 = 16`) and normal (`96 / 6 = 16`) spans.
    3. On nonnegative probabilities `P ∈ [0, 1]`, `U-E3M1` lowers the subnormal floor by
       an exact **`16×`** (`1/128` vs `1/8` for block-scaled `MXFP4`), keeping tail weights
       such as `p = 2^{-5} = 1/32` strictly representable where `MXFP4_PROB` flushes them to `0`.
    4. Companion 8-bit `FP8-E5M2` vs `FP8-E4M3` exact ratios (`16384×` full DR, `32768×` normal DR,
       `2×` unit-roundoff cost) and the universal sign-bit-to-exponent reallocation law
       `2 ^ (2 ^ (e_s + 1) - 2 ^ e_s) = 2 ^ (2 ^ e_s)`. -/
theorem unsigned_ue3m1_vs_mxfp4_dynamic_range_16x_exact :
    (fmtUE3M1.totalBits = 4 ∧ fmtMXFP4.totalBits = 4 ∧ fmtMXFP4Prob.totalBits = 4 ∧
     fmtUE3M1.mbits = 1 ∧ fmtMXFP4.mbits = 1 ∧
     fmtUE3M1.unitRoundoff = 1 / 4 ∧ fmtMXFP4.unitRoundoff = 1 / 4) ∧
    (fmtUE3M1.dynRangeFull = 192 ∧ fmtMXFP4.dynRangeFull = 12 ∧
     fmtUE3M1.dynRangeFull / fmtMXFP4.dynRangeFull = 16 ∧
     fmtUE3M1.dynRangeNormal = 96 ∧ fmtMXFP4.dynRangeNormal = 6 ∧
     fmtUE3M1.dynRangeNormal / fmtMXFP4.dynRangeNormal = 16) ∧
    (fmtMXFP4Prob.minSubnormal / fmtUE3M1.minSubnormal = 16 ∧
     (∀ p : Rat, fmtUE3M1.minSubnormal ≤ p → p < fmtMXFP4Prob.minSubnormal / 2 →
       (1 / 128 : Rat) ≤ p ∧ p < (1 / 16 : Rat)) ∧
     (fmtUE3M1.minSubnormal ≤ (1 / 32 : Rat) ∧ (1 / 32 : Rat) < fmtMXFP4Prob.minSubnormal / 2)) ∧
    (fmtE5M2.totalBits = 8 ∧ fmtE4M3.totalBits = 8 ∧
     fmtE5M2.dynRangeFull = 3758096384 ∧ fmtE4M3.dynRangeFull = 229376 ∧
     fmtE5M2.dynRangeFull / fmtE4M3.dynRangeFull = 16384 ∧
     fmtE5M2.dynRangeNormal = 939524096 ∧ fmtE4M3.dynRangeNormal = 28672 ∧
     fmtE5M2.dynRangeNormal / fmtE4M3.dynRangeNormal = 32768 ∧
     fmtE5M2.unitRoundoff / fmtE4M3.unitRoundoff = 2) ∧
    ((∀ e_s : Nat, 2 ^ (2 ^ (e_s + 1) - 2 ^ e_s) = 2 ^ (2 ^ e_s)) ∧
     2 ^ (2 ^ 2) = 16) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hUF : fmtUE3M1.dynRangeFull = 192 := by
      unfold FloatFormatSpec.dynRangeFull fmtUE3M1
      apply rat_div_eq_of_mul_rat (Rat.ne_of_gt (rat_div_pos (by decide) (by decide)))
      grind
    have hMF : fmtMXFP4.dynRangeFull = 12 := by
      unfold FloatFormatSpec.dynRangeFull fmtMXFP4
      apply rat_div_eq_of_mul_rat (Rat.ne_of_gt (rat_div_pos (by decide) (by decide)))
      grind
    have hUN : fmtUE3M1.dynRangeNormal = 96 := by
      unfold FloatFormatSpec.dynRangeNormal fmtUE3M1
      apply rat_div_eq_of_mul_rat (Rat.ne_of_gt (rat_div_pos (by decide) (by decide)))
      grind
    have hMN : fmtMXFP4.dynRangeNormal = 6 := by
      unfold FloatFormatSpec.dynRangeNormal fmtMXFP4
      apply rat_div_eq_of_mul_rat (by decide)
      grind
    refine ⟨hUF, hMF, ?_, hUN, hMN, ?_⟩
    · rw [hUF, hMF]
      apply rat_div_eq_of_mul_rat (by decide)
      grind
    · rw [hUN, hMN]
      apply rat_div_eq_of_mul_rat (by decide)
      grind
  · have hsubRatio : fmtMXFP4Prob.minSubnormal / fmtUE3M1.minSubnormal = 16 := by
      unfold fmtMXFP4Prob fmtUE3M1
      apply rat_div_eq_of_mul_rat (Rat.ne_of_gt (rat_div_pos (by decide) (by decide)))
      grind
    have hhalf : fmtMXFP4Prob.minSubnormal / 2 = (1 / 16 : Rat) := by
      unfold fmtMXFP4Prob
      apply rat_div_eq_of_mul_rat (by decide)
      grind
    refine ⟨hsubRatio, ?_, ?_⟩
    · intro p h1 h2
      rw [hhalf] at h2
      exact ⟨h1, h2⟩
    · rw [hhalf]
      unfold fmtUE3M1
      refine ⟨?_, ?_⟩
      · apply rat_le_of_mul_pos_right (c := (128 : Rat)) (by decide)
        have hl : (1 / 128 : Rat) * 128 = 1 := rat_div_mul_cancel (by decide)
        have hr : (1 / 32 : Rat) * 128 = 4 := by
          have : (1 / 32 : Rat) * 128 = ((1 / 32 : Rat) * 32) * 4 := by grind
          rw [this, rat_div_mul_cancel (by decide)]; grind
        rw [hl, hr]; decide
      · apply rat_lt_of_mul_pos_right (c := (32 : Rat)) (by decide)
        have hl : (1 / 32 : Rat) * 32 = 1 := rat_div_mul_cancel (by decide)
        have hr : (1 / 16 : Rat) * 32 = 2 := by
          have : (1 / 16 : Rat) * 32 = ((1 / 16 : Rat) * 16) * 2 := by grind
          rw [this, rat_div_mul_cancel (by decide)]; grind
        rw [hl, hr]; decide
  · have h5F : fmtE5M2.dynRangeFull = 3758096384 := by
      unfold FloatFormatSpec.dynRangeFull fmtE5M2
      apply rat_div_eq_of_mul_rat (Rat.ne_of_gt (rat_div_pos (by decide) (by decide)))
      grind
    have h4F : fmtE4M3.dynRangeFull = 229376 := by
      unfold FloatFormatSpec.dynRangeFull fmtE4M3
      apply rat_div_eq_of_mul_rat (Rat.ne_of_gt (rat_div_pos (by decide) (by decide)))
      grind
    have h5N : fmtE5M2.dynRangeNormal = 939524096 := by
      unfold FloatFormatSpec.dynRangeNormal fmtE5M2
      apply rat_div_eq_of_mul_rat (Rat.ne_of_gt (rat_div_pos (by decide) (by decide)))
      grind
    have h4N : fmtE4M3.dynRangeNormal = 28672 := by
      unfold FloatFormatSpec.dynRangeNormal fmtE4M3
      apply rat_div_eq_of_mul_rat (Rat.ne_of_gt (rat_div_pos (by decide) (by decide)))
      grind
    refine ⟨rfl, rfl, h5F, h4F, ?_, h5N, h4N, ?_, ?_⟩
    · rw [h5F, h4F]
      apply rat_div_eq_of_mul_rat (by decide)
      grind
    · rw [h5N, h4N]
      apply rat_div_eq_of_mul_rat (by decide)
      grind
    · unfold fmtE5M2 fmtE4M3
      apply rat_div_eq_of_mul_rat (Rat.ne_of_gt (rat_div_pos (by decide) (by decide)))
      grind
  · refine ⟨?_, rfl⟩
    intro e_s
    have hsub : 2 ^ (e_s + 1) - 2 ^ e_s = 2 ^ e_s := by
      rw [Nat.pow_succ]
      omega
    rw [hsub]

end FlashAttnBwdSignflip
