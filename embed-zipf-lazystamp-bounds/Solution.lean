/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EmbedZipfLazyStamp

/-!
# Verified Solutions (`embed-zipf-lazystamp-bounds`)
-/

namespace EmbedZipfLazyStampChallenge

open EmbedZipfLazyStamp

theorem tied_embedding_dense_pushdown_zero_sum_and_asymmetry :
    (∀ (V d : Nat) (p : Fin V → Rat) (y : Fin V) (h : Fin d → Rat),
      finSum p = 1 → ∀ j : Fin d, finSum (fun v : Fin V => gOutDense p y h v j) = 0) ∧
    (∀ (B V d : Nat) (pB : Fin B → Fin V → Rat) (yB : Fin B → Fin V) (hB : Fin B → Fin d → Rat),
      (∀ b : Fin B, finSum (pB b) = 1) →
      ∀ j : Fin d, finSum (fun v : Fin V => gOutBatch pB yB hB v j) = 0) ∧
    (∀ (V d : Nat) (p : Fin V → Rat) (y : Fin V) (h g_x : Fin d → Rat) (v : Fin V),
      v ≠ y → ∀ j : Fin d,
        gInSparse y g_x v j = 0 ∧
        gOutDense p y h v j = p v * h j ∧
        gOutDense p y h y j = -(1 - p y) * h j) ∧
    (∀ (V d : Nat) (p : Fin V → Rat) (y : Fin V) (h : Fin d → Rat) (v : Fin V) (j : Fin d),
      v ≠ y → (0 : Rat) < p v → (0 : Rat) < p y → p y < 1 → h j ≠ 0 →
        ratAbs (gOutDense p y h v j) / ratAbs (gOutDense p y h y j) = p v / (1 - p y) ∧
        ratAbs (gOutDense p y h v j) / ratAbs (p y * h j) = (1 / p y) * p v ∧
        ratAbs (gOutDense p y h v j) / ratAbs (gOutDense p y h y j) =
          ((1 / p y) * p v) * (p y / (1 - p y))) :=
  EmbedZipfLazyStamp.tied_embedding_dense_pushdown_zero_sum_and_asymmetry

theorem rare_token_rne_weight_flush_and_fp8_subnormal_underflow :
    (∀ (e_w : Int) (M : Nat) (q : Int) (dw : Rat),
      ratAbs dw < halfUlpBinade e_w M →
      rneGrid (ulpBinade e_w M) ((q : Rat) * ulpBinade e_w M + dw) -
        (q : Rat) * ulpBinade e_w M = 0) ∧
    (∀ (e_w : Int) (M : Nat) (q : Int) (dw : Rat),
      halfUlpBinade e_w M < dw → dw < ulpBinade e_w M →
      rneGrid (ulpBinade e_w M) ((q : Rat) * ulpBinade e_w M + dw) -
        (q : Rat) * ulpBinade e_w M = ulpBinade e_w M) ∧
    (fp8E4M3MinSubnormal = 1 / 512 ∧ fp8E4M3HalfSubnormal = 1 / 1024 ∧
     (∀ g : Rat, ratAbs g ≤ fp8E4M3HalfSubnormal → rneGrid fp8E4M3MinSubnormal g = 0)) ∧
    (fp8E5M2MinSubnormal = 1 / 65536 ∧ fp8E5M2HalfSubnormal = 1 / 131072 ∧
     (∀ g : Rat, ratAbs g ≤ fp8E5M2HalfSubnormal → rneGrid fp8E5M2MinSubnormal g = 0)) ∧
    (halfUlpBinade (-5) 7 = 1 / 8192 ∧
     halfUlpBinade (-5) 10 = 1 / 65536 ∧
     halfUlpBinade (-5) 2 = 1 / 256 ∧
     halfUlpBinade (-5) 3 = 1 / 512) ∧
    (∀ (e_w : Int) (M : Nat) (q : Int) (Z η H p_r h : Rat) (r : Nat),
      (0 : Rat) < Z → (0 : Rat) < η → 0 < r →
      (0 : Rat) ≤ p_r → p_r ≤ 1 / (Z * (r : Rat)) → ratAbs h ≤ H →
      (η * H) / (Z * halfUlpBinade e_w M) < (r : Rat) →
      rneGrid (ulpBinade e_w M) ((q : Rat) * ulpBinade e_w M + η * p_r * h) -
        (q : Rat) * ulpBinade e_w M = 0) ∧
    (∀ (Z H p_r h : Rat) (r : Nat),
      (0 : Rat) < Z → 0 < r → (0 : Rat) ≤ p_r → p_r ≤ 1 / (Z * (r : Rat)) → ratAbs h ≤ H →
      (H / (Z * fp8E4M3HalfSubnormal) ≤ (r : Rat) → rneGrid fp8E4M3MinSubnormal (p_r * h) = 0) ∧
      (H / (Z * fp8E5M2HalfSubnormal) ≤ (r : Rat) → rneGrid fp8E5M2MinSubnormal (p_r * h) = 0)) :=
  EmbedZipfLazyStamp.rare_token_rne_weight_flush_and_fp8_subnormal_underflow

theorem bf16_sparse_adamw_v_decay_freeze_exact :
    (∀ (p : Nat) (e : Int) (m : Nat) (β : Rat),
      m < 2 ^ p → (0 : Rat) ≤ 1 - β → 1 - β ≤ pow2Int (-((p + 2 : Nat) : Int)) →
      rneFloatBelow p e m (β * normalFloat p e m) = normalFloat p e m ∧
      ∀ K : Nat, iterFloatDecay p e m β K (normalFloat p e m) = normalFloat p e m) ∧
    (pow2Int (-((7 + 2 : Nat) : Int)) = 1 / 512 ∧
     (1 : Rat) - (999 / 1000 : Rat) = 1 / 1000 ∧
     (1 / 1000 : Rat) < 1 / 512 ∧
     (1 : Rat) - (9999 / 10000 : Rat) = 1 / 10000 ∧
     (1 / 10000 : Rat) < 1 / 512) ∧
    (∀ (e : Int) (m : Nat), m < 128 →
      rneFloatBelow 7 e m ((999 / 1000 : Rat) * normalFloat 7 e m) = normalFloat 7 e m ∧
      (∀ K : Nat, iterFloatDecay 7 e m (999 / 1000 : Rat) K (normalFloat 7 e m) = normalFloat 7 e m) ∧
      rneFloatBelow 7 e m ((9999 / 10000 : Rat) * normalFloat 7 e m) = normalFloat 7 e m) ∧
    (∀ (p : Nat) (e : Int) (β : Rat),
      pow2Int (-((p + 2 : Nat) : Int)) < 1 - β → 1 - β < pow2Int (-((p + 1 : Nat) : Int)) →
      rneFloatBelow p e 0 (β * normalFloat p e 0) ≠ normalFloat p e 0) :=
  EmbedZipfLazyStamp.bf16_sparse_adamw_v_decay_freeze_exact

theorem lazy_stamp_adamw_exact_equivalence_to_dense_updates :
    (∀ (β1 β2 η lam : Rat) (Δ : Nat) (s : AdamWState),
      denseAbsentSteps β1 β2 η lam Δ s = lazyStampJump β1 β2 η lam Δ s) ∧
    (∀ (β1 β2 η lam : Rat) (Δ : Nat) (s : AdamWState),
      lazyStampJumpFast β1 β2 η lam Δ s = denseAbsentSteps β1 β2 η lam Δ s) ∧
    (∀ (β1 β2 η lam : Rat) (Δ1 Δ2 : Nat) (s : AdamWState),
      lazyStampJump β1 β2 η lam Δ2 (lazyStampJump β1 β2 η lam Δ1 s) =
        lazyStampJump β1 β2 η lam (Δ1 + Δ2) s) ∧
    (∀ (e : Int) (m : Nat), m < 128 →
      rneFloatBelow 7 e m (ratPow (999 / 1000 : Rat) 4 * normalFloat 7 e m) ≠
        normalFloat 7 e m) :=
  EmbedZipfLazyStamp.lazy_stamp_adamw_exact_equivalence_to_dense_updates

theorem lazy_stamp_bandwidth_and_work_speedup_exact :
    (∀ (V U d bRow fRow T : Nat), 0 < U → 0 < d → 0 < bRow → 0 < fRow → 0 < T →
      (denseBytes V d bRow : Rat) / (lazyBytes U d bRow : Rat) = (V : Rat) / (U : Rat) ∧
      (denseFlops V d fRow : Rat) / (lazyFlops U d fRow : Rat) = (V : Rat) / (U : Rat) ∧
      ((T * denseBytes V d bRow : Nat) : Rat) / ((T * lazyBytes U d bRow : Nat) : Rat) =
        (V : Rat) / (U : Rat)) ∧
    (∀ (V U d bRow : Nat), 0 < V → 0 < d → 0 < bRow → U ≤ V →
      ((denseBytes V d bRow - lazyBytes U d bRow : Nat) : Rat) / (denseBytes V d bRow : Rat) =
        1 - (U : Rat) / (V : Rat)) ∧
    ((denseBytes 131072 4096 12 = 6442450944) ∧
     (lazyBytes 4096 4096 12 = 201326592) ∧
     ((131072 : Rat) / 4096 = 32) ∧
     ((1 : Rat) - (4096 : Rat) / 131072 = 31 / 32)) ∧
    (∀ U : Nat, 0 < U → U ≤ 5242 → (25 : Rat) ≤ (131072 : Rat) / (U : Rat)) :=
  EmbedZipfLazyStamp.lazy_stamp_bandwidth_and_work_speedup_exact

theorem zipf_mixed_precision_embedding_allocation_pareto :
    (∀ (V : Nat) (a b : Fin V → Rat),
      finSum (fun r => a r * b r) * finSum (fun r => a r * b r) ≤
        finSum (fun r => a r * a r) * finSum (fun r => b r * b r)) ∧
    (∀ (p_r p_s c : Rat) (b_r b_s b_r' b_s' : Int),
      (0 : Rat) < p_r → (0 : Rat) < p_s → (0 : Rat) < c →
      b_r' + b_s' = b_r + b_s →
      pow4Int (b_r - b_s) = p_r / p_s →
      p_r * c * pow4Int (-b_r) + p_s * c * pow4Int (-b_s) ≤
        p_r * c * pow4Int (-b_r') + p_s * c * pow4Int (-b_s')) ∧
    (∀ (V : Nat) (p : Fin V → Rat) (c : Rat) (bStar b : Fin V → Int),
      0 < V → (∀ r, (0 : Rat) < p r) → (0 : Rat) < c →
      finSumInt b = finSumInt bStar →
      (∀ r s : Fin V, pow4Int (bStar r - bStar s) = p r / p s) →
      weightedQuantMse p c bStar ≤ weightedQuantMse p c b) ∧
    ((899 + 11952 + 118221 = 131072) ∧
     tieredAvgBits 899 11952 118221 (33 / 4) (17 / 4) (69 / 40) < 2 ∧
     tieredAvgBits 899 11952 118221 8 4 (158 / 100) < 2 ∧
     (73 / 100 : Rat) + 23 / 100 + 4 / 100 = 1 ∧
     tieredWeightedMse (73 / 100) (23 / 100) (4 / 100)
       ((3721435 : Rat) / 4294967296)
       ((56305549 : Rat) / 4294967296)
       ((867528745 : Rat) / 4294967296) <
       ((56305549 : Rat) / 4294967296) ∧
     (75 / 100 : Rat) + 23 / 100 + 2 / 100 = 1 ∧
     tieredWeightedMse (75 / 100) (23 / 100) (2 / 100) (1 / 65536) (1 / 256) (1 / 8) <
       (1 / 256 : Rat)) :=
  EmbedZipfLazyStamp.zipf_mixed_precision_embedding_allocation_pareto

end EmbedZipfLazyStampChallenge
