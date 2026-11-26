/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MlaKantorovichRope

/-!
# Verified Solutions (`mla-kantorovich-rope-bounds`)
-/

namespace MlaKantorovichRopeChallenge

open MlaKantorovichRope

theorem kantorovich_bilinear_spectral_leakage_exact :
    (∀ (n : Nat) (σmin σmax : Rat) (w γ : Fin n → Rat),
      0 < σmin → σmin ≤ σmax →
      (∀ j, 0 < w j) → (∀ j, 0 < γ j) →
      (∀ j, σmin * σmin ≤ w j / γ j) → (∀ j, w j / γ j ≤ σmax * σmax) →
      unbalancedCost w γ ≤
        kantorovichFactor (σmax / σmin) *
          (finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j))) ∧
    (∀ (σmin σmax : Rat), 0 < σmin → 0 < σmax →
      unbalancedCost (twoLevelW σmin σmax) (twoLevelGamma σmin σmax) =
        kantorovichFactor (σmax / σmin) *
          (finSum 2 (fun j => twoLevelW σmin σmax j * twoLevelGamma σmin σmax j) *
           finSum 2 (fun j => twoLevelW σmin σmax j * twoLevelGamma σmin σmax j))) ∧
    (∀ (n : Nat) (w γ dSq : Fin n → Rat),
      (∀ j, 0 < w j) → (∀ j, 0 < γ j) → (∀ j, 0 < dSq j) →
      finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j) ≤
        bilinearWeightedCost w γ dSq ∧
      bilinearWeightedCost w γ (fun j => w j / γ j) =
        finSum n (fun j => w j * γ j) * finSum n (fun j => w j * γ j)) ∧
    (kantorovichFactor 1 = 1 ∧
     kantorovichFactor 2 = 25 / 16 ∧
     kantorovichFactor 4 = 289 / 64 ∧
     kantorovichFactor 8 = 4225 / 256 ∧
     kantorovichFactor 16 = 66049 / 1024 ∧
     kantorovichFactor 32 = 1050625 / 4096 ∧
     kantorovichFactor 64 = 16785409 / 16384) :=
  MlaKantorovichRope.kantorovich_bilinear_spectral_leakage_exact

theorem absorbed_kv_gl_invariance_exact :
    (∀ (d_h d_c : Nat) (W_UK : Fin d_h → Fin d_c → Rat)
       (M M_inv : Fin d_c → Fin d_c → Rat) (q : Fin d_h → Rat) (c : Fin d_c → Rat),
      isLeftInverse M_inv M →
      dot (matVec (matTranspose (matMul W_UK M_inv)) q) (matVec M c) =
        dot (matVec (matTranspose W_UK) q) c) ∧
    (∀ (d_q d_h d_c : Nat) (W_UQ : Fin d_h → Fin d_q → Rat)
       (W_UK : Fin d_h → Fin d_c → Rat)
       (M M_inv : Fin d_c → Fin d_c → Rat) (q0 : Fin d_q → Rat) (c : Fin d_c → Rat),
      isLeftInverse M_inv M →
      dot (matVec (matTranspose (matMul W_UK M_inv)) (matVec W_UQ q0)) (matVec M c) =
        dot (matVec (matTranspose W_UK) (matVec W_UQ q0)) c) ∧
    (∀ (d_h d_c : Nat) (W_UK : Fin d_h → Fin d_c → Rat)
       (U : Fin d_c → Fin d_c → Rat) (d : Fin d_c → Rat)
       (q : Fin d_h → Rat) (c : Fin d_c → Rat),
      isOrthogonal U → (∀ j, d j ≠ 0) →
      isLeftInverse (matMul (diagInv d) (matTranspose U)) (matMul U (diagMat d)) ∧
      dot (matVec (matTranspose (matMul W_UK (matMul (diagInv d) (matTranspose U)))) q)
          (matVec (matMul U (diagMat d)) c) =
        dot (matVec (matTranspose W_UK) q) c) :=
  MlaKantorovichRope.absorbed_kv_gl_invariance_exact

theorem decoupled_nope_rope_256_85_crossover_exact :
    (mlaBitBudget 512 64 3 8 = 2048 ∧
     mlaBitBudget 512 64 4 4 = 2304 ∧
     mlaBitBudget 512 64 4 8 = 2560 ∧
     mlaBitBudget 512 64 3 6 = 1920 ∧
     ((2304 - 2048 : Rat) / 2304 = 1 / 9)) ∧
    (crossoverThreshold 3 8 4 4 = 256 / 85 ∧
     crossoverThreshold 3 6 4 4 = 16 / 5) ∧
    (∀ α_c α_R : Rat, 0 < α_c →
      (mlaDistortion α_c α_R 3 8 < mlaDistortion α_c α_R 4 4 ↔ (256 / 85 : Rat) < α_R / α_c) ∧
      (mlaDistortion α_c α_R 3 6 < mlaDistortion α_c α_R 4 4 ↔ (16 / 5 : Rat) < α_R / α_c)) ∧
    (∀ (α_c α_R : Rat) (b_c b_R b_c' b_R' : Nat),
      0 < α_c → b_c < b_c' → b_R' < b_R →
      (mlaDistortion α_c α_R b_c b_R < mlaDistortion α_c α_R b_c' b_R' ↔
        crossoverThreshold b_c b_R b_c' b_R' < α_R / α_c)) ∧
    (∀ (d_c d_R b_c b_R b_c' b_R' : Nat),
      b_c ≤ b_c' → b_R' ≤ b_R →
      (mlaBitBudget d_c d_R b_c b_R < mlaBitBudget d_c d_R b_c' b_R' ↔
        d_R * (b_R - b_R') < d_c * (b_c' - b_c))) :=
  MlaKantorovichRope.decoupled_nope_rope_256_85_crossover_exact

theorem parseval_tight_frame_multihead_interference_cap :
    (∀ (H d_c : Nat) (W : Fin H → Fin d_c → Rat) (c : Rat) (e : Fin d_c → Rat),
      isTightFrame W c → multiheadDistSq W e = c * normSq e) ∧
    (∀ (H d_c : Nat) (W : Fin H → Fin d_c → Rat) (s : Rat) (e : Fin d_c → Rat),
      0 < s → isRowOrthogonal W s → multiheadDistSq W e ≤ s * normSq e) ∧
    (∀ (H d_c : Nat) (W : Fin H → Fin d_c → Rat) (z : Fin d_c → Rat),
      0 < d_c → isRowOrthogonal W (d_c : Rat) → (∀ j, z j * z j = 1) →
      multiheadDistSq W z ≤ (d_c : Rat) * (d_c : Rat) ∧
      multiheadDistSq (coherentHeads H d_c) (allOnesVec d_c) =
        (H : Rat) * ((d_c : Rat) * (d_c : Rat))) ∧
    ((isRowOrthogonal (walshHeads 6 8) 64 ∧
      (∀ z : Fin 64 → Rat, (∀ j, z j * z j = 1) → multiheadDistSq (walshHeads 6 8) z ≤ 4096) ∧
      multiheadDistSq (coherentHeads 8 64) (allOnesVec 64) = 32768 ∧
      (32768 : Rat) / 4096 = 8) ∧
     (isRowOrthogonal (walshHeads 6 16) 64 ∧
      (∀ z : Fin 64 → Rat, (∀ j, z j * z j = 1) → multiheadDistSq (walshHeads 6 16) z ≤ 4096) ∧
      multiheadDistSq (coherentHeads 16 64) (allOnesVec 64) = 65536 ∧
      (65536 : Rat) / 4096 = 16) ∧
     (isRowOrthogonal (walshHeads 6 32) 64 ∧
      (∀ z : Fin 64 → Rat, (∀ j, z j * z j = 1) → multiheadDistSq (walshHeads 6 32) z ≤ 4096) ∧
      multiheadDistSq (coherentHeads 32 64) (allOnesVec 64) = 131072 ∧
      (131072 : Rat) / 4096 = 32) ∧
     (isRowOrthogonal (walshHeads 6 64) 64 ∧
      isTightFrame (walshHeads 6 64) 64 ∧
      (∀ z : Fin 64 → Rat, (∀ j, z j * z j = 1) → multiheadDistSq (walshHeads 6 64) z = 4096) ∧
      multiheadDistSq (coherentHeads 64 64) (allOnesVec 64) = 262144 ∧
      (262144 : Rat) / 4096 = 64)) :=
  MlaKantorovichRope.parseval_tight_frame_multihead_interference_cap

theorem pythagorean_1105_multi_angle_rope_exact :
    (1105 = 5 * 13 * 17 ∧ 1105 * 1105 = 1221025) ∧
    (pythPrimitive1105.length = 4 ∧
     (∀ p ∈ pythPrimitive1105, p.1 * p.1 + p.2 * p.2 = 1105 * 1105 ∧ Nat.gcd p.1 p.2 = 1) ∧
     (1104 > 1073 ∧ 1073 > 943 ∧ 943 > 817 ∧ 817 > 744 ∧ 744 > 576 ∧ 576 > 264 ∧ 264 > 47 ∧ 47 > 0)) ∧
    (pythCampaign1105.length = 10 ∧
     (∀ p ∈ pythCampaign1105, p.1 * p.1 + p.2 * p.2 = 1105 * 1105)) ∧
    (∀ (c s R : Rat) (q k : Fin 2 → Rat), R ≠ 0 → c * c + s * s = R * R →
      isOrthogonal (ropeRotMat c s R) ∧
      matMul (ropeRotMat c s R) (matTranspose (ropeRotMat c s R)) = matId 2 ∧
      normSq (ropeApply c s R q) = normSq q ∧
      dot (ropeApply c s R q) (ropeApply c s R k) = dot q k) ∧
    (∀ (c1 s1 R1 c2 s2 R2 : Rat) (q k : Fin 2 → Rat), R1 ≠ 0 → R2 ≠ 0 →
      (c1 * c2 - s1 * s2) * (c1 * c2 - s1 * s2) + (s1 * c2 + c1 * s2) * (s1 * c2 + c1 * s2) =
        (c1 * c1 + s1 * s1) * (c2 * c2 + s2 * s2) ∧
      ropeApply c1 s1 R1 (ropeApply c2 s2 R2 q) =
        ropeApply (c1 * c2 - s1 * s2) (s1 * c2 + c1 * s2) (R1 * R2) q ∧
      dot (ropeApply c1 s1 R1 q) (ropeApply c2 s2 R2 k) =
        dot (ropeApply (c1 * c2 + s1 * s2) (s1 * c2 - c1 * s2) (R1 * R2) q) k) :=
  MlaKantorovichRope.pythagorean_1105_multi_angle_rope_exact

theorem subbyte_mla_memory_compression_ratios_exact :
    (mlaBytesPerToken 512 64 2 8 = 192 ∧
     mlaBytesPerToken 512 0 2 0 = 128 ∧
     mlaBytesPerToken 512 0 4 0 = 256 ∧
     bf16MlaBytesPerToken 512 64 = 1152 ∧
     bf16MhaBytesPerToken 128 128 = 65536) ∧
    (bf16MhaBytesPerToken 128 128 / mlaBytesPerToken 512 64 2 8 = 1024 / 3 ∧
     bf16MlaBytesPerToken 512 64 / mlaBytesPerToken 512 64 2 8 = 6 ∧
     bf16MhaBytesPerToken 128 128 / mlaBytesPerToken 512 0 2 0 = 512 ∧
     bf16MlaBytesPerToken 512 64 / mlaBytesPerToken 512 0 2 0 = 9 ∧
     bf16MhaBytesPerToken 128 128 / mlaBytesPerToken 512 0 4 0 = 256) ∧
    (∀ (H d_h d_c d_R b_c b_R : Nat), 0 < mlaBitBudget d_c d_R b_c b_R →
      bf16MhaBytesPerToken H d_h / mlaBytesPerToken d_c d_R b_c b_R =
        ((32 * H * d_h : Nat) : Rat) / ((mlaBitBudget d_c d_R b_c b_R : Nat) : Rat) ∧
      bf16MlaBytesPerToken d_c d_R / mlaBytesPerToken d_c d_R b_c b_R =
        ((16 * (d_c + d_R) : Nat) : Rat) / ((mlaBitBudget d_c d_R b_c b_R : Nat) : Rat)) :=
  MlaKantorovichRope.subbyte_mla_memory_compression_ratios_exact

end MlaKantorovichRopeChallenge
