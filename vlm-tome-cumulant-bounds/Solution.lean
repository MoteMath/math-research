/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VlmTomeCumulant

/-!
# Verified Solutions (`vlm-tome-cumulant-bounds`)
-/

namespace VlmTomeCumulantChallenge

open VlmTomeCumulant

theorem unweighted_merge_tv_distortion_and_exact_ceiling :
    (∀ (s : Nat) (w W : Rat), 1 ≤ s → 0 < w → 0 < W →
      origClusterProb s w W - unwClusterProb w W = tvUnweighted s (unwClusterProb w W)) ∧
    (∀ (s : Nat) (r p' : Rat), 1 ≤ s → 0 < r → r * r = (s : Rat) → 0 ≤ p' → p' ≤ 1 →
      tvCeilingOfSqrt r - tvUnweighted s p' =
        (r - 1) * ((r + 1) * p' - 1) * ((r + 1) * p' - 1) /
          ((r + 1) * (1 + ((s : Rat) - 1) * p')) ∧
      tvUnweighted s p' ≤ tvCeilingOfSqrt r ∧
      tvUnweighted s (1 / (r + 1)) = tvCeilingOfSqrt r) ∧
    (∀ (s : Nat) (r p' : Rat), 1 ≤ s → 0 < r → (s : Rat) ≤ r * r → 0 ≤ p' → p' ≤ 1 →
      tvUnweighted s p' ≤ tvCeilingOfSqrt r) ∧
    (∀ (s : Nat) (r : Rat), 1 ≤ s → 1 ≤ r → r * r ≤ (s : Rat) →
      tvCeilingOfSqrt r ≤ tvUnweighted s (1 / (r + 1))) ∧
    (tvCeilingOfSqrt 2 = 1 / 3 ∧ tvUnweighted 4 (1 / 3) = 1 / 3 ∧
     tvCeilingOfSqrt 3 = 1 / 2 ∧ tvUnweighted 9 (1 / 4) = 1 / 2 ∧
     tvCeilingOfSqrt 4 = 3 / 5 ∧ tvUnweighted 16 (1 / 5) = 3 / 5) ∧
    ((∀ p' : Rat, 0 ≤ p' → p' ≤ 1 → tvUnweighted 2 p' ≤ 17158 / 100000) ∧
     (17157 / 100000 : Rat) ≤ tvUnweighted 2 (100000 / 241421) ∧
     (∀ p' : Rat, 0 ≤ p' → p' ≤ 1 → tvUnweighted 8 p' ≤ 47760 / 100000) ∧
     (47759 / 100000 : Rat) ≤ tvUnweighted 8 (100000 / 382842) ∧
     (∀ p' : Rat, 0 ≤ p' → p' ≤ 1 → tvUnweighted 32 p' ≤ 69956 / 100000) ∧
     (69955 / 100000 : Rat) ≤ tvUnweighted 32 (100000 / 665685)) :=
  VlmTomeCumulant.unweighted_merge_tv_distortion_and_exact_ceiling

theorem proportional_attention_zero_dispersion_exact_invariance :
    ∀ (s m : Nat) (w : Rat) (vCl : Fin s → Rat) (u vOut : Fin m → Rat),
      1 ≤ s → 0 < w → (∀ i, 0 ≤ u i) →
      propPartition s w u = origPartition s w u ∧
      (∀ i : Fin m, u i / propPartition s w u = u i / origPartition s w u) ∧
      ((s : Rat) * w / propPartition s w u = finSum (fun _ : Fin s => w / origPartition s w u)) ∧
      collapsedTV
        ((s : Rat) * w / propPartition s w u)
        (finSum (fun _ : Fin s => w / origPartition s w u))
        (fun i => u i / propPartition s w u)
        (fun i => u i / origPartition s w u) = 0 ∧
      propAttnOutput s w vCl u vOut = origAttnOutput w vCl u vOut :=
  VlmTomeCumulant.proportional_attention_zero_dispersion_exact_invariance

theorem within_cluster_dispersion_jensen_underweight_and_cumulant2_bonus :
    (∀ (s : Nat) (η : Fin s → Rat), 1 ≤ s → finSum η = 0 →
      finSum (fun j => expTaylor2 (η j)) / (s : Rat) = 1 + clusterVar η / 2 ∧
      ((∃ j, η j ≠ 0) →
        (1 : Rat) < finSum (fun j => expTaylor2 (η j)) / (s : Rat) ∧
        (∀ w : Rat, 0 < w → (s : Rat) * w < w * finSum (fun j => expTaylor2 (η j))) ∧
        (1 : Rat) < finSum (fun j => expTaylor4 (η j)) / (s : Rat))) ∧
    (∀ (s : Nat) (η : Fin s → Rat), 1 ≤ s → finSum η = 0 →
      finSum (fun j => expTaylor2 (η j)) - (s : Rat) * cumulant2Factor1 (clusterVar η) = 0) ∧
    (∀ (s : Nat) (η : Fin s → Rat), 1 ≤ s → finSum η = 0 →
      finSum (fun j => expTaylor3 (η j)) / (s : Rat) - cumulant2Factor1 (clusterVar η) =
        clusterMoment3 η / 6 ∧
      finSum (fun j => expTaylor4 (η j)) / (s : Rat) - cumulant2Factor2 (clusterVar η) =
        clusterMoment3 η / 6 + (clusterMoment4 η - 3 * clusterVar η * clusterVar η) / 24) ∧
    (∀ σ : Rat,
      let η4 : Fin 4 → Rat := fun j => if j.val % 2 = 0 then σ else -σ
      finSum η4 = 0 ∧
      clusterVar η4 = σ * σ ∧
      clusterMoment3 η4 = 0 ∧
      finSum (fun j => expTaylor2 (η4 j)) / 4 - cumulant2Factor1 (clusterVar η4) = 0 ∧
      finSum (fun j => expTaylor4 (η4 j)) / 4 - 1 = σ * σ / 2 + σ * σ * σ * σ / 24 ∧
      finSum (fun j => expTaylor4 (η4 j)) / 4 - cumulant2Factor1 (clusterVar η4) =
        σ * σ * σ * σ / 24) ∧
    (let η02 : Fin 4 → Rat := fun j => if j.val % 2 = 0 then 1 / 5 else -(1 / 5)
     (finSum (fun j => expTaylor4 (η02 j)) / 4 - 1) /
       (finSum (fun j => expTaylor4 (η02 j)) / 4 - cumulant2Factor1 (clusterVar η02)) = 301) :=
  VlmTomeCumulant.within_cluster_dispersion_jensen_underweight_and_cumulant2_bonus

theorem bipartite_wht_int4_outlier_rescue_vs_binary_walsh_tie :
    (∀ (k : Nat) (u v : Fin (2 ^ k) → Int),
      dotInt (wht k u) (wht k v) = (2 ^ k : Int) * dotInt u v ∧
      normSqInt (wht k u) = (2 ^ k : Int) * normSqInt u ∧
      (∀ i : Fin (2 ^ k), wht k (wht k u) i = (2 ^ k : Int) * u i)) ∧
    (∀ (k : Nat) (M : Int) (i : Fin (2 ^ k)),
      wht k (outlierVec k M) i = M ∧
      ((wht k (outlierVec k M) i : Rat) * (wht k (outlierVec k M) i : Rat)) / ((2 ^ k : Nat) : Rat) =
        ((M : Rat) * (M : Rat)) / ((2 ^ k : Nat) : Rat)) ∧
    (∀ (m : Nat) (M : Int) (i : Fin (2 ^ (2 * m))),
      (wht (2 * m) (outlierVec (2 * m) M) i : Rat) / ((2 ^ m : Nat) : Rat) =
        (M : Rat) / ((2 ^ m : Nat) : Rat)) ∧
    (∀ (k : Nat), 1 ≤ k → ∀ (M a b1 b2 : Int),
      0 < a → 0 < b1 → 0 < b2 → a < M → b1 < M → b2 < M →
      let q := outlierSignalVec k M a
      let k1 := outlierSignalVec k M b1
      let k2 := outlierSignalVec k M (-b2)
      hammingDist (simHash q) (simHash k1) = 0 ∧
      hammingDist (simHash q) (simHash k2) = 1 ∧
      hammingDist (simHash (wht k q)) (simHash (wht k k1)) = 0 ∧
      hammingDist (simHash (wht k q)) (simHash (wht k k2)) = 0) ∧
    (∀ (k : Nat), 1 ≤ k → ∀ (j : Fin (2 ^ k)),
      j.val ≠ 0 →
      hammingDist (simHash (wht k (basisVec k ⟨0, Nat.two_pow_pos k⟩)))
        (simHash (wht k (basisVec k j))) = 2 ^ (k - 1)) :=
  VlmTomeCumulant.bipartite_wht_int4_outlier_rescue_vs_binary_walsh_tie

theorem vit_front_loaded_dominates_constant_r_schedule :
    (∀ (L N0 c : Nat) (r : Fin L → Nat) (w : Fin L → Rat) (i j : Fin L) (Δ : Nat),
      i.val < j.val → 0 < Δ → Δ ≤ r j → finSumNat r ≤ N0 →
      let r' := shiftSchedule r i j Δ
      finSumNat r' = finSumNat r ∧
      attnFlops N0 r' < attnFlops N0 r ∧
      vitFlops N0 c r' < vitFlops N0 c r ∧
      scheduleDrift w r' = scheduleDrift w r - (Δ : Rat) * (w j - w i) ∧
      (w i < w j → scheduleDrift w r' < scheduleDrift w r)) ∧
    (∀ (L N0 c R : Nat) (rFront : Fin L → Nat) (w : Fin L → Rat),
      2 ≤ L → L * R ≤ N0 →
      let rConst : Fin L → Nat := fun _ => R
      finSumNat rFront = finSumNat rConst →
      (∀ k : Fin (L - 1), prefixSum rConst k.val ≤ prefixSum rFront k.val) →
      (∃ k : Fin (L - 1), prefixSum rConst k.val < prefixSum rFront k.val) →
      attnFlops N0 rFront < attnFlops N0 rConst ∧
      vitFlops N0 c rFront < vitFlops N0 c rConst ∧
      ((∀ k : Fin (L - 1), w ⟨k.val, by omega⟩ < w ⟨k.val + 1, by omega⟩) →
        scheduleDrift w rFront < scheduleDrift w rConst)) ∧
    (let rConst24 : Fin 24 → Nat := fun _ => 32
     let rFront24 : Fin 24 → Nat := fun l => if l.val < 12 then 64 else 0
     finSumNat rFront24 = finSumNat rConst24 ∧
     attnFlops 1024 rFront24 < attnFlops 1024 rConst24 ∧
     vitFlops 1024 6144 rFront24 < vitFlops 1024 6144 rConst24) :=
  VlmTomeCumulant.vit_front_loaded_dominates_constant_r_schedule

theorem late_loaded_merging_flop_infeasibility_ceiling :
    (∀ (L k N0 c : Nat) (r : Fin L → Nat),
      k ≤ L → 1 ≤ k → 1 ≤ N0 → 2 * L ≤ 3 * k →
      (∀ l : Fin L, l.val < k → r l = 0) →
      2 * L * (N0 * N0) ≤ 3 * attnFlops N0 r ∧
      ((L * (N0 * N0) : Nat) : Rat) / (attnFlops N0 r : Rat) ≤ 3 / 2 ∧
      2 * L * (N0 * N0 + c * N0) ≤ 3 * vitFlops N0 c r ∧
      ((L * (N0 * N0 + c * N0) : Nat) : Rat) / (vitFlops N0 c r : Rat) ≤ 3 / 2 ∧
      ((∃ l : Fin L, k ≤ l.val ∧ 1 ≤ remTokens N0 r l) →
        2 * L * (N0 * N0) < 3 * attnFlops N0 r ∧
        ((L * (N0 * N0) : Nat) : Rat) / (attnFlops N0 r : Rat) < 3 / 2 ∧
        2 * L * (N0 * N0 + c * N0) < 3 * vitFlops N0 c r ∧
        ((L * (N0 * N0 + c * N0) : Nat) : Rat) / (vitFlops N0 c r : Rat) < 3 / 2)) ∧
    ((3 / 2 : Rat) < 2 ∧ (3 / 2 : Rat) < 4 ∧ (3 / 2 : Rat) < 8) ∧
    (∀ (r : Fin 24 → Nat),
      (∀ l : Fin 24, l.val < 16 → r l = 0) →
      (∃ l : Fin 24, 16 ≤ l.val ∧ 1 ≤ remTokens 1024 r l) →
      ((24 * (1024 * 1024) : Nat) : Rat) / (attnFlops 1024 r : Rat) < 3 / 2 ∧
      ((24 * (1024 * 1024 + 6144 * 1024) : Nat) : Rat) / (vitFlops 1024 6144 r : Rat) < 3 / 2) :=
  VlmTomeCumulant.late_loaded_merging_flop_infeasibility_ceiling

end VlmTomeCumulantChallenge
