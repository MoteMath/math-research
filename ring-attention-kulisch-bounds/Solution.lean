/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RingAttnKulisch

/-!
# Verified Solutions (`ring-attention-kulisch-bounds`)
-/

namespace RingAttnKulischChallenge

open RingAttnKulisch

theorem online_softmax_merge_exact_associativity :
    (∀ s₁ s₂ : OnlineSoftmaxState, onlineMerge s₁ s₂ = onlineMerge s₂ s₁) ∧
    (∀ s₁ s₂ : OnlineSoftmaxState, 0 < s₁.w → 0 < s₂.w → 0 < (onlineMerge s₁ s₂).w) ∧
    (∀ s₁ s₂ s₃ : OnlineSoftmaxState, 0 < s₁.w → 0 < s₂.w → 0 < s₃.w →
      onlineMerge (onlineMerge s₁ s₂) s₃ = onlineMerge s₁ (onlineMerge s₂ s₃)) ∧
    (∀ s₁ s₂ : OnlineSoftmaxState, 0 < s₁.w → 0 < s₂.w →
      totalDenom (onlineMerge s₁ s₂) = totalDenom s₁ + totalDenom s₂ ∧
      totalNum (onlineMerge s₁ s₂) = totalNum s₁ + totalNum s₂) ∧
    (∀ s₁ s₂ : OnlineSoftmaxState, 0 < s₁.w → 0 < s₂.w →
      totalDenom s₁ + totalDenom s₂ ≠ 0 →
      normOutput (onlineMerge s₁ s₂) =
        (totalNum s₁ + totalNum s₂) / (totalDenom s₁ + totalDenom s₂)) :=
  RingAttnKulisch.online_softmax_merge_exact_associativity

theorem attention_sink_l2r_desc_vanishing_law :
    (∀ (p Δ n : Nat), 2 ≤ p → p ≤ Δ →
      rneGrid p (1 + invPow2Rat Δ) = 1 ∧
      l2rSinkAccum p Δ n = 1) ∧
    (∀ (p : Nat), 2 ≤ p →
      l2rSinkAccum p (p - 1) 1 = 1 + invPow2Rat (p - 1) ∧
      (1 : Rat) < l2rSinkAccum p (p - 1) 1) ∧
    (∀ (p P : Nat), 2 ≤ p →
      sinkRelErr p P (l2rSinkAccum p p (P - 1)) =
        ((P - 1 : Nat) : Rat) / (pow2Rat p + ((P - 1 : Nat) : Rat))) ∧
    (sinkRelErr 4 256 (l2rSinkAccum 4 4 255) = 255 / 271 ∧
     sinkRelErr 8 256 (l2rSinkAccum 8 8 255) = 255 / 511 ∧
     sinkRelErr 11 256 (l2rSinkAccum 11 11 255) = 255 / 2303 ∧
     sinkRelErr 24 256 (l2rSinkAccum 24 24 255) = 255 / 16777471) :=
  RingAttnKulisch.attention_sink_l2r_desc_vanishing_law

theorem binary_tree_vs_l2r_sink_survival_separation :
    (∀ (p k Δ : Nat), 2 ≤ p → 1 ≤ k → p + k - 1 ≤ Δ →
      treeSinkAccum p Δ k = 1) ∧
    (∀ (p k : Nat), 2 ≤ p → 1 ≤ k →
      treeSinkAccum p (p + k - 2) k = 1 + invPow2Rat (p - 1) ∧
      (1 : Rat) < treeSinkAccum p (p + k - 2) k) ∧
    (∀ (p k : Nat), 2 ≤ p → 2 ≤ k →
      l2rSinkAccum p p (2 ^ k - 1) = 1 ∧
      1 + invPow2Rat (p - 1) ≤ treeSinkAccum p p k ∧
      l2rSinkAccum p p (2 ^ k - 1) < treeSinkAccum p p k) ∧
    (deltaVanishTree 8 4 (-6) 3 = 10 ∧
     deltaVanishTree 8 8 (-126) 7 = 15 ∧
     deltaVanishTree 8 11 (-14) 10 = 18 ∧
     deltaVanishTree 8 24 (-126) 23 = 31) :=
  RingAttnKulisch.binary_tree_vs_l2r_sink_survival_separation

theorem descending_mi_phase_transition_paradox :
    (∀ ws : List Rat, isNonIncreasing ws → rescaleCount ws = 0) ∧
    (∀ ws : List Rat, isStrictlyIncreasing ws → rescaleCount ws = ws.length - 1) ∧
    (rescaleCount [49 / 64, 7 / 8, 1] = 2 ∧
     rescaleCount [1, 7 / 8, 49 / 64] = 0 ∧
     seqMergeDenom 4 regimeIChunksAsc = 1 ∧
     seqMergeDenom 4 regimeIChunksDesc = 9 / 8 ∧
     ratAbs (557 / 512 - seqMergeDenom 4 regimeIChunksAsc) = 45 / 512 ∧
     ratAbs (557 / 512 - seqMergeDenom 4 regimeIChunksDesc) = 19 / 512 ∧
     ratAbs (557 / 512 - seqMergeDenom 4 regimeIChunksDesc) <
       ratAbs (557 / 512 - seqMergeDenom 4 regimeIChunksAsc)) ∧
    (∀ (p k : Nat), 2 ≤ p → 2 ≤ k →
      l2rSinkAccum p p (2 ^ k - 1) = 1 ∧
      l2rSinkAccum p p (2 ^ k - 1) < treeSinkAccum p p k ∧
      l2rSinkAccum p p (2 ^ k - 1) <
        rneGrid p (1 + ((2 ^ k - 1 : Nat) : Rat) * invPow2Rat p)) :=
  RingAttnKulisch.descending_mi_phase_transition_paradox

theorem fixed_point_kulisch_topology_partition_invariance :
    (∀ t : BinTree Int, t.evalInt = fixptSum t.toList) ∧
    (∀ chunks : List (List Int), fixptSum (chunks.map fixptSum) = fixptSum chunks.flatten) ∧
    (∀ xs ys : List Int, ListPerm xs ys → fixptSum xs = fixptSum ys) ∧
    (∀ xs : List Int, fixptSum xs.reverse = fixptSum xs) ∧
    (∀ (xs : List Int) (r : Nat), fixptSum (xs.drop r ++ xs.take r) = fixptSum xs) ∧
    (∀ (k p : Nat), wInvBits k p = p + 2 * k + 4) ∧
    (∀ (k p : Nat) (xs : List Int), xs.length ≤ 2 ^ k →
      (∀ x, x ∈ xs →
        -((2 ^ (p + k + 3) : Nat) : Int) + 1 ≤ x ∧
        x ≤ ((2 ^ (p + k + 3) : Nat) : Int) - 1) →
      -((2 ^ (wInvBits k p - 1) : Nat) : Int) < fixptSum xs ∧
      fixptSum xs < ((2 ^ (wInvBits k p - 1) : Nat) : Int)) ∧
    ((wInvBits 8 4 = 24 ∧ wInvBits 8 8 = 28 ∧ wInvBits 8 11 = 31 ∧ wInvBits 8 24 = 44) ∧
     (wKulischBits 8 8 (-6) 3 = 27 ∧ wKulischBits 8 15 (-14) 10 = 49 ∧
      wKulischBits 8 127 (-126) 7 = 270 ∧ wKulischBits 8 127 (-126) 23 = 286)) :=
  RingAttnKulisch.fixed_point_kulisch_topology_partition_invariance

theorem fixed_point_sink_cliff_elimination :
    (∀ (F Δ k : Nat), Δ ≤ F →
      fixptBulkTerm F Δ = ((2 ^ (F - Δ) : Nat) : Int) ∧
      fixptSinkDenom F Δ k = trueSinkDenom Δ (2 ^ k)) ∧
    (∀ (p k : Nat), 2 ≤ p → 2 ≤ k →
      fixptSinkDenom (p + k) (p + k - 1) k = trueSinkDenom (p + k - 1) (2 ^ k) ∧
      fixptSinkOut p (p + k) (p + k - 1) k = 1 + invPow2Rat (p - 1) ∧
      (1 : Rat) < fixptSinkOut p (p + k) (p + k - 1) k) ∧
    (∀ (p k : Nat), 2 ≤ p → 1 ≤ k →
      fixptSinkOut p (p + k) (p + k) k = 1) ∧
    (∀ (p k : Nat), 2 ≤ p → 1 ≤ k →
      fixptBulkTerm (p + k - 2) (p + k - 1) = 0 ∧
      fixptSinkDenom (p + k - 2) (p + k - 1) k = 1) :=
  RingAttnKulisch.fixed_point_sink_cliff_elimination

end RingAttnKulischChallenge
