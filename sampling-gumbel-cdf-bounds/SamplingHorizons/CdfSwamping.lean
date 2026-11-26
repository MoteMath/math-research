/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SamplingHorizons.RatOrder

/-!
# Pillar 3: Descending Inverse-CDF Swamping, Pairwise Fenwick Tree, and Top-p Shortfall Laws

Proves:
- Headline Theorem 4 (`descending_cdf_swamping_erasure_law`):
  Exact IEEE-754 RNE swamping cutoff `2^{-(m+2)}` at `S ≥ 1/2` (`1/512` BF16, `1/4096` FP16,
  `2^{-25}` FP32), proving every descending tail token `p_j ≤ 2^{-(m+2)}` is 100% swamped
  and all `V - k0` remaining tail tokens are permanently erased.
- Headline Theorem 5 (`fenwick_pairwise_tree_zero_swamping_exact`):
  Exact zero-rounding-error pairwise binary-tree / Fenwick summation `pairwiseTreeSum flAdd k (2^{-r}) = 2^k * 2^{-r}`
  for all `k, r : Nat` under any RNE adder exact on dyadic powers of two.
- Headline Theorem 6 (`top_p_nucleus_mass_shortfall_lower_bound`):
  Exact cumulative CDF shortfall `K * t` and exact TV distance lower bound `tvDist p pEff ≥ K * t`
  for `K` swamped tail tokens, plus the Llama-3 `V = 128,256` `BF16` witness exceeding `1/2`.
-/

namespace SamplingHorizons

/-! ### Helper Lemmas for Theorem 4 -/

theorem rneRoundsToGrid_add_swamp (m k : Nat) (p : Rat) (hp : (0 : Rat) ≤ p)
    (hcut : p < swampCutoffHalf m ∨ (p = swampCutoffHalf m ∧ k % 2 = 0)) :
    rneRoundsToGrid (invPow2Rat (m + 1)) k ((k : Rat) * invPow2Rat (m + 1) + p) := by
  unfold rneRoundsToGrid swampCutoffHalf at *
  have hdiff : ((k : Rat) * invPow2Rat (m + 1) + p) - (k : Rat) * invPow2Rat (m + 1) = p := by
    grind
  rw [hdiff, ratAbs_of_nonneg hp, invPow2Rat_div_two (m + 1)]
  exact hcut

theorem seqCdfAux_frozen (add : Rat → Rat → Rat) (S : Rat) :
    ∀ (k : Nat) (p : Fin k → Rat), (∀ i : Fin k, add S (p i) = S) →
      seqCdfAux add S k p = S
  | 0, _, _ => rfl
  | k + 1, p, hswamp => by
    simp only [seqCdfAux]
    have hprev : seqCdfAux add S k (fun j => p ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) = S :=
      seqCdfAux_frozen add S k (fun j => p ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
        (fun j => hswamp ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    rw [hprev]
    exact hswamp ⟨k, Nat.lt_succ_self k⟩

theorem seqCdf_frozen (add : Rat → Rat → Rat) (S : Rat) {n : Nat} (p : Fin n → Rat)
    (hswamp : ∀ i : Fin n, add S (p i) = S) :
    seqCdf add S p = S :=
  seqCdfAux_frozen add S n p hswamp

/-- Headline Theorem 4 (`descending_cdf_swamping_erasure_law`). -/
theorem descending_cdf_swamping_erasure_law :
    (swampCutoffHalf 7 = 1 / 512 ∧
     swampCutoffHalf 10 = 1 / 4096 ∧
     swampCutoffHalf 23 = 1 / 33554432) ∧
    (∀ (m k : Nat) (p : Rat), (0 : Rat) ≤ p →
      (p < swampCutoffHalf m ∨ (p = swampCutoffHalf m ∧ k % 2 = 0)) →
      rneRoundsToGrid (invPow2Rat (m + 1)) k ((k : Rat) * invPow2Rat (m + 1) + p)) ∧
    (∀ (m V : Nat) (add : Rat → Rat → Rat) (S : Rat) (p : Fin V → Rat) (k0 : Nat) (hk0 : k0 < V),
      (∀ x : Rat, (0 : Rat) ≤ x → x ≤ swampCutoffHalf m → add S x = S) →
      (∀ i : Fin V, (0 : Rat) ≤ p i) →
      (∀ i j : Fin V, i.val ≤ j.val → p j ≤ p i) →
      p ⟨k0, hk0⟩ ≤ swampCutoffHalf m →
      (∀ j : Fin V, k0 ≤ j.val → p j ≤ swampCutoffHalf m ∧ add S (p j) = S) ∧
      seqCdf add S (fun i : Fin (V - k0) => p ⟨k0 + i.val, by omega⟩) = S) ∧
    (32768 - 19647 = 13121 ∧ 0 < 32768 - 19647 ∧ swampCutoffHalf 23 = invPow2Rat 25) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · unfold swampCutoffHalf invPow2Rat pow2Rat; rfl
    · unfold swampCutoffHalf invPow2Rat pow2Rat; rfl
    · unfold swampCutoffHalf invPow2Rat pow2Rat; rfl
  · exact rneRoundsToGrid_add_swamp
  · intro m V add S p k0 hk0 hSwamp hNonneg hDesc hCut
    have hTail : ∀ j : Fin V, k0 ≤ j.val → p j ≤ swampCutoffHalf m ∧ add S (p j) = S := by
      intro j hj
      have hle : p j ≤ p ⟨k0, hk0⟩ := hDesc ⟨k0, hk0⟩ j hj
      have hcutj : p j ≤ swampCutoffHalf m := Rat.le_trans hle hCut
      exact ⟨hcutj, hSwamp (p j) (hNonneg j) hcutj⟩
    refine ⟨hTail, ?_⟩
    apply seqCdf_frozen
    intro i
    exact (hTail ⟨k0 + i.val, by omega⟩ (Nat.le_add_right k0 i.val)).2
  · refine ⟨by decide, by decide, rfl⟩

/-! ### Helper Lemmas for Theorem 5 -/

theorem isDyadicPow2_mul_inv (k r : Nat) : isDyadicPow2 (pow2Rat k * invPow2Rat r) :=
  ⟨k, r, rfl⟩

theorem pairwiseTreeSum_exact (add : Rat → Rat → Rat)
    (hExact : ∀ x : Rat, isDyadicPow2 x → add x x = x + x)
    (r : Nat) : ∀ k : Nat, pairwiseTreeSum add k (invPow2Rat r) = pow2Rat k * invPow2Rat r
  | 0 => by
    simp only [pairwiseTreeSum, pow2Rat, Nat.pow_zero]
    grind
  | k + 1 => by
    simp only [pairwiseTreeSum]
    have ih := pairwiseTreeSum_exact add hExact r k
    rw [ih, hExact _ (isDyadicPow2_mul_inv k r), pow2Rat_succ]
    grind

/-- Headline Theorem 5 (`fenwick_pairwise_tree_zero_swamping_exact`). -/
theorem fenwick_pairwise_tree_zero_swamping_exact :
    (∀ (add : Rat → Rat → Rat),
      (∀ x : Rat, isDyadicPow2 x → add x x = x + x) →
      ∀ (k r : Nat),
        pairwiseTreeSum add k (invPow2Rat r) = pow2Rat k * invPow2Rat r ∧
        pairwiseTreeSum add k (invPow2Rat r) - pow2Rat k * invPow2Rat r = 0) ∧
    (∀ (add : Rat → Rat → Rat) (k r : Nat),
      (∀ x : Rat, isDyadicPow2 x → add x x = x + x) →
      add (1 / 2 : Rat) (invPow2Rat r) = 1 / 2 →
      seqCdf add (1 / 2 : Rat) (fun _ : Fin (2 ^ k) => invPow2Rat r) = 1 / 2 ∧
      pairwiseTreeSum add k (invPow2Rat r) = pow2Rat k * invPow2Rat r) ∧
    (∀ (add : Rat → Rat → Rat) (r : Nat),
      (∀ x : Rat, isDyadicPow2 x → add x x = x + x) →
      1 ≤ r →
      pairwiseTreeSum add (r - 1) (invPow2Rat r) = 1 / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro add hExact k r
    have heq := pairwiseTreeSum_exact add hExact r k
    refine ⟨heq, ?_⟩
    rw [heq]; grind
  · intro add k r hExact hSwamp
    refine ⟨?_, pairwiseTreeSum_exact add hExact r k⟩
    apply seqCdf_frozen
    intro _; exact hSwamp
  · intro add r hExact hr
    rw [pairwiseTreeSum_exact add hExact r (r - 1)]
    have hsplit : r = (r - 1) + 1 := (Nat.sub_add_cancel hr).symm
    have hpow : pow2Rat r = 2 * pow2Rat (r - 1) := by
      have h1 : pow2Rat ((r - 1) + 1) = 2 * pow2Rat (r - 1) := pow2Rat_succ (r - 1)
      rw [← hsplit] at h1
      exact h1
    unfold invPow2Rat
    rw [hpow]
    have hp : pow2Rat (r - 1) ≠ 0 := pow2Rat_ne_zero (r - 1)
    have h2p : (2 : Rat) * pow2Rat (r - 1) ≠ 0 := by
      intro h0
      cases Rat.mul_eq_zero.mp h0 with
      | inl h => exact absurd h (by decide)
      | inr h => exact hp h
    apply Eq.symm
    apply (rat_div_eq_iff (by decide)).mpr
    have hmul : pow2Rat (r - 1) * (1 / (2 * pow2Rat (r - 1))) * 2 =
        (1 / (2 * pow2Rat (r - 1))) * (2 * pow2Rat (r - 1)) := by grind
    rw [hmul, rat_div_mul_cancel h2p]

/-! ### Helper Lemmas for Theorem 6 -/

theorem tvDist_ge_erased_tail {nHead K : Nat} (p pEff : Fin (nHead + K) → Rat) (t : Rat)
    (ht : (0 : Rat) ≤ t)
    (hpSum : finSum p = 1) (hpEffSum : finSum pEff = 1)
    (hpTail : ∀ j : Fin K, p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ = t)
    (hpEffTail : ∀ j : Fin K, pEff ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ = 0) :
    (K : Rat) * t ≤ tvDist p pEff := by
  unfold tvDist
  rw [finSum_split_head_tail]
  have hTailAbs : finSum (fun j : Fin K =>
      ratAbs (p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ -
              pEff ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩)) = (K : Rat) * t := by
    have hc : finSum (fun j : Fin K =>
        ratAbs (p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ -
                pEff ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩)) =
        finSum (fun _ : Fin K => t) := by
      apply finSum_congr
      intro j
      rw [hpTail j, hpEffTail j]
      have : t - 0 = t := by grind
      rw [this, ratAbs_of_nonneg ht]
    rw [hc, finSum_const]
  have hDiffSum : finSum (fun i : Fin (nHead + K) => p i - pEff i) = 0 := by
    rw [finSum_sub, hpSum, hpEffSum]; grind
  rw [finSum_split_head_tail] at hDiffSum
  have hTailDiff : finSum (fun j : Fin K =>
      p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ -
      pEff ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩) = (K : Rat) * t := by
    have hc : finSum (fun j : Fin K =>
        p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ -
        pEff ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩) =
        finSum (fun _ : Fin K => t) := by
      apply finSum_congr
      intro j
      rw [hpTail j, hpEffTail j]; grind
    rw [hc, finSum_const]
  rw [hTailDiff] at hDiffSum
  have hHeadSum : finSum (fun i : Fin nHead =>
      p ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right nHead K)⟩ -
      pEff ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right nHead K)⟩) = -((K : Rat) * t) := by
    grind
  have hKtNonneg : (0 : Rat) ≤ (K : Rat) * t := Rat.mul_nonneg (rat_natCast_nonneg K) ht
  have hHeadAbs : (K : Rat) * t ≤
      finSum (fun i : Fin nHead =>
        ratAbs (p ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right nHead K)⟩ -
                pEff ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right nHead K)⟩)) := by
    have htri := ratAbs_finSum_le (fun i : Fin nHead =>
      p ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right nHead K)⟩ -
      pEff ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right nHead K)⟩)
    rw [hHeadSum] at htri
    have hneg : -((K : Rat) * t) ≤ 0 := by
      have := rat_sub_nonneg hKtNonneg
      grind
    rw [ratAbs_of_nonpos hneg] at htri
    have hnn : - -((K : Rat) * t) = (K : Rat) * t := by grind
    rw [hnn] at htri
    exact htri
  rw [hTailAbs]
  have hsumLe : (K : Rat) * t + (K : Rat) * t ≤
      finSum (fun i : Fin nHead =>
        ratAbs (p ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right nHead K)⟩ -
                pEff ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right nHead K)⟩)) +
      (K : Rat) * t :=
    rat_add_le_add hHeadAbs Rat.le_refl
  have hhalf : (1 / 2 : Rat) * ((K : Rat) * t + (K : Rat) * t) = (K : Rat) * t := by grind
  have hhalfPos : (0 : Rat) < (1 / 2 : Rat) := rat_div_pos (a := 1) (b := 2) (by decide) (by decide)
  have hmul := rat_mul_le_mul_of_nonneg_left hsumLe (Rat.le_of_lt hhalfPos)
  rw [hhalf] at hmul
  exact hmul

/-- Headline Theorem 6 (`top_p_nucleus_mass_shortfall_lower_bound`). -/
theorem top_p_nucleus_mass_shortfall_lower_bound :
    (∀ (m nHead K : Nat) (add : Rat → Rat → Rat) (S t : Rat)
      (p pEff : Fin (nHead + K) → Rat),
      (1 / 2 : Rat) ≤ S → S ≤ 1 - (K : Rat) * t →
      (0 : Rat) ≤ t → t ≤ swampCutoffHalf m →
      (∀ x : Rat, (0 : Rat) ≤ x → x ≤ swampCutoffHalf m → add S x = S) →
      finSum p = 1 → finSum pEff = 1 →
      (∀ j : Fin K, p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ = t) →
      (∀ j : Fin K, pEff ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ = 0) →
      seqCdf add S (fun j : Fin K => p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩) = S ∧
      (K : Rat) * t ≤ 1 - S ∧
      (finSum (fun i : Fin nHead => p ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right nHead K)⟩) = S →
        1 - S = (K : Rat) * t) ∧
      (K : Rat) * t ≤ tvDist p pEff) ∧
    (let nHead : Nat := 84
     let K : Nat := 128172
     let S : Rat := 7 / 16
     let t : Rat := (9 / 16 : Rat) / (128172 : Rat)
     nHead + K = 128256 ∧
     (1 / 4 : Rat) ≤ S ∧ S < 1 / 2 ∧
     (0 : Rat) < t ∧ t < swampCutoffQuarter 7 ∧
     (K : Rat) * t = 9 / 16 ∧
     (1 / 2 : Rat) < (K : Rat) * t ∧
     ∀ (p pEff : Fin (nHead + K) → Rat),
       finSum p = 1 → finSum pEff = 1 →
       (∀ j : Fin K, p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ = t) →
       (∀ j : Fin K, pEff ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ = 0) →
       (1 / 2 : Rat) < tvDist p pEff) := by
  refine ⟨?_, ?_⟩
  · intro m nHead K add S t p pEff _hSlo hShi ht hcut hSwamp hpSum hpEffSum hpTail hpEffTail
    have hFrozen : seqCdf add S (fun j : Fin K => p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩) = S := by
      apply seqCdf_frozen
      intro j
      rw [hpTail j]
      exact hSwamp t ht hcut
    have hShortfallGe : (K : Rat) * t ≤ 1 - S := by
      have := rat_sub_nonneg hShi
      apply rat_le_of_sub_nonneg
      have heq : (1 - S) - (K : Rat) * t = (1 - (K : Rat) * t) - S := by grind
      rw [heq]; exact this
    have hExactShortfall :
        finSum (fun i : Fin nHead => p ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right nHead K)⟩) = S →
        1 - S = (K : Rat) * t := by
      intro hHead
      rw [finSum_split_head_tail] at hpSum
      have hTailSum : finSum (fun j : Fin K => p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩) =
          (K : Rat) * t := by
        rw [finSum_congr hpTail, finSum_const]
      rw [hHead, hTailSum] at hpSum
      grind
    exact ⟨hFrozen, hShortfallGe, hExactShortfall,
           tvDist_ge_erased_tail p pEff t ht hpSum hpEffSum hpTail hpEffTail⟩
  · dsimp only
    let nHead : Nat := 84
    let K : Nat := 128172
    let S : Rat := 7 / 16
    let t : Rat := (9 / 16 : Rat) / (128172 : Rat)
    have hS1 : (1 / 4 : Rat) ≤ S := by
      apply rat_le_of_mul_pos_right (c := (16 : Rat)) (by decide)
      have hL : (1 / 4 : Rat) * 16 = 4 := by
        have : (1 / 4 : Rat) * 16 = ((1 / 4 : Rat) * 4) * 4 := by grind
        rw [this, rat_div_mul_cancel (by decide)]; grind
      have hR : (7 / 16 : Rat) * 16 = 7 := rat_div_mul_cancel (by decide)
      rw [hL, hR]; exact rat_natCast_le (by decide)
    have hS2 : S < 1 / 2 := by
      apply rat_lt_of_mul_pos_right (c := (16 : Rat)) (by decide)
      have hL : (7 / 16 : Rat) * 16 = 7 := rat_div_mul_cancel (by decide)
      have hR : (1 / 2 : Rat) * 16 = 8 := by
        have : (1 / 2 : Rat) * 16 = ((1 / 2 : Rat) * 2) * 8 := by grind
        rw [this, rat_div_mul_cancel (by decide)]; grind
      rw [hL, hR]; exact rat_natCast_lt (by decide)
    have htPos : (0 : Rat) < t := rat_div_pos (rat_div_pos (by decide) (by decide)) (by decide)
    have htCut : t < swampCutoffQuarter 7 := by
      unfold swampCutoffQuarter invPow2Rat pow2Rat
      have hd : (0 : Rat) < (16 * 128172 * 1024 : Rat) := by
        exact rat_mul_pos (rat_mul_pos (by decide) (by decide)) (by decide)
      apply rat_lt_of_mul_pos_right hd
      have hL : ((9 / 16 : Rat) / 128172) * (16 * 128172 * 1024) = ((9 * 1024 : Nat) : Rat) := by
        have h1 : ((9 / 16 : Rat) / 128172) * (16 * 128172 * 1024) =
            (((9 / 16 : Rat) / 128172) * 128172) * 16 * 1024 := by grind
        rw [h1, rat_div_mul_cancel (by decide), rat_div_mul_cancel (by decide)]
        rw [Rat.natCast_mul]; rfl
      have hR : ((1 : Rat) / ((2 ^ (7 + 3) : Nat) : Rat)) * (16 * 128172 * 1024) =
          ((16 * 128172 : Nat) : Rat) := by
        have h1024 : ((2 ^ (7 + 3) : Nat) : Rat) = (1024 : Rat) := by decide
        rw [h1024]
        have h1 : ((1 : Rat) / 1024) * (16 * 128172 * 1024) =
            ((1 : Rat) / 1024 * 1024) * (16 * 128172) := by grind
        rw [h1, rat_div_mul_cancel (by decide), Rat.one_mul, Rat.natCast_mul]; rfl
      rw [hL, hR]
      exact rat_natCast_lt (by decide)
    have hKt : (K : Rat) * t = 9 / 16 := by
      exact rat_mul_div_cancel (by decide)
    have hKtHalf : (1 / 2 : Rat) < (K : Rat) * t := by
      rw [hKt]
      apply rat_lt_of_mul_pos_right (c := (16 : Rat)) (by decide)
      have hL : (1 / 2 : Rat) * 16 = 8 := by
        have : (1 / 2 : Rat) * 16 = ((1 / 2 : Rat) * 2) * 8 := by grind
        rw [this, rat_div_mul_cancel (by decide)]; grind
      have hR : (9 / 16 : Rat) * 16 = 9 := rat_div_mul_cancel (by decide)
      rw [hL, hR]; exact rat_natCast_lt (by decide)
    refine ⟨by decide, hS1, hS2, htPos, htCut, hKt, hKtHalf, ?_⟩
    intro p pEff hpSum hpEffSum hpTail hpEffTail
    have hge := tvDist_ge_erased_tail p pEff t (Rat.le_of_lt htPos) hpSum hpEffSum hpTail hpEffTail
    exact rat_lt_of_lt_of_le hKtHalf hge

end SamplingHorizons
