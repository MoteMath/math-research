/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FanoSparse24Perm.RatOrder

/-!
# Theorem 1: Universal Structured Top-`k` EF21 Contraction (`α(k:m) = k / m`)

Proves that for any `1 ≤ k ≤ m` and any sorted `m`-block of nonnegative magnitudes
`a 0 ≥ a 1 ≥ ... ≥ a (m - 1) ≥ 0`:
1. `blockEnergy m a = blockKeptEnergy k a + blockPrunedErr k m a`.
2. `(m - k) * blockKeptEnergy k a ≥ k * blockPrunedErr k m a`.
3. `blockPrunedErr k m a ≤ (1 - ef21Alpha k m) * blockEnergy m a`.
4. Multi-block lift: for `g` disjoint `m`-blocks, total pruned error is at most
   `(1 - k / m)` times total energy.
5. Exact tightness: a flat block `a i = c > 0` attains `1 - E / (K + E) = k / m`.
6. Exact instantiations: `2:4`, `4:8`, `8:16` give `1 / 2`; `1:4`, `2:8` give `1 / 4`.
-/

namespace FanoSparse24Perm

theorem blockEnergy_split {k m : Nat} (hkm : k ≤ m) (a : Nat → Rat) :
    blockEnergy m a = blockKeptEnergy k a + blockPrunedErr k m a := by
  unfold blockEnergy blockKeptEnergy blockPrunedErr
  have hm : k + (m - k) = m := Nat.add_sub_of_le hkm
  have hsplit := sumRange_split k (m - k) (fun i => a i * a i)
  rw [hm] at hsplit
  exact hsplit

theorem blockEnergy_nonneg (m : Nat) (a : Nat → Rat) :
    (0 : Rat) ≤ blockEnergy m a := by
  unfold blockEnergy
  exact sumRange_nonneg (fun i _ => rat_sq_nonneg (a i))

theorem blockKeptEnergy_ge_pivot {k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m)
    {a : Nat → Rat} (ha : NonIncreasingMags m a) :
    (k : Rat) * (a (k - 1) * a (k - 1)) ≤ blockKeptEnergy k a := by
  unfold blockKeptEnergy
  rw [← sumRange_const k (a (k - 1) * a (k - 1))]
  apply sumRange_le_sumRange
  intro i hi
  have h1 : i ≤ k - 1 := by omega
  have h2 : k - 1 < m := by omega
  have hle : a (k - 1) ≤ a i := ha.2 i (k - 1) h1 h2
  have hnn : (0 : Rat) ≤ a (k - 1) := ha.1 (k - 1) h2
  exact rat_sq_le_sq hnn hle

theorem blockPrunedErr_le_pivot {k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m)
    {a : Nat → Rat} (ha : NonIncreasingMags m a) :
    blockPrunedErr k m a ≤ ((m - k : Nat) : Rat) * (a (k - 1) * a (k - 1)) := by
  unfold blockPrunedErr
  rw [← sumRange_const (m - k) (a (k - 1) * a (k - 1))]
  apply sumRange_le_sumRange
  intro j hj
  have h1 : k - 1 ≤ k + j := by omega
  have h2 : k + j < m := by omega
  have hle : a (k + j) ≤ a (k - 1) := ha.2 (k - 1) (k + j) h1 h2
  have hnn : (0 : Rat) ≤ a (k + j) := ha.1 (k + j) h2
  exact rat_sq_le_sq hnn hle

theorem cross_ineq_block {k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m)
    {a : Nat → Rat} (ha : NonIncreasingMags m a) :
    (k : Rat) * blockPrunedErr k m a ≤ ((m - k : Nat) : Rat) * blockKeptEnergy k a := by
  have hkept := blockKeptEnergy_ge_pivot hk hkm ha
  have hpruned := blockPrunedErr_le_pivot hk hkm ha
  have h1 : (k : Rat) * blockPrunedErr k m a ≤
      (k : Rat) * (((m - k : Nat) : Rat) * (a (k - 1) * a (k - 1))) :=
    rat_mul_le_mul_of_nonneg_left hpruned (rat_natCast_nonneg k)
  have h2 : ((m - k : Nat) : Rat) * ((k : Rat) * (a (k - 1) * a (k - 1))) ≤
      ((m - k : Nat) : Rat) * blockKeptEnergy k a :=
    rat_mul_le_mul_of_nonneg_left hkept (rat_natCast_nonneg (m - k))
  have hcomm : (k : Rat) * (((m - k : Nat) : Rat) * (a (k - 1) * a (k - 1))) =
      ((m - k : Nat) : Rat) * ((k : Rat) * (a (k - 1) * a (k - 1))) := by grind
  rw [hcomm] at h1
  exact Rat.le_trans h1 h2

theorem block_pruned_le_contraction {k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m)
    {a : Nat → Rat} (ha : NonIncreasingMags m a) :
    blockPrunedErr k m a ≤ (1 - ef21Alpha k m) * blockEnergy m a := by
  have hm_pos : (0 : Rat) < (m : Rat) := rat_natCast_pos (by omega)
  have hm_ne : (m : Rat) ≠ 0 := Rat.ne_of_gt hm_pos
  have hsplit := blockEnergy_split hkm a
  have hcross := cross_ineq_block hk hkm ha
  have hmk_cast : ((m - k : Nat) : Rat) + (k : Rat) = (m : Rat) := by
    rw [← Rat.natCast_add]
    have hnat : m - k + k = m := Nat.sub_add_cancel hkm
    rw [hnat]
  have hmul : blockPrunedErr k m a * (m : Rat) ≤
      ((1 - ef21Alpha k m) * blockEnergy m a) * (m : Rat) := by
    have h1 : (1 - ef21Alpha k m) * (m : Rat) = ((m - k : Nat) : Rat) := by
      unfold ef21Alpha
      have hdiv : ((k : Rat) / (m : Rat)) * (m : Rat) = (k : Rat) := rat_div_mul_cancel hm_ne
      grind
    have h2 : ((1 - ef21Alpha k m) * blockEnergy m a) * (m : Rat) =
        ((m - k : Nat) : Rat) * (blockKeptEnergy k a + blockPrunedErr k m a) := by
      rw [hsplit]
      have : ((1 - ef21Alpha k m) * (blockKeptEnergy k a + blockPrunedErr k m a)) * (m : Rat) =
          ((1 - ef21Alpha k m) * (m : Rat)) * (blockKeptEnergy k a + blockPrunedErr k m a) := by grind
      rw [this, h1]
    rw [h2]
    have h3 : blockPrunedErr k m a * (m : Rat) =
        ((m - k : Nat) : Rat) * blockPrunedErr k m a + (k : Rat) * blockPrunedErr k m a := by
      rw [← hmk_cast]; grind
    have h4 : ((m - k : Nat) : Rat) * (blockKeptEnergy k a + blockPrunedErr k m a) =
        ((m - k : Nat) : Rat) * blockPrunedErr k m a + ((m - k : Nat) : Rat) * blockKeptEnergy k a := by
      grind
    rw [h3, h4]
    exact rat_add_le_add Rat.le_refl hcross
  exact rat_le_of_mul_pos_right hm_pos hmul

theorem multiblock_pruned_le_contraction {g k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m)
    {x : Nat → Nat → Rat} (hx : ∀ r : Nat, r < g → NonIncreasingMags m (x r)) :
    sumRange g (fun r => blockPrunedErr k m (x r)) ≤
      (1 - ef21Alpha k m) * sumRange g (fun r => blockEnergy m (x r)) := by
  rw [← sumRange_mul_left]
  exact sumRange_le_sumRange (fun r hr => block_pruned_le_contraction hk hkm (hx r hr))

theorem flat_block_attains_ef21Alpha {k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m)
    {c : Rat} (hc : (0 : Rat) < c) :
    NonIncreasingMags m (fun _ => c) ∧
    (0 : Rat) < blockEnergy m (fun _ => c) ∧
    1 - blockPrunedErr k m (fun _ => c) / blockEnergy m (fun _ => c) = ef21Alpha k m := by
  have hm_pos : (0 : Rat) < (m : Rat) := rat_natCast_pos (by omega)
  have hc2_pos : (0 : Rat) < c * c := rat_mul_pos hc hc
  have hE : blockEnergy m (fun _ => c) = (m : Rat) * (c * c) := by
    unfold blockEnergy
    exact sumRange_const m (c * c)
  have hP : blockPrunedErr k m (fun _ => c) = ((m - k : Nat) : Rat) * (c * c) := by
    unfold blockPrunedErr
    exact sumRange_const (m - k) (c * c)
  have hE_pos : (0 : Rat) < blockEnergy m (fun _ => c) := by
    rw [hE]
    exact rat_mul_pos hm_pos hc2_pos
  refine ⟨⟨fun _ _ => Rat.le_of_lt hc, fun _ _ _ _ => Rat.le_refl⟩, hE_pos, ?_⟩
  have hE_ne : blockEnergy m (fun _ => c) ≠ 0 := Rat.ne_of_gt hE_pos
  have hm_ne : (m : Rat) ≠ 0 := Rat.ne_of_gt hm_pos
  have hmk_cast : ((m - k : Nat) : Rat) + (k : Rat) = (m : Rat) := by
    rw [← Rat.natCast_add]
    have hnat : m - k + k = m := Nat.sub_add_cancel hkm
    rw [hnat]
  have hratio : blockPrunedErr k m (fun _ => c) / blockEnergy m (fun _ => c) =
      ((m - k : Nat) : Rat) / (m : Rat) := by
    apply rat_div_eq_of_cross hE_ne hm_ne
    rw [hP, hE]
    grind
  rw [hratio]
  unfold ef21Alpha
  have hsum : ((m - k : Nat) : Rat) / (m : Rat) + (k : Rat) / (m : Rat) = 1 := by
    have h1 : (((m - k : Nat) : Rat) / (m : Rat) + (k : Rat) / (m : Rat)) * (m : Rat) = (m : Rat) := by
      have ha := rat_div_mul_cancel (a := ((m - k : Nat) : Rat)) hm_ne
      have hb := rat_div_mul_cancel (a := (k : Rat)) hm_ne
      grind
    have h2 : (((m - k : Nat) : Rat) / (m : Rat) + (k : Rat) / (m : Rat) - 1) * (m : Rat) = 0 := by
      grind
    cases Rat.mul_eq_zero.mp h2 with
    | inl h0 => grind
    | inr hm0 => exact False.elim (hm_ne hm0)
  grind

/-- Headline Theorem 1: Universal Structured Top-`k` EF21 Contraction Law (`α(k:m) = k / m`). -/
theorem structured_topk_ef21_contraction_exact :
    (∀ (k m : Nat) (a : Nat → Rat), 1 ≤ k → k ≤ m → NonIncreasingMags m a →
      blockEnergy m a = blockKeptEnergy k a + blockPrunedErr k m a ∧
      blockPrunedErr k m a ≤ (1 - ef21Alpha k m) * blockEnergy m a) ∧
    (∀ (g k m : Nat) (x : Nat → Nat → Rat), 1 ≤ k → k ≤ m →
      (∀ r : Nat, r < g → NonIncreasingMags m (x r)) →
      sumRange g (fun r => blockPrunedErr k m (x r)) ≤
        (1 - ef21Alpha k m) * sumRange g (fun r => blockEnergy m (x r))) ∧
    (∀ (k m : Nat) (c : Rat), 1 ≤ k → k ≤ m → (0 : Rat) < c →
      NonIncreasingMags m (fun _ => c) ∧
      (0 : Rat) < blockEnergy m (fun _ => c) ∧
      1 - blockPrunedErr k m (fun _ => c) / blockEnergy m (fun _ => c) = ef21Alpha k m) ∧
    (ef21Alpha 2 4 = 1 / 2 ∧ ef21Alpha 4 8 = 1 / 2 ∧ ef21Alpha 8 16 = 1 / 2 ∧
     ef21Alpha 1 4 = 1 / 4 ∧ ef21Alpha 2 8 = 1 / 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k m a hk hkm ha
    exact ⟨blockEnergy_split hkm a, block_pruned_le_contraction hk hkm ha⟩
  · intro g k m x hk hkm hx
    exact multiblock_pruned_le_contraction hk hkm hx
  · intro k m c hk hkm hc
    exact flat_block_attains_ef21Alpha hk hkm hc
  · unfold ef21Alpha; grind

end FanoSparse24Perm
