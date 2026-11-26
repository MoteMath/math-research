/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FanoSparse24Perm.RatOrder

/-!
# Theorem 5: Exact Order-Statistic `k:2k` Structured Sparsity Gain Laws

Proves:
1. Exact hockey-stick identity `∑_{i=0}^{k-1} (i + 1)(i + 2) = k(k + 1)(k + 2) / 3`
   and universal closed-form Uniform `[-1, 1]` `k:2k` NMSE law:
   `unifNMSEFromOrderStats k = unifNMSE k = (k + 2) / (4 (2k + 1))` for all `k ≥ 1`.
2. Strict monotonicity `unifNMSE (k + 1) < unifNMSE k`, universal lower limit `1 / 8 < unifNMSE k`,
   general doubling gain `1 - unifNMSE (2k) / unifNMSE k = 3k / ((k + 2)(4k + 1))`,
   and exact values (`1:2` = `1/4`, `2:4` = `1/5`, `4:8` = `1/6`, `8:16` = `5/34`, `16:32` = `3/22`;
   `4:8` vs `2:4` = `-1/6`, `8:16` vs `4:8` = `-2/17`).
3. Exact Laplace `(0, 1)` `k:2k` NMSE via Rényi's exponential order-statistic identity:
   `1:2` = `1/8`, `2:4` = `23/288`, `4:8` = `79211/1411200`, `8:16` = `46212449531/1038874636800`,
   with exact `4:8` vs `2:4` gain `33489 / 112700` (`∈ (2971/10000, 2972/10000)`, i.e. `-29.72%`)
   and exact `8:16` vs `4:8` gain `12099837073 / 58312286604` (`∈ (2075/10000, 2076/10000)`).
-/

namespace FanoSparse24Perm

theorem hockey_stick_pair (k : Nat) :
    (3 : Rat) * sumRange k (fun i => (((i + 1) * (i + 2) : Nat) : Rat)) =
      ((k * (k + 1) * (k + 2) : Nat) : Rat) := by
  induction k with
  | zero =>
    simp only [sumRange]
    grind
  | succ k ih =>
    simp only [sumRange]
    have hl : (3 : Rat) * (sumRange k (fun i => (((i + 1) * (i + 2) : Nat) : Rat)) +
        (((k + 1) * (k + 2) : Nat) : Rat)) =
        (3 : Rat) * sumRange k (fun i => (((i + 1) * (i + 2) : Nat) : Rat)) +
        (3 : Rat) * (((k + 1) * (k + 2) : Nat) : Rat) := by grind
    rw [hl, ih]
    simp only [Rat.natCast_mul, Rat.natCast_add]
    grind

theorem unifOrderStatSum_closed (k : Nat) :
    unifOrderStatSum k =
      ((k * (k + 1) * (k + 2) : Nat) : Rat) / ((3 * (2 * k + 1) * (2 * k + 2) : Nat) : Rat) := by
  unfold unifOrderStatSum
  let D : Rat := (((2 * k + 1) * (2 * k + 2) : Nat) : Rat)
  have hD_pos : (0 : Rat) < D := rat_natCast_pos (Nat.mul_pos (by omega) (by omega))
  have hD_ne : D ≠ 0 := Rat.ne_of_gt hD_pos
  have h3D_pos_nat : 0 < 3 * (2 * k + 1) * (2 * k + 2) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have h3D_ne : ((3 * (2 * k + 1) * (2 * k + 2) : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_natCast_pos h3D_pos_nat)
  have hfactor : sumRange k (fun i => (((i + 1) * (i + 2) : Nat) : Rat) / D) =
      (1 / D) * sumRange k (fun i => (((i + 1) * (i + 2) : Nat) : Rat)) := by
    rw [← sumRange_mul_left]
    apply sumRange_congr; intro i _; grind
  rw [hfactor]
  have hhs := hockey_stick_pair k
  have h3D_eq : ((3 * (2 * k + 1) * (2 * k + 2) : Nat) : Rat) = (3 : Rat) * D := by
    simp only [D, Rat.natCast_mul]
    grind
  have hmul : ((1 / D) * sumRange k (fun i => (((i + 1) * (i + 2) : Nat) : Rat))) * ((3 : Rat) * D) =
      (((k * (k + 1) * (k + 2) : Nat) : Rat) / ((3 * (2 * k + 1) * (2 * k + 2) : Nat) : Rat)) *
      ((3 : Rat) * D) := by
    rw [← h3D_eq, rat_div_mul_cancel h3D_ne, h3D_eq]
    have h1 : (1 / D) * D = 1 := rat_div_mul_cancel hD_ne
    grind
  have hsub : (((1 / D) * sumRange k (fun i => (((i + 1) * (i + 2) : Nat) : Rat))) -
      (((k * (k + 1) * (k + 2) : Nat) : Rat) / ((3 * (2 * k + 1) * (2 * k + 2) : Nat) : Rat))) *
      ((3 : Rat) * D) = 0 := by grind
  cases Rat.mul_eq_zero.mp hsub with
  | inl h0 => grind
  | inr hd0 =>
    rw [← h3D_eq] at hd0
    exact False.elim (h3D_ne hd0)

theorem unifNMSEFromOrderStats_eq (k : Nat) (hk : 1 ≤ k) :
    unifNMSEFromOrderStats k = unifNMSE k := by
  unfold unifNMSEFromOrderStats unifNMSE
  rw [unifOrderStatSum_closed k]
  have h3D_ne : ((3 * (2 * k + 1) * (2 * k + 2) : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_natCast_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)))
  have h2k3_ne : ((2 * k : Rat) / 3) ≠ 0 :=
    Rat.ne_of_gt (rat_div_pos (rat_mul_pos (by grind) (rat_natCast_pos (by omega))) (by grind))
  have h4_ne : ((4 * (2 * k + 1) : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_natCast_pos (Nat.mul_pos (by omega) (by omega)))
  apply rat_div_eq_of_cross h2k3_ne h4_ne
  have hmul : (((k * (k + 1) * (k + 2) : Nat) : Rat) / ((3 * (2 * k + 1) * (2 * k + 2) : Nat) : Rat)) *
      ((3 * (2 * k + 1) * (2 * k + 2) : Nat) : Rat) = ((k * (k + 1) * (k + 2) : Nat) : Rat) :=
    rat_div_mul_cancel h3D_ne
  have hcross : (((k * (k + 1) * (k + 2) : Nat) : Rat) / ((3 * (2 * k + 1) * (2 * k + 2) : Nat) : Rat) *
      ((4 * (2 * k + 1) : Nat) : Rat) -
      ((k + 2 : Nat) : Rat) * ((2 * k : Rat) / 3)) * ((3 * (2 * k + 1) * (2 * k + 2) : Nat) : Rat) = 0 := by
    have hcast1 : ((k * (k + 1) * (k + 2) : Nat) : Rat) = (k : Rat) * ((k : Rat) + 1) * ((k : Rat) + 2) := by
      simp only [Rat.natCast_mul, Rat.natCast_add]; grind
    have hcast2 : ((3 * (2 * k + 1) * (2 * k + 2) : Nat) : Rat) =
        3 * (2 * (k : Rat) + 1) * (2 * (k : Rat) + 2) := by
      simp only [Rat.natCast_mul, Rat.natCast_add]; grind
    have hcast3 : ((4 * (2 * k + 1) : Nat) : Rat) = 4 * (2 * (k : Rat) + 1) := by
      simp only [Rat.natCast_mul, Rat.natCast_add]; grind
    have hcast4 : ((k + 2 : Nat) : Rat) = (k : Rat) + 2 := by
      simp only [Rat.natCast_add]; grind
    grind
  cases Rat.mul_eq_zero.mp hcross with
  | inl h0 => grind
  | inr hd0 => exact False.elim (h3D_ne hd0)

theorem unifNMSE_strict_anti (k : Nat) (hk : 1 ≤ k) :
    unifNMSE (k + 1) < unifNMSE k := by
  unfold unifNMSE
  apply rat_div_lt_div_of_cross
    (rat_natCast_pos (Nat.mul_pos (by omega) (by omega)))
    (rat_natCast_pos (Nat.mul_pos (by omega) (by omega)))
  have hnat : (k + 1 + 2) * (4 * (2 * k + 1)) < (k + 2) * (4 * (2 * (k + 1) + 1)) := by
    have h1 : (k + 1 + 2) * (4 * (2 * k + 1)) = 8 * (k * k) + 28 * k + 12 := by grind
    have h2 : (k + 2) * (4 * (2 * (k + 1) + 1)) = 8 * (k * k) + 28 * k + 24 := by grind
    omega
  have hcast := rat_natCast_lt hnat
  rw [Rat.natCast_mul (k + 1 + 2), Rat.natCast_mul (k + 2)] at hcast
  exact hcast

theorem unifNMSE_gt_eighth (k : Nat) : (1 / 8 : Rat) < unifNMSE k := by
  unfold unifNMSE
  apply rat_div_lt_div_of_cross (by grind) (rat_natCast_pos (Nat.mul_pos (by omega) (by omega)))
  have hnat : 1 * (4 * (2 * k + 1)) < (k + 2) * 8 := by omega
  have hcast := rat_natCast_lt hnat
  rw [Rat.natCast_mul 1, Rat.natCast_mul (k + 2)] at hcast
  exact hcast

theorem unifNMSE_doubling_gain (k : Nat) (hk : 1 ≤ k) :
    1 - unifNMSE (2 * k) / unifNMSE k =
      ((3 * k : Nat) : Rat) / (((k + 2) * (4 * k + 1) : Nat) : Rat) := by
  unfold unifNMSE
  have hd1 : ((4 * (2 * (2 * k) + 1) : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_natCast_pos (Nat.mul_pos (by omega) (by omega)))
  have hd2 : ((4 * (2 * k + 1) : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_natCast_pos (Nat.mul_pos (by omega) (by omega)))
  have hd_rhs : (((k + 2) * (4 * k + 1) : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt (rat_natCast_pos (Nat.mul_pos (by omega) (by omega)))
  have hratio : (((2 * k + 2 : Nat) : Rat) / ((4 * (2 * (2 * k) + 1) : Nat) : Rat)) /
      (((k + 2 : Nat) : Rat) / ((4 * (2 * k + 1) : Nat) : Rat)) =
      (((2 * k + 2) * (2 * k + 1) : Nat) : Rat) / (((k + 2) * (4 * k + 1) : Nat) : Rat) := by
    have hdenom_ne : (((k + 2 : Nat) : Rat) / ((4 * (2 * k + 1) : Nat) : Rat)) ≠ 0 :=
      Rat.ne_of_gt (rat_div_pos (rat_natCast_pos (by omega))
        (rat_natCast_pos (Nat.mul_pos (by omega) (by omega))))
    apply rat_div_eq_of_cross hdenom_ne hd_rhs
    have h1 := rat_div_mul_cancel (a := ((2 * k + 2 : Nat) : Rat)) hd1
    have h2 := rat_div_mul_cancel (a := ((k + 2 : Nat) : Rat)) hd2
    have hmul : ((((2 * k + 2 : Nat) : Rat) / ((4 * (2 * (2 * k) + 1) : Nat) : Rat)) *
        (((k + 2) * (4 * k + 1) : Nat) : Rat) -
        (((2 * k + 2) * (2 * k + 1) : Nat) : Rat) *
        (((k + 2 : Nat) : Rat) / ((4 * (2 * k + 1) : Nat) : Rat))) *
        (((4 * (2 * (2 * k) + 1) : Nat) : Rat) * ((4 * (2 * k + 1) : Nat) : Rat)) = 0 := by
      have c1 : ((4 * (2 * (2 * k) + 1) : Nat) : Rat) = 4 * (4 * (k : Rat) + 1) := by
        simp only [Rat.natCast_mul, Rat.natCast_add]; grind
      have c2 : ((4 * (2 * k + 1) : Nat) : Rat) = 4 * (2 * (k : Rat) + 1) := by
        simp only [Rat.natCast_mul, Rat.natCast_add]; grind
      have c3 : (((k + 2) * (4 * k + 1) : Nat) : Rat) = ((k : Rat) + 2) * (4 * (k : Rat) + 1) := by
        simp only [Rat.natCast_mul, Rat.natCast_add]; grind
      have c4 : (((2 * k + 2) * (2 * k + 1) : Nat) : Rat) = (2 * (k : Rat) + 2) * (2 * (k : Rat) + 1) := by
        simp only [Rat.natCast_mul, Rat.natCast_add]; grind
      have c5 : ((2 * k + 2 : Nat) : Rat) = 2 * (k : Rat) + 2 := by
        simp only [Rat.natCast_mul, Rat.natCast_add]; grind
      have c6 : ((k + 2 : Nat) : Rat) = (k : Rat) + 2 := by
        simp only [Rat.natCast_add]; grind
      grind
    cases Rat.mul_eq_zero.mp hmul with
    | inl h0 => grind
    | inr hprod =>
      cases Rat.mul_eq_zero.mp hprod with
      | inl ha => exact False.elim (hd1 ha)
      | inr hb => exact False.elim (hd2 hb)
  rw [hratio]
  have hsub : (1 - (((2 * k + 2) * (2 * k + 1) : Nat) : Rat) / (((k + 2) * (4 * k + 1) : Nat) : Rat) -
      ((3 * k : Nat) : Rat) / (((k + 2) * (4 * k + 1) : Nat) : Rat)) *
      (((k + 2) * (4 * k + 1) : Nat) : Rat) = 0 := by
    have ha := rat_div_mul_cancel (a := (((2 * k + 2) * (2 * k + 1) : Nat) : Rat)) hd_rhs
    have hb := rat_div_mul_cancel (a := ((3 * k : Nat) : Rat)) hd_rhs
    have c1 : (((k + 2) * (4 * k + 1) : Nat) : Rat) = ((k : Rat) + 2) * (4 * (k : Rat) + 1) := by
      simp only [Rat.natCast_mul, Rat.natCast_add]; grind
    have c2 : (((2 * k + 2) * (2 * k + 1) : Nat) : Rat) = (2 * (k : Rat) + 2) * (2 * (k : Rat) + 1) := by
      simp only [Rat.natCast_mul, Rat.natCast_add]; grind
    have c3 : ((3 * k : Nat) : Rat) = 3 * (k : Rat) := by
      simp only [Rat.natCast_mul]; grind
    grind
  cases Rat.mul_eq_zero.mp hsub with
  | inl h0 => grind
  | inr hd0 => exact False.elim (hd_rhs hd0)

theorem laplaceNMSE_1 : laplaceNMSE 1 = 1 / 8 := by
  simp only [laplaceNMSE, harmonicTail1, harmonicTail2, sumRange]
  grind

theorem laplaceNMSE_2 : laplaceNMSE 2 = 23 / 288 := by
  simp only [laplaceNMSE, harmonicTail1, harmonicTail2, sumRange]
  grind

theorem laplaceNMSE_4 : laplaceNMSE 4 = 79211 / 1411200 := by
  simp only [laplaceNMSE, harmonicTail1, harmonicTail2, sumRange]
  grind

theorem laplaceNMSE_8 : laplaceNMSE 8 = 46212449531 / 1038874636800 := by
  simp only [laplaceNMSE, harmonicTail1, harmonicTail2, sumRange]
  grind

/-- Headline Theorem 5: Exact Order-Statistic `k:2k` Gain Laws (Uniform & Laplace). -/
theorem order_statistic_k2k_nmse_laws_exact :
    (∀ k : Nat, 1 ≤ k →
      unifNMSEFromOrderStats k = unifNMSE k ∧
      unifNMSE (k + 1) < unifNMSE k ∧
      (1 / 8 : Rat) < unifNMSE k ∧
      1 - unifNMSE (2 * k) / unifNMSE k =
        ((3 * k : Nat) : Rat) / (((k + 2) * (4 * k + 1) : Nat) : Rat)) ∧
    (unifNMSE 1 = 1 / 4 ∧ unifNMSE 2 = 1 / 5 ∧ unifNMSE 4 = 1 / 6 ∧
     unifNMSE 8 = 5 / 34 ∧ unifNMSE 16 = 3 / 22 ∧
     1 - unifNMSE 4 / unifNMSE 2 = 1 / 6 ∧
     1 - unifNMSE 8 / unifNMSE 4 = 2 / 17) ∧
    (laplaceNMSE 1 = 1 / 8 ∧
     laplaceNMSE 2 = 23 / 288 ∧
     laplaceNMSE 4 = 79211 / 1411200 ∧
     laplaceNMSE 8 = 46212449531 / 1038874636800 ∧
     1 - laplaceNMSE 4 / laplaceNMSE 2 = 33489 / 112700 ∧
     (2971 / 10000 : Rat) < 33489 / 112700 ∧ (33489 / 112700 : Rat) < 2972 / 10000 ∧
     1 - laplaceNMSE 8 / laplaceNMSE 4 = 12099837073 / 58312286604 ∧
     (2075 / 10000 : Rat) < 12099837073 / 58312286604 ∧
       (12099837073 / 58312286604 : Rat) < 2076 / 10000) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    exact ⟨unifNMSEFromOrderStats_eq k hk, unifNMSE_strict_anti k hk,
           unifNMSE_gt_eighth k, unifNMSE_doubling_gain k hk⟩
  · unfold unifNMSE; grind
  · refine ⟨laplaceNMSE_1, laplaceNMSE_2, laplaceNMSE_4, laplaceNMSE_8, ?_, by grind, by grind, ?_, by grind, by grind⟩
    · rw [laplaceNMSE_4, laplaceNMSE_2]; grind
    · rw [laplaceNMSE_8, laplaceNMSE_4]; grind

end FanoSparse24Perm
