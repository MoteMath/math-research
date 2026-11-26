/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AllReduceXorVdc.RatBasic

/-!
# Pillar 1: Exact Quantized All-Reduce Topology Error Laws & Ternary Saturation Barrier

Proves:
- Theorem 1 (`allreduce_subulp_drift_ring_vs_tree_exact`): Exact `(TP - 1)`-fold separation
  between sequential Ring RNE and Binary-Tree / Direct accumulation on adversarial sub-ULP drift
  (e.g., `63x` at `TP = 64`).
- Theorem 2 (`allreduce_cancel_wipeout_ring_vs_tree_exact`): Exact combinatorial catastrophic-
  cancellation wipeout law: Ring `2 / TP` vs Binary-Tree `TP / (2 * (TP - 1)) > 1/2` (strictly
  worse than Ring for all `TP = 2h ≥ 4`, reaching `1024/63 > 16x` at `TP = 64`) vs Direct `0`.
- Theorem 6 (`fixed_scale_ternary_saturation_barrier`): Exact fixed-scale ternary saturation at
  `±S` identically across Ring, Tree, and Direct topologies (`1x` ratio; universal barrier for
  any sum exceeding `S`).
-/

namespace AllReduceXorVdc

/-! ### Part A: Theorem 1 — Exact Sub-ULP Drift Law -/

theorem exactSubUlpSum_eq (p tp : Nat) (htp : 1 ≤ tp) :
    exactSubUlpSum p tp = 1 + ((tp - 1 : Nat) : Rat) * (dyadicUlp p / 2) := by
  unfold exactSubUlpSum
  induction tp with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp [sumRange, subUlpInput, Rat.zero_add, Rat.add_zero]
    | succ m =>
      have hm : 1 ≤ m + 1 := by omega
      change sumRange (m + 1) (subUlpInput (dyadicUlp p)) + subUlpInput (dyadicUlp p) (m + 1) = _
      rw [ih hm]
      have hne : m + 1 ≠ 0 := by omega
      simp only [subUlpInput, hne, ↓reduceIte]
      have hcast : ((m + 1 : Nat) : Rat) = (m : Rat) + 1 := by
        rw [rat_natCast_add]; rfl
      have hsub1 : m + 1 - 1 = m := by omega
      have hsub2 : m + 1 + 1 - 1 = m + 1 := by omega
      rw [hsub1, hsub2, hcast]
      grind

theorem rneAdd_one_half_ulp (p : Nat) (hp : 1 ≤ p) :
    rneAdd (dyadicUlp p) 1 (dyadicUlp p / 2) = 1 := by
  unfold rneAdd rneGrid dyadicUlp
  have hpow_ne : ((2 ^ p : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero p
  have hdiv : (1 + (1 : Rat) / ((2 ^ p : Nat) : Rat) / 2) / ((1 : Rat) / ((2 ^ p : Nat) : Rat)) =
      (((2 ^ p : Nat) : Int) : Rat) + (1 : Rat) / 2 := by
    have h1 : ((1 : Rat) / ((2 ^ p : Nat) : Rat))⁻¹ = ((2 ^ p : Nat) : Rat) := by
      rw [Rat.div_def, Rat.one_mul, Rat.inv_inv]
    rw [Rat.div_def, h1]
    have hmul : ((1 : Rat) / ((2 ^ p : Nat) : Rat)) * ((2 ^ p : Nat) : Rat) = 1 := by
      rw [Rat.div_def, Rat.one_mul, Rat.inv_mul_cancel _ hpow_ne]
    have h2 : (1 + (1 : Rat) / ((2 ^ p : Nat) : Rat) / 2) * ((2 ^ p : Nat) : Rat) =
        ((2 ^ p : Nat) : Rat) + (((1 : Rat) / ((2 ^ p : Nat) : Rat)) * ((2 ^ p : Nat) : Rat)) / 2 := by
      grind
    rw [h2, hmul]
    rfl
  have heven : ((2 ^ p : Nat) : Int) % 2 = 0 := by
    have hp1 : p = (p - 1) + 1 := by omega
    have hnat : 2 ^ p % 2 = 0 := by
      rw [hp1, Nat.pow_succ]; omega
    omega
  rw [hdiv, rneInt_int_add_half_even heven]
  have hcast : (((2 ^ p : Nat) : Int) : Rat) = ((2 ^ p : Nat) : Rat) := rfl
  rw [hcast, Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ hpow_ne]

theorem ringSubUlpOut_eq_one (p tp : Nat) (hp : 1 ≤ p) (htp : 1 ≤ tp) :
    ringSubUlpOut p tp = 1 := by
  unfold ringSubUlpOut
  induction tp with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp [ringReduceFn, subUlpInput]
    | succ m =>
      simp only [ringReduceFn]
      rw [ih (by omega)]
      have hne : m + 1 ≠ 0 := by omega
      simp only [subUlpInput, hne, ↓reduceIte]
      exact rneAdd_one_half_ulp p hp

theorem ringSubUlpErr_exact (p tp : Nat) (hp : 1 ≤ p) (htp : 1 ≤ tp) :
    ringSubUlpErr p tp = ((tp - 1 : Nat) : Rat) * (dyadicUlp p / 2) := by
  unfold ringSubUlpErr
  rw [ringSubUlpOut_eq_one p tp hp htp, exactSubUlpSum_eq p tp htp]
  have hsub : 1 - (1 + ((tp - 1 : Nat) : Rat) * (dyadicUlp p / 2)) =
      -(((tp - 1 : Nat) : Rat) * (dyadicUlp p / 2)) := by grind
  rw [hsub, absRat_neg]
  apply absRat_of_nonneg
  exact Rat.mul_nonneg (rat_natCast_le_natCast (Nat.zero_le _))
    (Rat.le_of_lt (rat_div_pos (dyadicUlp_pos p) (by decide)))

/-- Helper: balanced binary tree on `2^k` copies of `u / 2` (`k ≥ 1`) equals `2^(k - 1) * u` exactly. -/
theorem treeReduce_half_ulp_exact (p k : Nat) (hk : 1 ≤ k) :
    treeReduce (rneAdd (dyadicUlp p)) k (fun _ => dyadicUlp p / 2) =
    ((2 ^ (k - 1) : Nat) : Rat) * dyadicUlp p := by
  induction k with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      simp only [treeReduce, rneAdd]
      have hadd : dyadicUlp p / 2 + dyadicUlp p / 2 = ((1 : Int) : Rat) * dyadicUlp p := by grind
      rw [hadd, rneGrid_int_mul (dyadicUlp_pos p) 1]
      simp
    | succ r =>
      change rneAdd (dyadicUlp p)
        (treeReduce (rneAdd (dyadicUlp p)) (r + 1) (fun _ => dyadicUlp p / 2))
        (treeReduce (rneAdd (dyadicUlp p)) (r + 1) (fun _ => dyadicUlp p / 2)) = _
      rw [ih (by omega)]
      unfold rneAdd
      have hsub1 : r + 1 - 1 = r := by omega
      have hsub2 : r + 1 + 1 - 1 = r + 1 := by omega
      rw [hsub1, hsub2]
      have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [Nat.pow_succ]; omega
      have hadd : ((2 ^ r : Nat) : Rat) * dyadicUlp p + ((2 ^ r : Nat) : Rat) * dyadicUlp p =
          (((2 ^ (r + 1) : Nat) : Int) : Rat) * dyadicUlp p := by
        have hc : (((2 ^ (r + 1) : Nat) : Int) : Rat) = ((2 ^ r : Nat) : Rat) + ((2 ^ r : Nat) : Rat) := by
          rw [show (((2 ^ (r + 1) : Nat) : Int) : Rat) = ((2 ^ (r + 1) : Nat) : Rat) by rfl, hpow]
          exact rat_natCast_add _ _
        rw [hc]; grind
      rw [hadd, rneGrid_int_mul (dyadicUlp_pos p)]
      rfl

/-- Balanced binary tree on `[1, u/2, ..., u/2]` of length `2^k` (`k ≥ 1`) equals
    `1 + (2^(k - 1) - 1) * u`. -/
theorem treeSubUlpOut_exact (p k : Nat) (hp : 1 ≤ p) (hk : 1 ≤ k) :
    treeSubUlpOut p k = 1 + ((2 ^ (k - 1) - 1 : Nat) : Rat) * dyadicUlp p := by
  unfold treeSubUlpOut
  induction k with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      simp only [treeReduce, subUlpInput]
      have h1 : (0 + 2 ^ 0 : Nat) ≠ 0 := by omega
      simp only [h1, ↓reduceIte]
      rw [rneAdd_one_half_ulp p hp]
      simp [Rat.add_zero]
    | succ r =>
      change rneAdd (dyadicUlp p)
        (treeReduce (rneAdd (dyadicUlp p)) (r + 1) (subUlpInput (dyadicUlp p)))
        (treeReduce (rneAdd (dyadicUlp p)) (r + 1) (fun i => subUlpInput (dyadicUlp p) (i + 2 ^ (r + 1)))) = _
      have hright : (fun i => subUlpInput (dyadicUlp p) (i + 2 ^ (r + 1))) =
          (fun _ => dyadicUlp p / 2) := by
        funext i
        have hne : i + 2 ^ (r + 1) ≠ 0 := by
          have := Nat.two_pow_pos (r + 1); omega
        simp [subUlpInput]
      rw [ih (by omega), hright, treeReduce_half_ulp_exact p (r + 1) (by omega)]
      unfold rneAdd
      have hsub1 : r + 1 - 1 = r := by omega
      have hsub2 : r + 1 + 1 - 1 = r + 1 := by omega
      rw [hsub1, hsub2]
      have h1_eq : (1 : Rat) = ((2 ^ p : Nat) : Rat) * dyadicUlp p := by
        unfold dyadicUlp
        rw [Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ (rat_pow2_ne_zero p)]
      have h2r_pos : 1 ≤ 2 ^ r := Nat.two_pow_pos r
      have hpow : 2 ^ (r + 1) - 1 = (2 ^ r - 1) + 2 ^ r := by
        have hp2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [Nat.pow_succ]; omega
        omega
      have hsum :
          (1 + ((2 ^ r - 1 : Nat) : Rat) * dyadicUlp p) + ((2 ^ r : Nat) : Rat) * dyadicUlp p =
          (((2 ^ p + (2 ^ (r + 1) - 1) : Nat) : Int) : Rat) * dyadicUlp p := by
        rw [hpow, h1_eq]
        have hcast : (((2 ^ p + ((2 ^ r - 1) + 2 ^ r) : Nat) : Int) : Rat) =
            ((2 ^ p : Nat) : Rat) + ((2 ^ r - 1 : Nat) : Rat) + ((2 ^ r : Nat) : Rat) := by
          rw [show (((2 ^ p + ((2 ^ r - 1) + 2 ^ r) : Nat) : Int) : Rat) =
              ((2 ^ p + ((2 ^ r - 1) + 2 ^ r) : Nat) : Rat) by rfl]
          rw [rat_natCast_add, rat_natCast_add]
          grind
        rw [hcast]
        grind
      rw [hsum, rneGrid_int_mul (dyadicUlp_pos p)]
      rw [h1_eq]
      have hcast2 : (((2 ^ p + (2 ^ (r + 1) - 1) : Nat) : Int) : Rat) =
          ((2 ^ p : Nat) : Rat) + ((2 ^ (r + 1) - 1 : Nat) : Rat) := by
        rw [show (((2 ^ p + (2 ^ (r + 1) - 1) : Nat) : Int) : Rat) =
            ((2 ^ p + (2 ^ (r + 1) - 1) : Nat) : Rat) by rfl]
        exact rat_natCast_add _ _
      rw [hcast2]
      grind

theorem treeSubUlpErr_exact (p k : Nat) (hp : 1 ≤ p) (hk : 1 ≤ k) :
    treeSubUlpErr p k = dyadicUlp p / 2 := by
  unfold treeSubUlpErr
  have h2k : 1 ≤ 2 ^ k := Nat.two_pow_pos k
  rw [treeSubUlpOut_exact p k hp hk, exactSubUlpSum_eq p (2 ^ k) h2k]
  have h2k_eq : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv => lhs; rw [hk1, Nat.pow_succ]
    omega
  have h1le : 1 ≤ 2 ^ (k - 1) := Nat.two_pow_pos (k - 1)
  have hnat : 2 ^ k - 1 = 2 * (2 ^ (k - 1) - 1) + 1 := by omega
  have hcast : ((2 ^ k - 1 : Nat) : Rat) = 2 * ((2 ^ (k - 1) - 1 : Nat) : Rat) + 1 := by
    rw [hnat, rat_natCast_add, rat_natCast_mul]
    rfl
  rw [hcast]
  have hdiff :
      (1 + ((2 ^ (k - 1) - 1 : Nat) : Rat) * dyadicUlp p) -
      (1 + (2 * ((2 ^ (k - 1) - 1 : Nat) : Rat) + 1) * (dyadicUlp p / 2)) =
      -(dyadicUlp p / 2) := by grind
  rw [hdiff, absRat_neg]
  exact absRat_of_nonneg (Rat.le_of_lt (rat_div_pos (dyadicUlp_pos p) (by decide)))

theorem directSubUlpErr_le_half (p tp : Nat) :
    directSubUlpErr p tp ≤ dyadicUlp p / 2 := by
  unfold directSubUlpErr directSubUlpOut directReduce exactSubUlpSum
  have hneg : absRat (rneGrid (dyadicUlp p) (sumRange tp (subUlpInput (dyadicUlp p))) -
      sumRange tp (subUlpInput (dyadicUlp p))) =
      absRat (sumRange tp (subUlpInput (dyadicUlp p)) -
        rneGrid (dyadicUlp p) (sumRange tp (subUlpInput (dyadicUlp p)))) := by
    have h : rneGrid (dyadicUlp p) (sumRange tp (subUlpInput (dyadicUlp p))) -
        sumRange tp (subUlpInput (dyadicUlp p)) =
        -(sumRange tp (subUlpInput (dyadicUlp p)) -
          rneGrid (dyadicUlp p) (sumRange tp (subUlpInput (dyadicUlp p)))) := by grind
    rw [h, absRat_neg]
  rw [hneg]
  exact absRat_sub_rneGrid_le_half (dyadicUlp_pos p) (sumRange tp (subUlpInput (dyadicUlp p)))

theorem directSubUlpErr_even_exact (p tp : Nat) (htp : 2 ≤ tp) (heven : tp % 2 = 0) :
    directSubUlpErr p tp = dyadicUlp p / 2 := by
  unfold directSubUlpErr directSubUlpOut directReduce
  have hsum_val : sumRange tp (subUlpInput (dyadicUlp p)) =
      1 + ((tp - 1 : Nat) : Rat) * (dyadicUlp p / 2) :=
    exactSubUlpSum_eq p tp (by omega)
  change absRat (rneGrid (dyadicUlp p) (sumRange tp (subUlpInput (dyadicUlp p))) -
      sumRange tp (subUlpInput (dyadicUlp p))) = dyadicUlp p / 2
  rw [hsum_val]
  let m : Nat := (tp - 2) / 2
  have htp_eq : tp - 1 = 2 * m + 1 := by omega
  have hu_ne : dyadicUlp p ≠ 0 := dyadicUlp_ne_zero p
  have h1_eq : (1 : Rat) = ((2 ^ p : Nat) : Rat) * dyadicUlp p := by
    unfold dyadicUlp
    rw [Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ (rat_pow2_ne_zero p)]
  have hsum_eq : 1 + ((tp - 1 : Nat) : Rat) * (dyadicUlp p / 2) =
      ((((2 ^ p + m : Nat) : Int) : Rat) + (1 : Rat) / 2) * dyadicUlp p := by
    rw [htp_eq, h1_eq]
    have hc1 : ((2 * m + 1 : Nat) : Rat) = 2 * (m : Rat) + 1 := by
      rw [rat_natCast_add, rat_natCast_mul]; rfl
    have hc2 : (((2 ^ p + m : Nat) : Int) : Rat) = ((2 ^ p : Nat) : Rat) + (m : Rat) := by
      rw [show (((2 ^ p + m : Nat) : Int) : Rat) = ((2 ^ p + m : Nat) : Rat) by rfl]
      exact rat_natCast_add _ _
    rw [hc1, hc2]
    grind
  rw [hsum_eq]
  unfold rneGrid
  have hdiv : ((((2 ^ p + m : Nat) : Int) : Rat) + (1 : Rat) / 2) * dyadicUlp p / dyadicUlp p =
      (((2 ^ p + m : Nat) : Int) : Rat) + (1 : Rat) / 2 := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.mul_inv_cancel _ hu_ne, Rat.mul_one]
  rw [hdiv]
  by_cases hev : ((2 ^ p + m : Nat) : Int) % 2 = 0
  · rw [rneInt_int_add_half_even hev]
    have hdiff :
        (((2 ^ p + m : Nat) : Int) : Rat) * dyadicUlp p -
        ((((2 ^ p + m : Nat) : Int) : Rat) + (1 : Rat) / 2) * dyadicUlp p =
        -(dyadicUlp p / 2) := by grind
    rw [hdiff, absRat_neg]
    exact absRat_of_nonneg (Rat.le_of_lt (rat_div_pos (dyadicUlp_pos p) (by decide)))
  · rw [rneInt_int_add_half_odd hev]
    have hdiff :
        ((((2 ^ p + m : Nat) : Int) + 1 : Int) : Rat) * dyadicUlp p -
        ((((2 ^ p + m : Nat) : Int) : Rat) + (1 : Rat) / 2) * dyadicUlp p =
        dyadicUlp p / 2 := by
      rw [Rat.intCast_add]
      have h1 : ((1 : Int) : Rat) = 1 := rfl
      rw [h1]; grind
    rw [hdiff]
    exact absRat_of_nonneg (Rat.le_of_lt (rat_div_pos (dyadicUlp_pos p) (by decide)))

/-- **Headline Theorem 1 (Sub-ULP Drift Ring vs Tree/Direct Separation):** -/
theorem allreduce_subulp_drift_ring_vs_tree_exact :
    (∀ (p tp : Nat), 1 ≤ p → 2 ≤ tp →
      ringSubUlpErr p tp = ((tp - 1 : Nat) : Rat) * (dyadicUlp p / 2) ∧
      directSubUlpErr p tp ≤ dyadicUlp p / 2) ∧
    (∀ (p k : Nat), 1 ≤ p → 1 ≤ k →
      treeSubUlpErr p k = dyadicUlp p / 2 ∧
      directSubUlpErr p (2 ^ k) = dyadicUlp p / 2 ∧
      ringSubUlpErr p (2 ^ k) = ((2 ^ k - 1 : Nat) : Rat) * treeSubUlpErr p k ∧
      ringSubUlpErr p (2 ^ k) = ((2 ^ k - 1 : Nat) : Rat) * directSubUlpErr p (2 ^ k)) ∧
    (∀ (p : Nat), 1 ≤ p →
      ringSubUlpErr p 64 = 63 * treeSubUlpErr p 6 ∧
      ringSubUlpErr p 64 = 63 * directSubUlpErr p 64) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p tp hp htp
    exact ⟨ringSubUlpErr_exact p tp hp (by omega), directSubUlpErr_le_half p tp⟩
  · intro p k hp hk
    have h2k : 2 ≤ 2 ^ k := by
      have hk1 : k = (k - 1) + 1 := by omega
      have hpos : 1 ≤ 2 ^ (k - 1) := Nat.two_pow_pos (k - 1)
      rw [hk1, Nat.pow_succ]; omega
    have hev : 2 ^ k % 2 = 0 := by
      have hk1 : k = (k - 1) + 1 := by omega
      rw [hk1, Nat.pow_succ]; omega
    have hring := ringSubUlpErr_exact p (2 ^ k) hp (by omega)
    have htree := treeSubUlpErr_exact p k hp hk
    have hdir := directSubUlpErr_even_exact p (2 ^ k) h2k hev
    refine ⟨htree, hdir, ?_, ?_⟩
    · rw [hring, htree]
    · rw [hring, hdir]
  · intro p hp
    have h6 := ringSubUlpErr_exact p 64 hp (by omega)
    have ht6 := treeSubUlpErr_exact p 6 hp (by omega)
    have hd6 := directSubUlpErr_even_exact p 64 (by omega) (by omega)
    rw [h6, ht6, hd6]
    exact ⟨rfl, rfl⟩

/-! ### Part B: Theorem 2 — Exact Combinatorial Catastrophic-Cancellation Wipeout Law -/

theorem swampAdd_posM_right {M bound s : Rat} (hs : absRat s ≤ bound) :
    swampAdd M bound M s = M := by
  unfold swampAdd
  simp [hs]

theorem swampAdd_posM_left {M bound s : Rat} (hM : (0 : Rat) < M) (hs : absRat s ≤ bound)
    (hbound : bound < M) :
    swampAdd M bound s M = M := by
  unfold swampAdd
  have hne : s ≠ M := by
    intro heq; subst heq
    rw [absRat_of_nonneg (Rat.le_of_lt hM)] at hs
    exact Rat.not_lt.mpr hs hbound
  simp [hne, hs]

theorem swampAdd_negM_right {M bound s : Rat} (hM : (0 : Rat) < M) (hs : absRat s ≤ bound)
    (hbound : bound < M) :
    swampAdd M bound (-M) s = -M := by
  unfold swampAdd
  have h1 : -M ≠ M := by
    intro heq
    have : M = 0 := by grind
    exact Rat.ne_of_gt hM this
  have h2 : s ≠ M := by
    intro heq; subst heq
    rw [absRat_of_nonneg (Rat.le_of_lt hM)] at hs
    exact Rat.not_lt.mpr hs hbound
  simp [h1, h2, hs]

theorem swampAdd_negM_left {M bound s : Rat} (hM : (0 : Rat) < M) (hs : absRat s ≤ bound)
    (hbound : bound < M) :
    swampAdd M bound s (-M) = -M := by
  unfold swampAdd
  have h1 : s ≠ M := by
    intro heq; subst heq
    rw [absRat_of_nonneg (Rat.le_of_lt hM)] at hs
    exact Rat.not_lt.mpr hs hbound
  have h2 : -M ≠ M := by
    intro heq
    have : M = 0 := by grind
    exact Rat.ne_of_gt hM this
  have h3 : s ≠ -M := by
    intro heq; subst heq
    rw [absRat_neg, absRat_of_nonneg (Rat.le_of_lt hM)] at hs
    exact Rat.not_lt.mpr hs hbound
  simp [h1, h2, h3, hs]

theorem swampAdd_posM_negM {M bound : Rat} (hM : (0 : Rat) < M) (hbound : bound < M) :
    swampAdd M bound M (-M) = 0 := by
  unfold swampAdd
  have hnot : ¬ (absRat (-M) ≤ bound) := by
    rw [absRat_neg, absRat_of_nonneg (Rat.le_of_lt hM)]
    exact Rat.not_le.mpr hbound
  have hnot2 : ¬ (absRat M ≤ bound) := by
    rw [absRat_of_nonneg (Rat.le_of_lt hM)]
    exact Rat.not_le.mpr hbound
  simp only [hnot, hnot2, and_false, ↓reduceIte]
  grind

theorem swampAdd_negM_posM {M bound : Rat} (hM : (0 : Rat) < M) (hbound : bound < M) :
    swampAdd M bound (-M) M = 0 := by
  unfold swampAdd
  have hnot : ¬ (absRat (-M) ≤ bound) := by
    rw [absRat_neg, absRat_of_nonneg (Rat.le_of_lt hM)]
    exact Rat.not_le.mpr hbound
  have hnot2 : ¬ (absRat M ≤ bound) := by
    rw [absRat_of_nonneg (Rat.le_of_lt hM)]
    exact Rat.not_le.mpr hbound
  simp only [hnot, hnot2, and_false, ↓reduceIte]
  grind

theorem swampAdd_small {M bound a b : Rat} (hM : (0 : Rat) < M) (hbound : bound < M)
    (ha : absRat a ≤ bound) (hb : absRat b ≤ bound) :
    swampAdd M bound a b = a + b := by
  unfold swampAdd
  have hne : ∀ x : Rat, absRat x ≤ bound → x ≠ M ∧ x ≠ -M := by
    intro x hx
    constructor
    · intro h; subst h
      rw [absRat_of_nonneg (Rat.le_of_lt hM)] at hx
      exact Rat.not_lt.mpr hx hbound
    · intro h; subst h
      rw [absRat_neg, absRat_of_nonneg (Rat.le_of_lt hM)] at hx
      exact Rat.not_lt.mpr hx hbound
  have ⟨ha1, ha2⟩ := hne a ha
  have ⟨hb1, hb2⟩ := hne b hb
  simp [ha1, ha2, hb1, hb2]

/-- Exact prefix evaluation of `ringReduceFn (swampAdd M bound)` on `cancelInput M δ i j`. -/
theorem ringCancelOut_prefix (M bound δ : Rat) (hM : (0 : Rat) < M) (hδ : (0 : Rat) < δ)
    (tp i j : Nat) (hij : i ≠ j) (hbound : ((tp : Rat) * δ) ≤ bound) (hboundM : bound < M) :
    ∀ n, 1 ≤ n → n ≤ tp →
      ringReduceFn (swampAdd M bound) n (cancelInput M δ i j) =
      if n ≤ i ∧ n ≤ j then (n : Rat) * δ
      else if i < n ∧ n ≤ j then M
      else if j < n ∧ n ≤ i then -M
      else ((n - 1 - (if i < j then j else i) : Nat) : Rat) * δ := by
  intro n hn hntp
  have hsmall : ∀ m : Nat, m ≤ tp → absRat ((m : Rat) * δ) ≤ bound := by
    intro m hm
    have hnn : (0 : Rat) ≤ (m : Rat) * δ :=
      Rat.mul_nonneg (rat_natCast_le_natCast (Nat.zero_le m)) (Rat.le_of_lt hδ)
    rw [absRat_of_nonneg hnn]
    exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right (rat_natCast_le_natCast hm) (Rat.le_of_lt hδ)) hbound
  have hδ_le : absRat δ ≤ bound := by
    have h1 := hsmall 1 (by omega)
    have h1d : ((1 : Nat) : Rat) * δ = δ := by grind
    rw [h1d] at h1
    exact h1
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      change cancelInput M δ i j 0 = _
      unfold cancelInput
      by_cases hi0 : 0 = i
      · subst hi0
        have hj1 : 1 ≤ j := by omega
        simp [hj1]
      · by_cases hj0 : 0 = j
        · subst hj0
          have hi1 : 1 ≤ i := by omega
          simp [hi0, hi1]
        · have hi1 : 1 ≤ i := by omega
          have hj1 : 1 ≤ j := by omega
          simp [hi0, hj0, hi1, hj1]
    | succ r =>
      have hr1 : 1 ≤ r + 1 := by omega
      have hrt : r + 1 ≤ tp := by omega
      change swampAdd M bound (ringReduceFn (swampAdd M bound) (r + 1) (cancelInput M δ i j))
        (cancelInput M δ i j (r + 1)) = _
      rw [ih hr1 hrt]
      by_cases hri : r + 1 < i
      · by_cases hrj : r + 1 < j
        · have h1 : r + 1 ≤ i := by omega
          have h2 : r + 1 ≤ j := by omega
          have h3 : r + 1 + 1 ≤ i := by omega
          have h4 : r + 1 + 1 ≤ j := by omega
          have hci : cancelInput M δ i j (r + 1) = δ := by
            unfold cancelInput; simp [show r + 1 ≠ i by omega, show r + 1 ≠ j by omega]
          simp only [h1, h2, h3, h4, and_self, ↓reduceIte, hci]
          rw [swampAdd_small hM hboundM (hsmall (r + 1) hrt) hδ_le]
          rw [rat_natCast_add]; have : ((1 : Nat) : Rat) = 1 := rfl; rw [this]; grind
        · by_cases heqj : r + 1 = j
          · have h1 : r + 1 ≤ i := by omega
            have h2 : r + 1 ≤ j := by omega
            have h3 : ¬ (r + 1 + 1 ≤ j) := by omega
            have h4 : j < r + 1 + 1 := by omega
            have h5 : r + 1 + 1 ≤ i := by omega
            have hci : cancelInput M δ i j (r + 1) = -M := by
              unfold cancelInput
              have hji : j ≠ i := Ne.symm hij
              simp only [heqj, hji, ↓reduceIte]
            simp only [h1, h2, h3, h4, h5, and_self, and_false, ↓reduceIte, hci]
            exact swampAdd_negM_left hM (hsmall (r + 1) hrt) hboundM
          · have h1 : ¬ (r + 1 ≤ j) := by omega
            have h2 : j < r + 1 := by omega
            have h3 : r + 1 ≤ i := by omega
            have h4 : ¬ (r + 1 + 1 ≤ j) := by omega
            have h5 : j < r + 1 + 1 := by omega
            have h6 : r + 1 + 1 ≤ i := by omega
            have hci : cancelInput M δ i j (r + 1) = δ := by
              unfold cancelInput; simp [show r + 1 ≠ i by omega, show r + 1 ≠ j by omega]
            simp only [h1, h2, h3, h4, h5, h6, and_self, and_false, ↓reduceIte, hci]
            exact swampAdd_negM_right hM hδ_le hboundM
      · by_cases heqi : r + 1 = i
        · by_cases hrj : r + 1 < j
          · have h1 : r + 1 ≤ i := by omega
            have h2 : r + 1 ≤ j := by omega
            have h3 : ¬ (r + 1 + 1 ≤ i) := by omega
            have h4 : i < r + 1 + 1 := by omega
            have h5 : r + 1 + 1 ≤ j := by omega
            have hci : cancelInput M δ i j (r + 1) = M := by
              unfold cancelInput; simp [heqi]
            simp only [h1, h2, h3, h4, h5, and_self, false_and, ↓reduceIte, hci]
            exact swampAdd_posM_left hM (hsmall (r + 1) hrt) hboundM
          · have h1 : ¬ (r + 1 ≤ j) := by omega
            have h2 : j < r + 1 := by omega
            have h3 : r + 1 ≤ i := by omega
            have h4 : ¬ (r + 1 + 1 ≤ j) := by omega
            have h5 : ¬ (r + 1 + 1 ≤ i) := by omega
            have hci : cancelInput M δ i j (r + 1) = M := by
              unfold cancelInput; simp [heqi]
            have hmax : (if i < j then j else i) = r + 1 := by
              have : ¬ (i < j) := by omega
              simp [this, heqi]
            simp only [h1, h2, h3, h4, h5, and_self, and_false, ↓reduceIte, hci, hmax]
            rw [swampAdd_negM_posM hM hboundM]
            have hz : r + 1 + 1 - 1 - (r + 1) = 0 := by omega
            rw [hz]; simp
        · by_cases hrj : r + 1 < j
          · have h1 : ¬ (r + 1 ≤ i) := by omega
            have h2 : i < r + 1 := by omega
            have h3 : r + 1 ≤ j := by omega
            have h4 : ¬ (r + 1 + 1 ≤ i) := by omega
            have h5 : i < r + 1 + 1 := by omega
            have h6 : r + 1 + 1 ≤ j := by omega
            have hci : cancelInput M δ i j (r + 1) = δ := by
              unfold cancelInput; simp [show r + 1 ≠ i by omega, show r + 1 ≠ j by omega]
            simp only [h1, h2, h3, h4, h5, h6, and_self, false_and, ↓reduceIte, hci]
            exact swampAdd_posM_right hδ_le
          · by_cases heqj : r + 1 = j
            · have h1 : ¬ (r + 1 ≤ i) := by omega
              have h2 : i < r + 1 := by omega
              have h3 : r + 1 ≤ j := by omega
              have h4 : ¬ (r + 1 + 1 ≤ i) := by omega
              have h5 : ¬ (r + 1 + 1 ≤ j) := by omega
              have hci : cancelInput M δ i j (r + 1) = -M := by
                unfold cancelInput
                have hji : j ≠ i := Ne.symm hij
                simp only [heqj, hji, ↓reduceIte]
              have hmax : (if i < j then j else i) = r + 1 := by
                have : i < j := by omega
                simp [this, heqj]
              simp only [h1, h2, h3, h4, h5, and_self, and_false, false_and, ↓reduceIte, hci, hmax]
              rw [swampAdd_posM_negM hM hboundM]
              have hz : r + 1 + 1 - 1 - (r + 1) = 0 := by omega
              rw [hz]; simp
            · have h1 : ¬ (r + 1 ≤ i) := by omega
              have h2 : ¬ (r + 1 ≤ j) := by omega
              have h3 : ¬ (r + 1 + 1 ≤ i) := by omega
              have h4 : ¬ (r + 1 + 1 ≤ j) := by omega
              have hci : cancelInput M δ i j (r + 1) = δ := by
                unfold cancelInput; simp [show r + 1 ≠ i by omega, show r + 1 ≠ j by omega]
              simp only [h1, h2, h3, h4, and_false, ↓reduceIte, hci]
              have hmle : r + 1 - 1 - (if i < j then j else i) ≤ tp := by omega
              rw [swampAdd_small hM hboundM (hsmall _ hmle) hδ_le]
              have hstep : r + 1 + 1 - 1 - (if i < j then j else i) =
                  (r + 1 - 1 - (if i < j then j else i)) + 1 := by
                split <;> omega
              rw [hstep, rat_natCast_add]
              have : ((1 : Nat) : Rat) = 1 := rfl
              rw [this]; grind

/-- Ring wipes out the signal to exact `0` iff `i = tp - 1 ∨ j = tp - 1`. -/
theorem ringCancelOut_eq_zero_iff (M bound δ : Rat) (hM : (0 : Rat) < M) (hδ : (0 : Rat) < δ)
    (tp i j : Nat) (htp : 2 ≤ tp) (hi : i < tp) (hj : j < tp) (hij : i ≠ j)
    (hbound : ((tp : Rat) * δ) ≤ bound) (hboundM : bound < M) :
    ringCancelOut M bound δ tp i j = 0 ↔ (i = tp - 1 ∨ j = tp - 1) := by
  unfold ringCancelOut
  rw [ringCancelOut_prefix M bound δ hM hδ tp i j hij hbound hboundM tp (by omega) (Nat.le_refl tp)]
  have h1 : ¬ (tp ≤ i ∧ tp ≤ j) := by omega
  have h2 : ¬ (i < tp ∧ tp ≤ j) := by omega
  have h3 : ¬ (j < tp ∧ tp ≤ i) := by omega
  simp only [h1, h2, h3, ↓reduceIte]
  constructor
  · intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl hnat =>
      have hz : tp - 1 - (if i < j then j else i) = 0 := by
        have hcast : (((tp - 1 - (if i < j then j else i) : Nat) : Int) : Rat) = ((0 : Int) : Rat) := hnat
        have hint := Rat.intCast_inj.mp hcast
        omega
      by_cases hlt : i < j
      · simp only [hlt, ↓reduceIte] at hz
        right; omega
      · simp only [hlt, ↓reduceIte] at hz
        left; omega
    | inr hδ0 => exact absurd hδ0 (Rat.ne_of_gt hδ)
  · intro hor
    have hz : tp - 1 - (if i < j then j else i) = 0 := by
      rcases hor with rfl | rfl
      · have : ¬ (tp - 1 < j) := by omega
        simp [this]
      · have : i < tp - 1 := by omega
        simp [this]
    rw [hz]; simp

/-- Tree evaluation helper: a subtree of size `2^k` holding no `±M` outputs `2^k * δ`;
    holding only `+M` outputs `+M`; holding only `-M` outputs `-M`;
    holding both `+M` and `-M` outputs a non-negative multiple `m * δ` with `m ≤ 2^k`. -/
theorem treeReduce_cancel_classify (M bound δ : Rat) (hM : (0 : Rat) < M) (hδ : (0 : Rat) < δ)
    (k : Nat) (hbound : ((2 ^ k : Nat) : Rat) * δ ≤ bound) (hboundM : bound < M) :
    ∀ (off i j : Nat), i ≠ j →
      let out := treeReduce (swampAdd M bound) k (fun r => cancelInput M δ i j (off + r))
      (((i < off ∨ off + 2 ^ k ≤ i) ∧ (j < off ∨ off + 2 ^ k ≤ j)) →
        out = ((2 ^ k : Nat) : Rat) * δ) ∧
      (((off ≤ i ∧ i < off + 2 ^ k) ∧ (j < off ∨ off + 2 ^ k ≤ j)) →
        out = M) ∧
      (((i < off ∨ off + 2 ^ k ≤ i) ∧ (off ≤ j ∧ j < off + 2 ^ k)) →
        out = -M) ∧
      (((off ≤ i ∧ i < off + 2 ^ k) ∧ (off ≤ j ∧ j < off + 2 ^ k)) →
        ∃ m : Nat, m ≤ 2 ^ k ∧ out = (m : Rat) * δ) := by
  induction k with
  | zero =>
    intro off i j hij
    dsimp only
    simp only [treeReduce, cancelInput, Nat.pow_zero, Nat.add_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨hi, hj⟩
      have h1 : off ≠ i := by omega
      have h2 : off ≠ j := by omega
      simp [h1, h2]
    · intro ⟨hi, _⟩
      have h1 : off = i := by omega
      simp [h1]
    · intro ⟨hi, hj⟩
      have h2 : off = j := by omega
      have hji : j ≠ i := Ne.symm hij
      simp [h2, hji]
    · intro ⟨hi, hj⟩
      omega
  | succ k ih =>
    intro off i j hij
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hbk : ((2 ^ k : Nat) : Rat) * δ ≤ bound := by
      have h2k_pos : 1 ≤ 2 ^ k := Nat.two_pow_pos k
      have hle : 2 ^ k ≤ 2 ^ (k + 1) := by omega
      exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right (rat_natCast_le_natCast hle) (Rat.le_of_lt hδ)) hbound
    have hsmall : ∀ m : Nat, m ≤ 2 ^ k → absRat ((m : Rat) * δ) ≤ bound := by
      intro m hm
      have hnn : (0 : Rat) ≤ (m : Rat) * δ :=
        Rat.mul_nonneg (rat_natCast_le_natCast (Nat.zero_le m)) (Rat.le_of_lt hδ)
      rw [absRat_of_nonneg hnn]
      exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right (rat_natCast_le_natCast hm) (Rat.le_of_lt hδ)) hbk
    have ⟨hL0, hLp, hLn, hLb⟩ := ih hbk off i j hij
    have ⟨hR0, hRp, hRn, hRb⟩ := ih hbk (off + 2 ^ k) i j hij
    dsimp only at hL0 hLp hLn hLb hR0 hRp hRn hRb ⊢
    have hshift : (fun r => cancelInput M δ i j (off + (r + 2 ^ k))) =
        (fun r => cancelInput M δ i j ((off + 2 ^ k) + r)) := by
      funext r; congr 1; omega
    have hstep : treeReduce (swampAdd M bound) (k + 1) (fun r => cancelInput M δ i j (off + r)) =
        swampAdd M bound
          (treeReduce (swampAdd M bound) k (fun r => cancelInput M δ i j (off + r)))
          (treeReduce (swampAdd M bound) k (fun r => cancelInput M δ i j ((off + 2 ^ k) + r))) := by
      change swampAdd M bound
        (treeReduce (swampAdd M bound) k (fun r => cancelInput M δ i j (off + r)))
        (treeReduce (swampAdd M bound) k (fun r => cancelInput M δ i j (off + (r + 2 ^ k)))) = _
      rw [hshift]
    rw [hstep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨hi, hj⟩
      rw [hL0 ⟨by omega, by omega⟩, hR0 ⟨by omega, by omega⟩]
      rw [swampAdd_small hM hboundM (hsmall (2 ^ k) (Nat.le_refl _)) (hsmall (2 ^ k) (Nat.le_refl _))]
      rw [hpow, rat_natCast_add]; grind
    · intro ⟨hi, hj⟩
      by_cases hiL : i < off + 2 ^ k
      · rw [hLp ⟨⟨hi.1, hiL⟩, by omega⟩, hR0 ⟨by omega, by omega⟩]
        exact swampAdd_posM_right (hsmall (2 ^ k) (Nat.le_refl _))
      · rw [hL0 ⟨by omega, by omega⟩, hRp ⟨⟨by omega, by omega⟩, by omega⟩]
        exact swampAdd_posM_left hM (hsmall (2 ^ k) (Nat.le_refl _)) hboundM
    · intro ⟨hi, hj⟩
      by_cases hjL : j < off + 2 ^ k
      · rw [hLn ⟨by omega, ⟨hj.1, hjL⟩⟩, hR0 ⟨by omega, by omega⟩]
        exact swampAdd_negM_right hM (hsmall (2 ^ k) (Nat.le_refl _)) hboundM
      · rw [hL0 ⟨by omega, by omega⟩, hRn ⟨by omega, ⟨by omega, by omega⟩⟩]
        exact swampAdd_negM_left hM (hsmall (2 ^ k) (Nat.le_refl _)) hboundM
    · intro ⟨hi, hj⟩
      by_cases hiL : i < off + 2 ^ k
      · by_cases hjL : j < off + 2 ^ k
        · rcases hLb ⟨⟨hi.1, hiL⟩, ⟨hj.1, hjL⟩⟩ with ⟨m, hm, hmEq⟩
          rw [hmEq, hR0 ⟨by omega, by omega⟩]
          rw [swampAdd_small hM hboundM (hsmall m hm) (hsmall (2 ^ k) (Nat.le_refl _))]
          refine ⟨m + 2 ^ k, by omega, ?_⟩
          rw [rat_natCast_add]; grind
        · rw [hLp ⟨⟨hi.1, hiL⟩, by omega⟩, hRn ⟨by omega, ⟨by omega, by omega⟩⟩]
          rw [swampAdd_posM_negM hM hboundM]
          exact ⟨0, Nat.zero_le _, by simp⟩
      · by_cases hjL : j < off + 2 ^ k
        · rw [hLn ⟨by omega, ⟨hj.1, hjL⟩⟩, hRp ⟨⟨by omega, by omega⟩, by omega⟩]
          rw [swampAdd_negM_posM hM hboundM]
          exact ⟨0, Nat.zero_le _, by simp⟩
        · rcases hRb ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩ with ⟨m, hm, hmEq⟩
          rw [hL0 ⟨by omega, by omega⟩, hmEq]
          rw [swampAdd_small hM hboundM (hsmall (2 ^ k) (Nat.le_refl _)) (hsmall m hm)]
          refine ⟨2 ^ k + m, by omega, ?_⟩
          rw [rat_natCast_add]; grind

/-- Binary-Tree (`TP = 2^(k+1)`) wipes out the signal to exact `0` iff `+M` and `-M` land in
    opposite halves of the tree! -/
theorem treeCancelOut_eq_zero_iff (M bound δ : Rat) (hM : (0 : Rat) < M) (hδ : (0 : Rat) < δ)
    (k i j : Nat) (hi : i < 2 ^ (k + 1)) (hj : j < 2 ^ (k + 1)) (hij : i ≠ j)
    (hbound : ((2 ^ (k + 1) : Nat) : Rat) * δ ≤ bound) (hboundM : bound < M) :
    treeCancelOut M bound δ (k + 1) i j = 0 ↔
    ((i < 2 ^ k ∧ 2 ^ k ≤ j) ∨ (j < 2 ^ k ∧ 2 ^ k ≤ i)) := by
  unfold treeCancelOut
  change swampAdd M bound (treeReduce (swampAdd M bound) k (cancelInput M δ i j))
    (treeReduce (swampAdd M bound) k (fun r => cancelInput M δ i j (r + 2 ^ k))) = 0 ↔ _
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hbk : ((2 ^ k : Nat) : Rat) * δ ≤ bound := by
    have hle : 2 ^ k ≤ 2 ^ (k + 1) := by omega
    exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right (rat_natCast_le_natCast hle) (Rat.le_of_lt hδ)) hbound
  have hsmall : ∀ m : Nat, m ≤ 2 ^ k → absRat ((m : Rat) * δ) ≤ bound := by
    intro m hm
    have hnn : (0 : Rat) ≤ (m : Rat) * δ :=
      Rat.mul_nonneg (rat_natCast_le_natCast (Nat.zero_le m)) (Rat.le_of_lt hδ)
    rw [absRat_of_nonneg hnn]
    exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right (rat_natCast_le_natCast hm) (Rat.le_of_lt hδ)) hbk
  have ⟨hL0, hLp, hLn, hLb⟩ := treeReduce_cancel_classify M bound δ hM hδ k hbk hboundM 0 i j hij
  have ⟨hR0, hRp, hRn, hRb⟩ := treeReduce_cancel_classify M bound δ hM hδ k hbk hboundM (2 ^ k) i j hij
  have h0eq : (fun r => cancelInput M δ i j (0 + r)) = cancelInput M δ i j := by
    funext r; simp
  have hRshift : (fun r => cancelInput M δ i j (r + 2 ^ k)) =
      (fun r => cancelInput M δ i j (2 ^ k + r)) := by
    funext r; congr 1; omega
  rw [h0eq] at hL0 hLp hLn hLb
  rw [hRshift]
  by_cases hiL : i < 2 ^ k
  · by_cases hjL : j < 2 ^ k
    · rcases hLb ⟨⟨Nat.zero_le _, by omega⟩, ⟨Nat.zero_le _, by omega⟩⟩ with ⟨m, hm, hmEq⟩
      rw [hmEq, hR0 ⟨by omega, by omega⟩]
      rw [swampAdd_small hM hboundM (hsmall m hm) (hsmall (2 ^ k) (Nat.le_refl _))]
      have hpos : (0 : Rat) < (m : Rat) * δ + ((2 ^ k : Nat) : Rat) * δ := by
        have h1 : (0 : Rat) ≤ (m : Rat) * δ :=
          Rat.mul_nonneg (rat_natCast_le_natCast (Nat.zero_le m)) (Rat.le_of_lt hδ)
        have h2 : (0 : Rat) < ((2 ^ k : Nat) : Rat) * δ := rat_mul_pos (rat_pow2_pos k) hδ
        have h3 := (Rat.add_le_add_right (c := ((2 ^ k : Nat) : Rat) * δ)).mpr h1
        have h0 : (0 : Rat) + ((2 ^ k : Nat) : Rat) * δ = ((2 ^ k : Nat) : Rat) * δ := by grind
        rw [h0] at h3
        exact rat_lt_of_lt_of_le h2 h3
      have hne : (m : Rat) * δ + ((2 ^ k : Nat) : Rat) * δ ≠ 0 := Rat.ne_of_gt hpos
      have hnot : ¬ ((i < 2 ^ k ∧ 2 ^ k ≤ j) ∨ (j < 2 ^ k ∧ 2 ^ k ≤ i)) := by omega
      exact ⟨fun h => absurd h hne, fun h => absurd h hnot⟩
    · rw [hLp ⟨⟨Nat.zero_le _, by omega⟩, by omega⟩, hRn ⟨by omega, ⟨by omega, by omega⟩⟩]
      rw [swampAdd_posM_negM hM hboundM]
      exact ⟨fun _ => Or.inl ⟨hiL, by omega⟩, fun _ => rfl⟩
  · by_cases hjL : j < 2 ^ k
    · rw [hLn ⟨by omega, ⟨Nat.zero_le _, by omega⟩⟩, hRp ⟨⟨by omega, by omega⟩, by omega⟩]
      rw [swampAdd_negM_posM hM hboundM]
      exact ⟨fun _ => Or.inr ⟨hjL, by omega⟩, fun _ => rfl⟩
    · rcases hRb ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩ with ⟨m, hm, hmEq⟩
      rw [hL0 ⟨by omega, by omega⟩, hmEq]
      rw [swampAdd_small hM hboundM (hsmall (2 ^ k) (Nat.le_refl _)) (hsmall m hm)]
      have hpos : (0 : Rat) < ((2 ^ k : Nat) : Rat) * δ + (m : Rat) * δ := by
        have h1 : (0 : Rat) ≤ (m : Rat) * δ :=
          Rat.mul_nonneg (rat_natCast_le_natCast (Nat.zero_le m)) (Rat.le_of_lt hδ)
        have h2 : (0 : Rat) < ((2 ^ k : Nat) : Rat) * δ := rat_mul_pos (rat_pow2_pos k) hδ
        have h3 := (Rat.add_le_add_right (c := ((2 ^ k : Nat) : Rat) * δ)).mpr h1
        have h4 : ((2 ^ k : Nat) : Rat) * δ ≤ ((2 ^ k : Nat) : Rat) * δ + (m : Rat) * δ := by
          rw [Rat.add_comm] at h3
          have h0 : ((2 ^ k : Nat) : Rat) * δ + 0 = ((2 ^ k : Nat) : Rat) * δ := by grind
          rw [h0] at h3
          rw [Rat.add_comm]
          exact h3
        exact rat_lt_of_lt_of_le h2 h4
      have hne : ((2 ^ k : Nat) : Rat) * δ + (m : Rat) * δ ≠ 0 := Rat.ne_of_gt hpos
      have hnot : ¬ ((i < 2 ^ k ∧ 2 ^ k ≤ j) ∨ (j < 2 ^ k ∧ 2 ^ k ≤ i)) := by omega
      exact ⟨fun h => absurd h hne, fun h => absurd h hnot⟩

/-- Direct exact accumulation always equals `(tp - 2) * δ > 0` (zero wipeouts!). -/
theorem directCancelOut_exact (M δ : Rat) (tp i j : Nat)
    (hi : i < tp) (hj : j < tp) (hij : i ≠ j) :
    directCancelOut M δ tp i j = ((tp - 2 : Nat) : Rat) * δ := by
  unfold directCancelOut
  have hsum : ∀ n, sumRange n (cancelInput M δ i j) =
      (n : Rat) * δ +
      (if i < n then M - δ else 0) +
      (if j < n then -M - δ else 0) := by
    intro n
    induction n with
    | zero => simp [sumRange]; grind
    | succ n ih =>
      simp only [sumRange, ih]
      unfold cancelInput
      by_cases hni : n = i
      · subst hni
        have h1 : ¬ (n < n) := by omega
        have h2 : n < n + 1 := by omega
        have h3 : (j < n + 1) ↔ (j < n) := by omega
        simp only [h1, h2, h3, ↓reduceIte]
        rw [rat_natCast_add]; have : ((1 : Nat) : Rat) = 1 := rfl; rw [this]; grind
      · by_cases hnj : n = j
        · subst hnj
          have h1 : ¬ (n < n) := by omega
          have h2 : n < n + 1 := by omega
          have h3 : (i < n + 1) ↔ (i < n) := by omega
          simp only [hni, h1, h2, h3, ↓reduceIte]
          rw [rat_natCast_add]; have : ((1 : Nat) : Rat) = 1 := rfl; rw [this]; grind
        · have h1 : (i < n + 1) ↔ (i < n) := by omega
          have h2 : (j < n + 1) ↔ (j < n) := by omega
          simp only [hni, hnj, h1, h2, ↓reduceIte]
          rw [rat_natCast_add]; have : ((1 : Nat) : Rat) = 1 := rfl; rw [this]; grind
  rw [hsum tp]
  simp only [hi, hj, ↓reduceIte]
  have htp2 : tp = (tp - 2) + 2 := by omega
  have hcast : (tp : Rat) = ((tp - 2 : Nat) : Rat) + 2 := by
    rw [htp2, rat_natCast_add]; rfl
  rw [hcast]; grind

/-- Exact combinatorial count of Ring wipeout placements: `2 * (tp - 1)`. -/
theorem ringWipeoutCount_exact (tp : Nat) (htp : 2 ≤ tp) :
    ringWipeoutCount tp = 2 * (tp - 1) := by
  unfold ringWipeoutCount countOrderedPairs ringWipeoutPred
  have htp1 : tp = (tp - 1) + 1 := by omega
  rw [htp1, sumNatRange_append]
  have hfirst : sumNatRange (tp - 1) (fun i =>
      countRange (tp - 1 + 1) (fun j => decide (i ≠ j) && decide (i = tp - 1 + 1 - 1 ∨ j = tp - 1 + 1 - 1))) =
      tp - 1 := by
    have hcongr : sumNatRange (tp - 1) (fun i =>
        countRange (tp - 1 + 1) (fun j => decide (i ≠ j) && decide (i = tp - 1 + 1 - 1 ∨ j = tp - 1 + 1 - 1))) =
        sumNatRange (tp - 1) (fun _ => 1) := by
      apply sumNatRange_congr
      intro i hi
      have hc : countRange (tp - 1 + 1) (fun j => decide (i ≠ j) && decide (i = tp - 1 + 1 - 1 ∨ j = tp - 1 + 1 - 1)) =
          countRange (tp - 1 + 1) (fun j => decide (j = tp - 1)) := by
        apply countRange_congr
        intro j _
        by_cases hj : j = tp - 1
        · subst hj
          have hne : i ≠ tp - 1 := by omega
          simp [hne]
        · have hne : i ≠ tp - 1 := by omega
          simp [hne, hj]
      rw [hc]
      exact countRange_eq_single (tp - 1 + 1) (tp - 1) (by omega)
    rw [hcongr, sumNatRange_const]; omega
  have hlast : sumNatRange 1 (fun j =>
      countRange (tp - 1 + 1) (fun k =>
        decide (tp - 1 + j ≠ k) && decide (tp - 1 + j = tp - 1 + 1 - 1 ∨ k = tp - 1 + 1 - 1))) =
      tp - 1 := by
    simp only [sumNatRange, Nat.zero_add, Nat.add_zero]
    have hc : countRange (tp - 1 + 1) (fun k =>
        decide (tp - 1 ≠ k) && decide (tp - 1 = tp - 1 + 1 - 1 ∨ k = tp - 1 + 1 - 1)) =
        countRange (tp - 1 + 1) (fun k => decide (tp - 1 ≠ k)) := by
      apply countRange_congr
      intro k _
      simp
    rw [hc, countRange_ne (tp - 1 + 1) (tp - 1) (by omega)]
    omega
  rw [hfirst, hlast]; omega

/-- Exact combinatorial count of Tree opposite-halves wipeout placements: `2 * h * h`. -/
theorem treeWipeoutCount_exact (h : Nat) :
    treeWipeoutCount h = 2 * h * h := by
  unfold treeWipeoutCount countOrderedPairs treeOppositeHalvesPred
  have h2 : 2 * h = h + h := by omega
  rw [h2, sumNatRange_append]
  have hleft : sumNatRange h (fun i =>
      countRange (h + h) (fun j => decide (i ≠ j) && decide ((i < h ∧ h ≤ j) ∨ (j < h ∧ h ≤ i)))) =
      h * h := by
    have hcongr : sumNatRange h (fun i =>
        countRange (h + h) (fun j => decide (i ≠ j) && decide ((i < h ∧ h ≤ j) ∨ (j < h ∧ h ≤ i)))) =
        sumNatRange h (fun _ => h) := by
      apply sumNatRange_congr
      intro i hi
      rw [countRange_append]
      have h0 : countRange h (fun j => decide (i ≠ j) && decide ((i < h ∧ h ≤ j) ∨ (j < h ∧ h ≤ i))) = 0 := by
        rw [countRange_congr (q := fun _ => false) (by intro j hj; simp [show ¬ (h ≤ j) by omega, show ¬ (h ≤ i) by omega])]
        exact countRange_false h
      have h1 : countRange h (fun j => decide (i ≠ h + j) && decide ((i < h ∧ h ≤ h + j) ∨ (h + j < h ∧ h ≤ i))) = h := by
        rw [countRange_congr (q := fun _ => true) (by intro j _; simp [show i ≠ h + j by omega, hi])]
        exact countRange_true h
      rw [h0, h1]; omega
    rw [hcongr, sumNatRange_const]
  have hright : sumNatRange h (fun j =>
      countRange (h + h) (fun k =>
        decide (h + j ≠ k) && decide ((h + j < h ∧ h ≤ k) ∨ (k < h ∧ h ≤ h + j)))) =
      h * h := by
    have hcongr : sumNatRange h (fun j =>
        countRange (h + h) (fun k =>
          decide (h + j ≠ k) && decide ((h + j < h ∧ h ≤ k) ∨ (k < h ∧ h ≤ h + j)))) =
        sumNatRange h (fun _ => h) := by
      apply sumNatRange_congr
      intro j _
      rw [countRange_append]
      have h1 : countRange h (fun k => decide (h + j ≠ k) && decide ((h + j < h ∧ h ≤ k) ∨ (k < h ∧ h ≤ h + j))) = h := by
        rw [countRange_congr (q := fun _ => true) (by intro k hk; simp [show h + j ≠ k by omega, hk])]
        exact countRange_true h
      have h0 : countRange h (fun k => decide (h + j ≠ h + k) && decide ((h + j < h ∧ h ≤ h + k) ∨ (h + k < h ∧ h ≤ h + j))) = 0 := by
        rw [countRange_congr (q := fun _ => false) (by intro k _; simp [show ¬ (h + j < h) by omega, show ¬ (h + k < h) by omega])]
        exact countRange_false h
      rw [h1, h0]; omega
    rw [hcongr, sumNatRange_const]
  rw [hleft, hright]
  have h2hh : (h + h) * h = h * h + h * h := Nat.add_mul h h h
  omega

theorem directWipeoutCount_zero (tp : Nat) : directWipeoutCount tp = 0 := by
  unfold directWipeoutCount countOrderedPairs
  have hcongr : sumNatRange tp (fun i => countRange tp (fun j => decide (i ≠ j) && false)) =
      sumNatRange tp (fun _ => 0) := by
    apply sumNatRange_congr
    intro i _
    simp only [Bool.and_false]
    exact countRange_false tp
  rw [hcongr, sumNatRange_const]; omega

theorem ringWipeoutProb_exact (tp : Nat) (htp : 2 ≤ tp) :
    ringWipeoutProb tp = 2 / (tp : Rat) := by
  unfold ringWipeoutProb
  rw [ringWipeoutCount_exact tp htp, rat_natCast_mul, rat_natCast_mul]
  have htp_ne : (tp : Rat) ≠ 0 := rat_natCast_ne_zero (by omega)
  have htp1_ne : ((tp - 1 : Nat) : Rat) ≠ 0 := rat_natCast_ne_zero (by omega)
  have h2 : ((2 : Nat) : Rat) = 2 := rfl
  rw [h2]
  have hcancel : (2 * ((tp - 1 : Nat) : Rat)) / ((tp : Rat) * ((tp - 1 : Nat) : Rat)) =
      2 / (tp : Rat) := by
    rw [Rat.div_def, Rat.div_def, rat_mul_inv _ _ htp_ne htp1_ne]
    have : 2 * ((tp - 1 : Nat) : Rat) * (((tp - 1 : Nat) : Rat)⁻¹ * (tp : Rat)⁻¹) =
        2 * (((tp - 1 : Nat) : Rat) * ((tp - 1 : Nat) : Rat)⁻¹) * (tp : Rat)⁻¹ := by grind
    rw [this, Rat.mul_inv_cancel _ htp1_ne, Rat.mul_one]
  exact hcancel

theorem treeWipeoutProb_exact (h : Nat) (hh : 1 ≤ h) :
    treeWipeoutProb h = ((2 * h : Nat) : Rat) / (2 * ((2 * h - 1 : Nat) : Rat)) := by
  unfold treeWipeoutProb
  rw [treeWipeoutCount_exact h]
  have h2h_ne : ((2 * h : Nat) : Rat) ≠ 0 := rat_natCast_ne_zero (by omega)
  have h2h1_ne : ((2 * h - 1 : Nat) : Rat) ≠ 0 := rat_natCast_ne_zero (by omega)
  have hnum : ((2 * h * h : Nat) : Rat) = ((2 * h : Nat) : Rat) * (h : Rat) := rat_natCast_mul (2 * h) h
  have hden : (((2 * h) * (2 * h - 1) : Nat) : Rat) = ((2 * h : Nat) : Rat) * ((2 * h - 1 : Nat) : Rat) :=
    rat_natCast_mul (2 * h) (2 * h - 1)
  have h2h : ((2 * h : Nat) : Rat) = 2 * (h : Rat) := by rw [rat_natCast_mul]; rfl
  rw [hnum, hden]
  have h1 : ((2 * h : Nat) : Rat) * (h : Rat) / (((2 * h : Nat) : Rat) * ((2 * h - 1 : Nat) : Rat)) =
      (h : Rat) / ((2 * h - 1 : Nat) : Rat) := by
    rw [Rat.div_def, Rat.div_def, rat_mul_inv _ _ h2h_ne h2h1_ne]
    have : ((2 * h : Nat) : Rat) * (h : Rat) * (((2 * h - 1 : Nat) : Rat)⁻¹ * ((2 * h : Nat) : Rat)⁻¹) =
        (((2 * h : Nat) : Rat) * ((2 * h : Nat) : Rat)⁻¹) * ((h : Rat) * ((2 * h - 1 : Nat) : Rat)⁻¹) := by grind
    rw [this, Rat.mul_inv_cancel _ h2h_ne, Rat.one_mul]
  rw [h1, h2h]
  have h2ne : (2 : Rat) ≠ 0 := by decide
  rw [Rat.div_def, Rat.div_def, rat_mul_inv _ _ h2ne h2h1_ne]
  have : 2 * (h : Rat) * (((2 * h - 1 : Nat) : Rat)⁻¹ * (2 : Rat)⁻¹) =
      (2 * (2 : Rat)⁻¹) * ((h : Rat) * ((2 * h - 1 : Nat) : Rat)⁻¹) := by grind
  rw [this, Rat.mul_inv_cancel _ h2ne, Rat.one_mul]

/-- **Headline Theorem 2 (Exact Combinatorial Catastrophic-Cancellation Wipeout Law):** -/
theorem allreduce_cancel_wipeout_ring_vs_tree_exact :
    (∀ (M bound δ : Rat) (tp i j : Nat),
      (0 : Rat) < M → (0 : Rat) < δ → 2 ≤ tp → i < tp → j < tp → i ≠ j →
      ((tp : Rat) * δ) ≤ bound → bound < M →
      (ringCancelOut M bound δ tp i j = 0 ↔ (i = tp - 1 ∨ j = tp - 1)) ∧
      directCancelOut M δ tp i j = ((tp - 2 : Nat) : Rat) * δ) ∧
    (∀ (M bound δ : Rat) (k i j : Nat),
      (0 : Rat) < M → (0 : Rat) < δ → i < 2 ^ (k + 1) → j < 2 ^ (k + 1) → i ≠ j →
      ((2 ^ (k + 1) : Nat) : Rat) * δ ≤ bound → bound < M →
      (treeCancelOut M bound δ (k + 1) i j = 0 ↔
        ((i < 2 ^ k ∧ 2 ^ k ≤ j) ∨ (j < 2 ^ k ∧ 2 ^ k ≤ i)))) ∧
    (∀ (h : Nat), 2 ≤ h →
      ringWipeoutCount (2 * h) = 2 * (2 * h - 1) ∧
      treeWipeoutCount h = 2 * h * h ∧
      directWipeoutCount (2 * h) = 0 ∧
      ringWipeoutProb (2 * h) = 2 / ((2 * h : Nat) : Rat) ∧
      treeWipeoutProb h = ((2 * h : Nat) : Rat) / (2 * ((2 * h - 1 : Nat) : Rat)) ∧
      directWipeoutProb (2 * h) = 0 ∧
      (1 : Rat) / 2 < treeWipeoutProb h ∧
      ringWipeoutProb (2 * h) < treeWipeoutProb h) ∧
    (ringWipeoutProb 64 = 1 / 32 ∧
     treeWipeoutProb 32 = 32 / 63 ∧
     treeWipeoutProb 32 / ringWipeoutProb 64 = 1024 / 63 ∧
     (16 : Rat) < treeWipeoutProb 32 / ringWipeoutProb 64) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M bound δ tp i j hM hδ htp hi hj hij hb hbm
    exact ⟨ringCancelOut_eq_zero_iff M bound δ hM hδ tp i j htp hi hj hij hb hbm,
           directCancelOut_exact M δ tp i j hi hj hij⟩
  · intro M bound δ k i j hM hδ hi hj hij hb hbm
    exact treeCancelOut_eq_zero_iff M bound δ hM hδ k i j hi hj hij hb hbm
  · intro h hh
    have hrc := ringWipeoutCount_exact (2 * h) (by omega)
    have htc := treeWipeoutCount_exact h
    have hdc := directWipeoutCount_zero (2 * h)
    have hrp := ringWipeoutProb_exact (2 * h) (by omega)
    have htp := treeWipeoutProb_exact h (by omega)
    have hdp : directWipeoutProb (2 * h) = 0 := by
      unfold directWipeoutProb; rw [hdc]; grind
    have hgt_half : (1 : Rat) / 2 < treeWipeoutProb h := by
      rw [htp]
      have hden_pos : (0 : Rat) < 2 * ((2 * h - 1 : Nat) : Rat) :=
        rat_mul_pos (by decide) (rat_natCast_pos (by omega))
      have hlt : ((2 * h - 1 : Nat) : Rat) < ((2 * h : Nat) : Rat) :=
        rat_natCast_lt_natCast (by omega)
      have hhalf : (1 : Rat) / 2 = ((2 * h - 1 : Nat) : Rat) / (2 * ((2 * h - 1 : Nat) : Rat)) := by
        have hne : ((2 * h - 1 : Nat) : Rat) ≠ 0 := rat_natCast_ne_zero (by omega)
        have h2ne : (2 : Rat) ≠ 0 := by decide
        rw [Rat.div_def, Rat.div_def, rat_mul_inv _ _ h2ne hne]
        have : ((2 * h - 1 : Nat) : Rat) * (((2 * h - 1 : Nat) : Rat)⁻¹ * (2 : Rat)⁻¹) =
            (((2 * h - 1 : Nat) : Rat) * ((2 * h - 1 : Nat) : Rat)⁻¹) * (2 : Rat)⁻¹ := by grind
        rw [this, Rat.mul_inv_cancel _ hne]
      rw [hhalf]
      exact rat_div_lt_div_of_pos_right hlt hden_pos
    have hring_lt_tree : ringWipeoutProb (2 * h) < treeWipeoutProb h := by
      rw [hrp]
      have hle_half : 2 / ((2 * h : Nat) : Rat) ≤ (1 : Rat) / 2 := by
        have h4le : (4 : Rat) ≤ ((2 * h : Nat) : Rat) := by
          have : 4 ≤ 2 * h := by omega
          exact rat_natCast_le_natCast this
        have hpos : (0 : Rat) < 2 * ((2 * h : Nat) : Rat) :=
          rat_mul_pos (by decide) (rat_natCast_pos (by omega))
        have hdiv := rat_div_le_div_of_pos_right h4le hpos
        have hl : (4 : Rat) / (2 * ((2 * h : Nat) : Rat)) = 2 / ((2 * h : Nat) : Rat) := by
          have h2ne : (2 : Rat) ≠ 0 := by decide
          have h2hne : ((2 * h : Nat) : Rat) ≠ 0 := rat_natCast_ne_zero (by omega)
          rw [Rat.div_def, Rat.div_def, rat_mul_inv _ _ h2ne h2hne]
          have : (4 : Rat) * (((2 * h : Nat) : Rat)⁻¹ * (2 : Rat)⁻¹) =
              2 * (2 * (2 : Rat)⁻¹) * ((2 * h : Nat) : Rat)⁻¹ := by grind
          rw [this, Rat.mul_inv_cancel _ h2ne, Rat.mul_one]
        have hr : ((2 * h : Nat) : Rat) / (2 * ((2 * h : Nat) : Rat)) = (1 : Rat) / 2 := by
          have hne : ((2 * h : Nat) : Rat) ≠ 0 := rat_natCast_ne_zero (by omega)
          have h2ne : (2 : Rat) ≠ 0 := by decide
          rw [Rat.div_def, Rat.div_def, rat_mul_inv _ _ h2ne hne]
          have : ((2 * h : Nat) : Rat) * (((2 * h : Nat) : Rat)⁻¹ * (2 : Rat)⁻¹) =
              (((2 * h : Nat) : Rat) * ((2 * h : Nat) : Rat)⁻¹) * (2 : Rat)⁻¹ := by grind
          rw [this, Rat.mul_inv_cancel _ hne]
        rw [hl, hr] at hdiv
        exact hdiv
      exact rat_lt_of_le_of_lt hle_half hgt_half
    exact ⟨hrc, htc, hdc, hrp, htp, hdp, hgt_half, hring_lt_tree⟩
  · have hr64 : ringWipeoutProb 64 = 1 / 32 := by
      rw [ringWipeoutProb_exact 64 (by omega)]; grind
    have ht32 : treeWipeoutProb 32 = 32 / 63 := by
      rw [treeWipeoutProb_exact 32 (by omega)]; grind
    rw [hr64, ht32]
    refine ⟨rfl, rfl, by grind, by grind⟩

/-! ### Part C: Theorem 6 — Fixed-Scale Ternary Saturation Barrier -/

theorem ternaryQuant_of_ge {S x : Rat} (hS : (0 : Rat) < S) (hx : S ≤ x) :
    ternaryQuant S x = S := by
  unfold ternaryQuant
  have hhalf : S / 2 ≤ S := by
    apply rat_le_of_sub_nonneg
    have h1 : S - S / 2 = S / 2 := by grind
    rw [h1]
    exact Rat.le_of_lt (rat_div_pos hS (by decide))
  have hge : S / 2 ≤ x := Rat.le_trans hhalf hx
  simp [hge]

theorem ternaryQuant_of_le_neg {S x : Rat} (hS : (0 : Rat) < S) (hx : x ≤ -S) :
    ternaryQuant S x = -S := by
  unfold ternaryQuant
  have hhalf_pos : (0 : Rat) < S / 2 := rat_div_pos hS (by decide)
  have hnot : ¬ (S / 2 ≤ x) := by
    intro hle
    have h1 : S / 2 ≤ -S := Rat.le_trans hle hx
    have h2 : (0 : Rat) < S / 2 + S := rat_add_pos hhalf_pos hS
    have h3 : S / 2 + S ≤ 0 := by
      have := (Rat.add_le_add_right (c := S)).mpr h1
      grind
    exact Rat.not_lt.mpr h3 h2
  have hle_neg : x ≤ -(S / 2) := by
    have h1 : -S ≤ -(S / 2) := by
      apply rat_le_of_sub_nonneg
      have : -(S / 2) - (-S) = S / 2 := by grind
      rw [this]; exact Rat.le_of_lt hhalf_pos
    exact Rat.le_trans hx h1
  simp [hnot, hle_neg]

theorem ringTernaryDrift_eq_S (S : Rat) (hS : (0 : Rat) < S) (tp : Nat) (htp : 1 ≤ tp) :
    ringReduceFn (ternaryAdd S) tp (ternaryDriftInput S) = S := by
  induction tp with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [ringReduceFn, ternaryDriftInput]
    | succ m =>
      simp only [ringReduceFn]
      rw [ih (by omega)]
      have hne : m + 1 ≠ 0 := by omega
      simp only [ternaryDriftInput, hne, ↓reduceIte]
      unfold ternaryAdd
      apply ternaryQuant_of_ge hS
      have hhalf : (0 : Rat) ≤ S / 2 := Rat.le_of_lt (rat_div_pos hS (by decide))
      have := (Rat.add_le_add_right (c := S)).mpr hhalf
      grind

theorem treeTernary_const_nonneg (S : Rat) (hS : (0 : Rat) < S) (k : Nat) :
    (0 : Rat) ≤ treeReduce (ternaryAdd S) k (fun _ => S / 2) := by
  induction k with
  | zero =>
    simp only [treeReduce]
    exact Rat.le_of_lt (rat_div_pos hS (by decide))
  | succ k ih =>
    change (0 : Rat) ≤ ternaryQuant S (treeReduce (ternaryAdd S) k (fun _ => S / 2) +
        treeReduce (ternaryAdd S) k (fun _ => S / 2))
    unfold ternaryQuant
    have hnn : (0 : Rat) ≤ treeReduce (ternaryAdd S) k (fun _ => S / 2) +
        treeReduce (ternaryAdd S) k (fun _ => S / 2) := rat_add_nonneg ih ih
    by_cases h1 : S / 2 ≤ treeReduce (ternaryAdd S) k (fun _ => S / 2) +
        treeReduce (ternaryAdd S) k (fun _ => S / 2)
    · simp only [h1, ↓reduceIte]; exact Rat.le_of_lt hS
    · simp only [h1, ↓reduceIte]
      have h2 : ¬ (treeReduce (ternaryAdd S) k (fun _ => S / 2) +
          treeReduce (ternaryAdd S) k (fun _ => S / 2) ≤ -(S / 2)) := by
        intro hle
        have hpos : (0 : Rat) < S / 2 := rat_div_pos hS (by decide)
        have hlt : -(S / 2) < 0 := by
          have := (Rat.add_lt_add_right (c := -(S / 2))).mpr hpos
          grind
        exact Rat.not_lt.mpr hnn (rat_lt_of_le_of_lt hle hlt)
      simp [h2]

theorem treeTernaryDrift_eq_S (S : Rat) (hS : (0 : Rat) < S) (k : Nat) :
    treeReduce (ternaryAdd S) k (ternaryDriftInput S) = S := by
  induction k with
  | zero => simp [treeReduce, ternaryDriftInput]
  | succ k ih =>
    change ternaryQuant S (treeReduce (ternaryAdd S) k (ternaryDriftInput S) +
        treeReduce (ternaryAdd S) k (fun i => ternaryDriftInput S (i + 2 ^ k))) = S
    have hright : (fun i => ternaryDriftInput S (i + 2 ^ k)) = (fun _ => S / 2) := by
      funext i
      simp [ternaryDriftInput]
    rw [ih, hright]
    apply ternaryQuant_of_ge hS
    have hnn := treeTernary_const_nonneg S hS k
    have := (Rat.add_le_add_right (c := S)).mpr hnn
    grind

theorem exactTernaryDriftSum (S : Rat) (tp : Nat) (htp : 1 ≤ tp) :
    sumRange tp (ternaryDriftInput S) = S + ((tp - 1 : Nat) : Rat) * (S / 2) := by
  induction tp with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [sumRange, ternaryDriftInput, Rat.zero_add, Rat.add_zero]
    | succ m =>
      change sumRange (m + 1) (ternaryDriftInput S) + ternaryDriftInput S (m + 1) = _
      rw [ih (by omega)]
      have hne : m + 1 ≠ 0 := by omega
      simp only [ternaryDriftInput, hne, ↓reduceIte]
      have hsub1 : m + 1 - 1 = m := by omega
      have hsub2 : m + 1 + 1 - 1 = m + 1 := by omega
      rw [hsub1, hsub2, rat_natCast_add]
      have h1 : ((1 : Nat) : Rat) = 1 := rfl
      rw [h1]; grind

theorem directTernaryDrift_eq_S (S : Rat) (hS : (0 : Rat) < S) (tp : Nat) (htp : 1 ≤ tp) :
    directReduce (ternaryQuant S) tp (ternaryDriftInput S) = S := by
  unfold directReduce
  rw [exactTernaryDriftSum S tp htp]
  apply ternaryQuant_of_ge hS
  have hnn : (0 : Rat) ≤ ((tp - 1 : Nat) : Rat) * (S / 2) :=
    Rat.mul_nonneg (rat_natCast_le_natCast (Nat.zero_le _))
      (Rat.le_of_lt (rat_div_pos hS (by decide)))
  have := (Rat.add_le_add_right (c := S)).mpr hnn
  grind

/-- Universal fixed-scale ternary saturation barrier: for ANY sum `x` with `|x| > S`,
    `|ternaryQuant S x - x| ≥ |x| - S > 0`. -/
theorem ternaryQuant_saturation_lower_bound (S x : Rat) (hS : (0 : Rat) < S) (hx : S < absRat x) :
    absRat x - S ≤ absRat (ternaryQuant S x - x) ∧ (0 : Rat) < absRat x - S := by
  have hpos : (0 : Rat) < absRat x - S := rat_sub_pos hx
  refine ⟨?_, hpos⟩
  by_cases hlt : x < 0
  · have hax : absRat x = -x := absRat_of_nonpos (Rat.le_of_lt hlt)
    rw [hax] at hx ⊢
    have hxle : x ≤ -S := by
      have := (Rat.add_lt_add_right (c := x - S)).mpr hx
      exact Rat.le_of_lt (by grind)
    rw [ternaryQuant_of_le_neg hS hxle]
    have hnn : (0 : Rat) ≤ -S - x := by
      have := rat_sub_nonneg hxle; grind
    rw [absRat_of_nonneg hnn]
    have : -x - S = -S - x := by grind
    rw [this]; exact Rat.le_refl
  · have hge : (0 : Rat) ≤ x := Rat.not_lt.mp hlt
    have hax : absRat x = x := absRat_of_nonneg hge
    rw [hax] at hx ⊢
    rw [ternaryQuant_of_ge hS (Rat.le_of_lt hx)]
    have hnp : S - x ≤ 0 := by
      have := rat_sub_pos hx; grind
    rw [absRat_of_nonpos hnp]
    have : -(S - x) = x - S := by grind
    rw [this]; exact Rat.le_refl

/-- **Headline Theorem 6 (Fixed-Scale Ternary Saturation Barrier):** -/
theorem fixed_scale_ternary_saturation_barrier :
    (∀ (S : Rat) (k : Nat), (0 : Rat) < S → 1 ≤ k →
      let exactS := sumRange (2 ^ k) (ternaryDriftInput S)
      let rOut := ringReduceFn (ternaryAdd S) (2 ^ k) (ternaryDriftInput S)
      let tOut := treeReduce (ternaryAdd S) k (ternaryDriftInput S)
      let dOut := directReduce (ternaryQuant S) (2 ^ k) (ternaryDriftInput S)
      rOut = S ∧ tOut = S ∧ dOut = S ∧
      absRat (rOut - exactS) = ((2 ^ k - 1 : Nat) : Rat) * (S / 2) ∧
      absRat (tOut - exactS) = ((2 ^ k - 1 : Nat) : Rat) * (S / 2) ∧
      absRat (dOut - exactS) = ((2 ^ k - 1 : Nat) : Rat) * (S / 2) ∧
      absRat (rOut - exactS) / absRat (tOut - exactS) = 1 ∧
      absRat (rOut - exactS) / absRat (dOut - exactS) = 1) ∧
    (∀ (S x : Rat), (0 : Rat) < S → S < absRat x →
      absRat x - S ≤ absRat (ternaryQuant S x - x) ∧ (0 : Rat) < absRat x - S) := by
  refine ⟨?_, ?_⟩
  · intro S k hS hk
    have h2k : 1 ≤ 2 ^ k := Nat.two_pow_pos k
    have h2k2 : 2 ≤ 2 ^ k := by
      have hk1 : k = (k - 1) + 1 := by omega
      have hpos : 1 ≤ 2 ^ (k - 1) := Nat.two_pow_pos (k - 1)
      rw [hk1, Nat.pow_succ]; omega
    have hr := ringTernaryDrift_eq_S S hS (2 ^ k) h2k
    have ht := treeTernaryDrift_eq_S S hS k
    have hd := directTernaryDrift_eq_S S hS (2 ^ k) h2k
    have hex := exactTernaryDriftSum S (2 ^ k) h2k
    dsimp only
    rw [hr, ht, hd, hex]
    have herr : absRat (S - (S + ((2 ^ k - 1 : Nat) : Rat) * (S / 2))) =
        ((2 ^ k - 1 : Nat) : Rat) * (S / 2) := by
      have hsub : S - (S + ((2 ^ k - 1 : Nat) : Rat) * (S / 2)) =
          -(((2 ^ k - 1 : Nat) : Rat) * (S / 2)) := by grind
      rw [hsub, absRat_neg]
      exact absRat_of_nonneg (Rat.mul_nonneg (rat_natCast_le_natCast (Nat.zero_le _))
        (Rat.le_of_lt (rat_div_pos hS (by decide))))
    have herr_pos : (0 : Rat) < ((2 ^ k - 1 : Nat) : Rat) * (S / 2) :=
      rat_mul_pos (rat_natCast_pos (by omega)) (rat_div_pos hS (by decide))
    have herr_ne : ((2 ^ k - 1 : Nat) : Rat) * (S / 2) ≠ 0 := Rat.ne_of_gt herr_pos
    rw [herr]
    have hdiv1 : (((2 ^ k - 1 : Nat) : Rat) * (S / 2)) / (((2 ^ k - 1 : Nat) : Rat) * (S / 2)) = 1 := by
      rw [Rat.div_def, Rat.mul_inv_cancel _ herr_ne]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hdiv1, hdiv1⟩
  · intro S x hS hx
    exact ternaryQuant_saturation_lower_bound S x hS hx

end AllReduceXorVdc
