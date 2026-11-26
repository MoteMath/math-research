/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EF21Ternary.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exact EF21 Contraction Law & Harmonic Sandwich for Optimal Ternary Compression

Proves:
- `ternary_ef21_contraction_exact`: for all `d ≥ 1`, optimal ternary compression achieves
  EF21 contraction `α_tern(d) = (∑_{i=0}^{d-1} (√(i+1) - √i)^2)⁻¹` for every `x : Fin d → ℝ`
  (via Abel summation by parts), and this constant is attained tightly at `w_i = √(i+1) - √i`.
- `alphaTern_harmonic_sandwich`: for all `d ≥ 1`,
  `4 / (4 + H_{d-1}) ≤ α_tern(d) ≤ 4 / (3 + H_d)`.
-/

namespace EF21Ternary

open scoped BigOperators

private lemma ternaryExtremal_nonneg (d : ℕ) (i : Fin d) : 0 ≤ ternaryExtremal d i := by
  unfold ternaryExtremal
  have h : (i.1 : ℝ) ≤ (i.1 : ℝ) + 1 := by linarith
  linarith [Real.sqrt_le_sqrt h]

private lemma ternaryExtremal_mul_conj (d : ℕ) (i : Fin d) :
    ternaryExtremal d i * (Real.sqrt ((i.1 : ℝ) + 1) + Real.sqrt (i.1 : ℝ)) = 1 := by
  unfold ternaryExtremal
  have h1 : (0 : ℝ) ≤ (i.1 : ℝ) + 1 := by positivity
  have h0 : (0 : ℝ) ≤ (i.1 : ℝ) := by positivity
  calc (Real.sqrt ((i.1 : ℝ) + 1) - Real.sqrt (i.1 : ℝ)) *
        (Real.sqrt ((i.1 : ℝ) + 1) + Real.sqrt (i.1 : ℝ))
      = Real.sqrt ((i.1 : ℝ) + 1) ^ 2 - Real.sqrt (i.1 : ℝ) ^ 2 := by ring
    _ = ((i.1 : ℝ) + 1) - (i.1 : ℝ) := by rw [Real.sq_sqrt h1, Real.sq_sqrt h0]
    _ = 1 := by ring

private lemma ternaryExtremal_eq_inv (d : ℕ) (i : Fin d) :
    ternaryExtremal d i = (Real.sqrt ((i.1 : ℝ) + 1) + Real.sqrt (i.1 : ℝ))⁻¹ := by
  have hpos : 0 < Real.sqrt ((i.1 : ℝ) + 1) + Real.sqrt (i.1 : ℝ) := by
    have h1 : 0 < Real.sqrt ((i.1 : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have h0 : 0 ≤ Real.sqrt (i.1 : ℝ) := Real.sqrt_nonneg _
    linarith
  exact eq_inv_of_mul_eq_one_left (ternaryExtremal_mul_conj d i)

private lemma ternaryExtremal_antitone (d : ℕ) : Antitone (ternaryExtremal d) := by
  intro i j hij
  rw [ternaryExtremal_eq_inv, ternaryExtremal_eq_inv]
  have hpos_i : 0 < Real.sqrt ((i.1 : ℝ) + 1) + Real.sqrt (i.1 : ℝ) := by
    have h1 : 0 < Real.sqrt ((i.1 : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have h0 : 0 ≤ Real.sqrt (i.1 : ℝ) := Real.sqrt_nonneg _
    linarith
  apply inv_anti₀ hpos_i
  have hij' : (i.1 : ℝ) ≤ (j.1 : ℝ) := by exact_mod_cast hij
  have h1 : Real.sqrt ((i.1 : ℝ) + 1) ≤ Real.sqrt ((j.1 : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (i.1 : ℝ) ≤ Real.sqrt (j.1 : ℝ) := Real.sqrt_le_sqrt hij'
  linarith

private lemma sum_ternaryExtremal_sq_pos (d : ℕ) (hd : 0 < d) :
    0 < ∑ i : Fin d, (ternaryExtremal d i) ^ 2 := by
  let i0 : Fin d := ⟨0, hd⟩
  have h0 : (ternaryExtremal d i0) ^ 2 = 1 := by
    simp [ternaryExtremal, i0]
  have hle : (ternaryExtremal d i0) ^ 2 ≤ ∑ i : Fin d, (ternaryExtremal d i) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ i0)
  linarith

/-- Telescoping prefix sum: `∑_{i < k} (√(i+1) - √i) = √k`. -/
private lemma sum_sqrt_diff_range (k : ℕ) :
    ∑ i ∈ Finset.range k, (Real.sqrt ((i : ℝ) + 1) - Real.sqrt (i : ℝ)) = Real.sqrt (k : ℝ) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma sum_ternaryExtremal_filter_lt {d : ℕ} {k : ℕ} (hk : k ≤ d) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.1 < k), ternaryExtremal d i =
      Real.sqrt (k : ℝ) := by
  rw [← sum_sqrt_diff_range k]
  refine Finset.sum_bij (fun (i : Fin d) _ => i.1) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    exact ⟨⟨j, lt_of_lt_of_le hjk hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩, rfl⟩
  · intro i _
    rfl

/-- Abel summation by parts inequality on `Finset.range n`:
if `a` is non-increasing and nonnegative on `{0, ..., n-1}`, and all prefix sums of `b`
are `≤ 0`, then `∑_{i < n} a_i b_i ≤ 0`. -/
private lemma abel_sum_nonpos (n : ℕ) (a b : ℕ → ℝ)
    (ha_anti : ∀ i j, i ≤ j → j < n → a j ≤ a i)
    (ha_nonneg : ∀ i, i < n → 0 ≤ a i)
    (hb_prefix : ∀ k, k ≤ n → ∑ i ∈ Finset.range k, b i ≤ 0) :
    ∑ i ∈ Finset.range n, a i * b i ≤ 0 := by
  induction n generalizing a b with
  | zero => simp
  | succ m ih =>
    -- Apply IH to `a' i = a i - a m` on `range m`
    have h_ih : ∑ i ∈ Finset.range m, (a i - a m) * b i ≤ 0 := by
      apply ih (fun i => a i - a m) b
      · intro i j hij hj
        have := ha_anti i j hij (Nat.lt_succ_of_lt hj)
        linarith
      · intro i hi
        have := ha_anti i m (le_of_lt hi) (Nat.lt_succ_self m)
        linarith
      · intro k hk
        exact hb_prefix k (Nat.le_succ_of_le hk)
    have h_split : ∑ i ∈ Finset.range (m + 1), a i * b i =
        ∑ i ∈ Finset.range m, (a i - a m) * b i + a m * ∑ i ∈ Finset.range (m + 1), b i := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [h_split]
    have hlast : a m * ∑ i ∈ Finset.range (m + 1), b i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (ha_nonneg m (Nat.lt_succ_self m)) (hb_prefix (m + 1) le_rfl)
    linarith

/-- Rearrangement for antitone functions on `Fin d`: any `k`-element subset has sum at most
the top-`k` prefix sum. -/
private lemma sum_le_prefix_of_antitone {d : ℕ} {w : Fin d → ℝ} (hw : Antitone w)
    (S : Finset (Fin d)) :
    ∑ i ∈ S, w i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.1 < S.card), w i := by
  set k := S.card
  set T : Finset (Fin d) := Finset.univ.filter (fun i : Fin d => i.1 < k)
  by_cases hkd : k = d
  · have hS : S = Finset.univ := Finset.eq_univ_of_card S (by simpa [k] using hkd)
    have hT : T = Finset.univ := by
      ext i; simp [T, hkd]
    rw [hS, hT]
  · have hk_lt : k < d := lt_of_le_of_ne (by simpa [k] using S.card_le_univ) hkd
    have hT_card : T.card = k := by
      have : T.card = (Finset.range k).card := by
        refine Finset.card_bij (fun (i : Fin d) _ => i.1) ?_ ?_ ?_
        · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
        · intro i₁ _ i₂ _ h; exact Fin.ext h
        · intro j hj
          have hjk := Finset.mem_range.mp hj
          exact ⟨⟨j, lt_trans hjk hk_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩, rfl⟩
      simpa using this
    have hcard_sdiff : (S \ T).card = (T \ S).card := by
      have h1 := Finset.card_sdiff_add_card_inter S T
      have h2 := Finset.card_sdiff_add_card_inter T S
      rw [Finset.inter_comm] at h2
      omega
    let pivot : Fin d := ⟨k, hk_lt⟩
    have hST : ∑ i ∈ S \ T, w i ≤ (S \ T).card • w pivot := by
      calc ∑ i ∈ S \ T, w i ≤ ∑ _i ∈ S \ T, w pivot := by
            apply Finset.sum_le_sum
            intro i hi
            have hnotT : ¬ (i.1 < k) := by
              intro hlt
              exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
            exact hw (show pivot ≤ i from Nat.le_of_not_lt hnotT)
        _ = (S \ T).card • w pivot := Finset.sum_const _
    have hTS : (T \ S).card • w pivot ≤ ∑ i ∈ T \ S, w i := by
      calc (T \ S).card • w pivot = ∑ _i ∈ T \ S, w pivot := (Finset.sum_const _).symm
        _ ≤ ∑ i ∈ T \ S, w i := by
            apply Finset.sum_le_sum
            intro i hi
            have hlt : i.1 < k := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2
            exact hw (show i ≤ pivot from le_of_lt hlt)
    have hS_split : ∑ i ∈ S, w i = ∑ i ∈ S \ T, w i + ∑ i ∈ S ∩ T, w i := by
      have h := Finset.sum_sdiff (f := w) (Finset.inter_subset_left (s₁ := S) (s₂ := T))
      rw [Finset.sdiff_inter_self_left] at h
      exact h.symm
    have hT_split : ∑ i ∈ T, w i = ∑ i ∈ T \ S, w i + ∑ i ∈ S ∩ T, w i := by
      have h := Finset.sum_sdiff (f := w) (Finset.inter_subset_right (s₁ := S) (s₂ := T))
      rw [Finset.sdiff_inter_self_right] at h
      exact h.symm
    rw [hS_split, hT_split]
    rw [hcard_sdiff] at hST
    linarith

/-- Theorem 1 (`I082`): Exact universal EF21 contraction law and tightness for optimal
ternary compression in ALL dimensions `d ≥ 1`. -/
theorem ternary_ef21_contraction_exact (d : ℕ) (hd : 0 < d) :
    (∀ x : Fin d → ℝ, ∃ (γ : ℝ) (t : Fin d → ℤ),
      (∀ i, t i = -1 ∨ t i = 0 ∨ t i = 1) ∧
      ∑ i : Fin d, (x i - γ * (t i : ℝ)) ^ 2 ≤
        (1 - alphaTern d) * ∑ i : Fin d, (x i) ^ 2) ∧
    (∀ (γ : ℝ) (t : Fin d → ℤ),
      (∀ i, t i = -1 ∨ t i = 0 ∨ t i = 1) →
      (1 - alphaTern d) * ∑ i : Fin d, (ternaryExtremal d i) ^ 2 ≤
        ∑ i : Fin d, (ternaryExtremal d i - γ * (t i : ℝ)) ^ 2) := by
  have hw_sq_pos : 0 < ∑ i : Fin d, (ternaryExtremal d i) ^ 2 := sum_ternaryExtremal_sq_pos d hd
  have hα_mul : alphaTern d * ∑ i : Fin d, (ternaryExtremal d i) ^ 2 = 1 := by
    unfold alphaTern ternaryExtremal
    exact inv_mul_cancel₀ hw_sq_pos.ne'
  constructor
  · -- Part 1: Universal lower bound via sorting + Abel summation by parts
    intro x
    let σ : Equiv.Perm (Fin d) := Tuple.sort (fun i => -|x i|)
    have hσ_mono : Monotone (fun i => -|x (σ i)|) := Tuple.monotone_sort (fun i => -|x i|)
    let y : Fin d → ℝ := fun i => |x (σ i)|
    have hy_anti : Antitone y := by
      intro i j hij
      have := hσ_mono hij
      dsimp [y] at this ⊢
      linarith
    have hy_nonneg : ∀ i, 0 ≤ y i := fun i => abs_nonneg _
    -- Prefix score `P k = (∑_{i ≤ k} y i)^2 / (k + 1)`
    let prefSum : Fin d → ℝ := fun k => ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.1 ≤ k.1), y i
    let score : Fin d → ℝ := fun k => (prefSum k) ^ 2 / ((k.1 : ℝ) + 1)
    have huniv_ne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    obtain ⟨k0, _, hk0_max⟩ := Finset.exists_max_image Finset.univ score huniv_ne
    set M : ℝ := score k0
    have hM_nonneg : 0 ≤ M := by
      dsimp [M, score]
      positivity
    set s : ℝ := Real.sqrt M
    have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg M
    have hs_sq : s ^ 2 = M := Real.sq_sqrt hM_nonneg
    -- Extend `y` and `w` to `ℕ → ℝ` for Abel summation on `Finset.range d`
    let yN : ℕ → ℝ := fun n => if h : n < d then y ⟨n, h⟩ else 0
    let wN : ℕ → ℝ := fun n => if h : n < d then ternaryExtremal d ⟨n, h⟩ else 0
    have hsum_y_range : ∑ i ∈ Finset.range d, (yN i) ^ 2 = ∑ i : Fin d, (y i) ^ 2 := by
      refine (Finset.sum_bij (fun (i : Fin d) _ => i.1) ?_ ?_ ?_ ?_).symm
      · intro i _; exact Finset.mem_range.mpr i.2
      · intro i₁ _ i₂ _ h; exact Fin.ext h
      · intro j hj; exact ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
      · intro i _; simp [yN, i.2]
    have hsum_w_range : ∑ i ∈ Finset.range d, (wN i) ^ 2 =
        ∑ i : Fin d, (ternaryExtremal d i) ^ 2 := by
      refine (Finset.sum_bij (fun (i : Fin d) _ => i.1) ?_ ?_ ?_ ?_).symm
      · intro i _; exact Finset.mem_range.mpr i.2
      · intro i₁ _ i₂ _ h; exact Fin.ext h
      · intro j hj; exact ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
      · intro i _; simp [wN, i.2]
    have habel : ∑ i ∈ Finset.range d, (yN i + s * wN i) * (yN i - s * wN i) ≤ 0 := by
      apply abel_sum_nonpos d (fun i => yN i + s * wN i) (fun i => yN i - s * wN i)
      · intro i j hij hj
        have hi : i < d := lt_of_le_of_lt hij hj
        simp only [yN, wN, hi, hj, ↓reduceDIte]
        have hy_le := hy_anti (show (⟨i, hi⟩ : Fin d) ≤ ⟨j, hj⟩ from hij)
        have hw_le := ternaryExtremal_antitone d (show (⟨i, hi⟩ : Fin d) ≤ ⟨j, hj⟩ from hij)
        nlinarith
      · intro i hi
        simp only [yN, wN, hi, ↓reduceDIte]
        exact add_nonneg (hy_nonneg _) (mul_nonneg hs_nonneg (ternaryExtremal_nonneg d _))
      · intro k hk
        cases k with
        | zero => simp
        | succ m =>
          have hm : m < d := Nat.lt_of_succ_le hk
          let km : Fin d := ⟨m, hm⟩
          have hy_pref : ∑ i ∈ Finset.range (m + 1), yN i = prefSum km := by
            refine (Finset.sum_bij (fun (i : Fin d) _ => i.1) ?_ ?_ ?_ ?_).symm
            · intro i hi
              exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hi).2)
            · intro i₁ _ i₂ _ h; exact Fin.ext h
            · intro j hj
              have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              exact ⟨⟨j, lt_of_le_of_lt hjm hm⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjm⟩, rfl⟩
            · intro i _; simp [yN, i.2]
          have hw_pref : ∑ i ∈ Finset.range (m + 1), wN i = Real.sqrt ((m : ℝ) + 1) := by
            have hcongr : ∀ i ∈ Finset.range (m + 1),
                wN i = Real.sqrt ((i : ℝ) + 1) - Real.sqrt (i : ℝ) := by
              intro i hi
              have hid : i < d := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
              simp [wN, hid, ternaryExtremal]
            rw [Finset.sum_congr rfl hcongr, sum_sqrt_diff_range]
            push_cast; rfl
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hy_pref, hw_pref]
          have hsc : score km ≤ M := hk0_max km (Finset.mem_univ km)
          have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
          have hsq : (prefSum km) ^ 2 ≤ (s * Real.sqrt ((m : ℝ) + 1)) ^ 2 := by
            rw [mul_pow, hs_sq, Real.sq_sqrt hden.le]
            exact (div_le_iff₀ hden).mp hsc
          have hpref_nonneg : 0 ≤ prefSum km := Finset.sum_nonneg (fun i _ => hy_nonneg i)
          have hrhs_nonneg : 0 ≤ s * Real.sqrt ((m : ℝ) + 1) :=
            mul_nonneg hs_nonneg (Real.sqrt_nonneg _)
          nlinarith
    have hnorm_le : ∑ i : Fin d, (y i) ^ 2 ≤ M * ∑ i : Fin d, (ternaryExtremal d i) ^ 2 := by
      have hident : ∑ i ∈ Finset.range d, (yN i + s * wN i) * (yN i - s * wN i) =
          ∑ i ∈ Finset.range d, (yN i) ^ 2 - M * ∑ i ∈ Finset.range d, (wN i) ^ 2 := by
        have hpt : ∀ i, (yN i + s * wN i) * (yN i - s * wN i) = (yN i) ^ 2 - M * (wN i) ^ 2 := by
          intro i
          calc (yN i + s * wN i) * (yN i - s * wN i) = (yN i) ^ 2 - s ^ 2 * (wN i) ^ 2 := by ring
            _ = (yN i) ^ 2 - M * (wN i) ^ 2 := by rw [hs_sq]
        simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hident, hsum_y_range, hsum_w_range] at habel
      linarith
    have hM_ge : alphaTern d * ∑ i : Fin d, (y i) ^ 2 ≤ M := by
      have hα_pos : 0 < alphaTern d := by
        unfold alphaTern; exact inv_pos.mpr hw_sq_pos
      have := mul_le_mul_of_nonneg_left hnorm_le hα_pos.le
      rw [← mul_assoc, mul_comm (alphaTern d) M, mul_assoc, hα_mul, mul_one] at this
      exact this
    -- Construct witness `(γ, t)` achieving exact error `∑ x_i^2 - M`
    let γ : ℝ := prefSum k0 / ((k0.1 : ℝ) + 1)
    let t : Fin d → ℤ := fun j =>
      if (σ.symm j).1 ≤ k0.1 then (if 0 ≤ x j then 1 else -1) else 0
    refine ⟨γ, t, ?_, ?_⟩
    · intro j
      dsimp [t]
      split_ifs <;> simp
    · have hsum_x_eq : ∑ j : Fin d, (x j) ^ 2 = ∑ i : Fin d, (y i) ^ 2 := by
        rw [← Equiv.sum_comp σ (fun j => (x j) ^ 2)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        dsimp [y]
        exact (sq_abs (x (σ i))).symm
      have herr_eq : ∑ j : Fin d, (x j - γ * (t j : ℝ)) ^ 2 =
          ∑ i : Fin d, (y i) ^ 2 - M := by
        rw [← Equiv.sum_comp σ (fun j => (x j - γ * (t j : ℝ)) ^ 2)]
        let A : Finset (Fin d) := Finset.univ.filter (fun i : Fin d => i.1 ≤ k0.1)
        let B : Finset (Fin d) := Finset.univ.filter (fun i : Fin d => ¬ (i.1 ≤ k0.1))
        have hsplit1 : ∑ i : Fin d, (x (σ i) - γ * (t (σ i) : ℝ)) ^ 2 =
            ∑ i ∈ A, (x (σ i) - γ * (t (σ i) : ℝ)) ^ 2 +
              ∑ i ∈ B, (x (σ i) - γ * (t (σ i) : ℝ)) ^ 2 :=
          (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin d => i.1 ≤ k0.1) _).symm
        have hsplit2 : ∑ i : Fin d, (y i) ^ 2 =
            ∑ i ∈ A, (y i) ^ 2 + ∑ i ∈ B, (y i) ^ 2 :=
          (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin d => i.1 ≤ k0.1) _).symm
        have hA_eq : ∑ i ∈ A, (x (σ i) - γ * (t (σ i) : ℝ)) ^ 2 =
            ∑ i ∈ A, (y i - γ) ^ 2 := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hle : i.1 ≤ k0.1 := (Finset.mem_filter.mp hi).2
          simp only [t, Equiv.symm_apply_apply, hle, ↓reduceIte, y]
          split_ifs with hx
          · rw [abs_of_nonneg hx]; push_cast; ring
          · rw [abs_of_neg (lt_of_not_ge hx)]; push_cast; ring
        have hB_eq : ∑ i ∈ B, (x (σ i) - γ * (t (σ i) : ℝ)) ^ 2 = ∑ i ∈ B, (y i) ^ 2 := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hnot : ¬ (i.1 ≤ k0.1) := (Finset.mem_filter.mp hi).2
          simp only [t, Equiv.symm_apply_apply, hnot, ↓reduceIte, y, Int.cast_zero, mul_zero,
            sub_zero]
          exact (sq_abs (x (σ i))).symm
        have hA_card : (A.card : ℝ) = (k0.1 : ℝ) + 1 := by
          have hcard : A.card = k0.1 + 1 := by
            have : A.card = (Finset.range (k0.1 + 1)).card := by
              refine Finset.card_bij (fun (i : Fin d) _ => i.1) ?_ ?_ ?_
              · intro i hi
                exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hi).2)
              · intro i₁ _ i₂ _ h; exact Fin.ext h
              · intro j hj
                have hjk : j ≤ k0.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                exact ⟨⟨j, lt_of_le_of_lt hjk k0.2⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩, rfl⟩
            simpa using this
          rw [hcard]; push_cast; rfl
        have hA_expand : ∑ i ∈ A, (y i - γ) ^ 2 = ∑ i ∈ A, (y i) ^ 2 - M := by
          have hpt : ∀ i, (y i - γ) ^ 2 = (y i) ^ 2 - 2 * γ * y i + γ ^ 2 := fun i => by ring
          simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            Finset.sum_const, nsmul_eq_mul, hA_card]
          have hA_sum : ∑ i ∈ A, y i = prefSum k0 := rfl
          rw [hA_sum]
          dsimp [γ, M, score]
          have hd0 : (0 : ℝ) < (k0.1 : ℝ) + 1 := by positivity
          field_simp
          ring
        rw [hsplit1, hA_eq, hB_eq, hA_expand, hsplit2]
        ring
      rw [herr_eq, hsum_x_eq]
      linarith
  · -- Part 2: Exact tightness at `ternaryExtremal d`
    intro γ t ht
    let w := ternaryExtremal d
    let S : Finset (Fin d) := Finset.univ.filter (fun i : Fin d => t i ≠ 0)
    by_cases hS : S.card = 0
    · have ht0 : ∀ i : Fin d, t i = 0 := by
        intro i
        by_contra hne
        have hmem : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hmem⟩
        omega
      simp_rw [ht0, Int.cast_zero, mul_zero, sub_zero]
      have hα_pos : 0 < alphaTern d := by
        unfold alphaTern; exact inv_pos.mpr hw_sq_pos
      nlinarith
    · have hk_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hS)
      have htsq : ∀ i ∈ S, ((t i : ℝ)) ^ 2 = 1 := by
        intro i hi
        have hne : t i ≠ 0 := (Finset.mem_filter.mp hi).2
        rcases ht i with h | h | h
        · rw [h]; norm_num
        · exact absurd h hne
        · rw [h]; norm_num
      have htabs : ∀ i ∈ S, |(t i : ℝ)| = 1 := by
        intro i hi
        have hne : t i ≠ 0 := (Finset.mem_filter.mp hi).2
        rcases ht i with h | h | h
        · rw [h]; norm_num
        · exact absurd h hne
        · rw [h]; norm_num
      have hexpand : ∑ i : Fin d, (w i - γ * (t i : ℝ)) ^ 2 =
          ∑ i : Fin d, (w i) ^ 2 - 2 * γ * (∑ i ∈ S, w i * (t i : ℝ)) +
            γ ^ 2 * (S.card : ℝ) := by
        have hpt : ∀ i : Fin d, (w i - γ * (t i : ℝ)) ^ 2 =
            (w i) ^ 2 - 2 * γ * (w i * (t i : ℝ)) + γ ^ 2 * ((t i : ℝ)) ^ 2 := fun i => by ring
        simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        have h1 : ∑ i : Fin d, w i * (t i : ℝ) = ∑ i ∈ S, w i * (t i : ℝ) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin d => t i ≠ 0)]
          have hz : ∑ i ∈ Finset.univ.filter (fun i : Fin d => ¬ (t i ≠ 0)),
              w i * (t i : ℝ) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have : t i = 0 := not_not.mp (Finset.mem_filter.mp hi).2
            simp [this]
          linarith
        have h2 : ∑ i : Fin d, ((t i : ℝ)) ^ 2 = (S.card : ℝ) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin d => t i ≠ 0)]
          have hz : ∑ i ∈ Finset.univ.filter (fun i : Fin d => ¬ (t i ≠ 0)),
              ((t i : ℝ)) ^ 2 = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have : t i = 0 := not_not.mp (Finset.mem_filter.mp hi).2
            simp [this]
          have ho : ∑ i ∈ S, ((t i : ℝ)) ^ 2 = (S.card : ℝ) := by
            rw [Finset.sum_congr rfl htsq, Finset.sum_const, nsmul_eq_mul, mul_one]
          linarith
        rw [h1, h2]
      have hcs : ∑ i : Fin d, (w i) ^ 2 - (∑ i ∈ S, w i * (t i : ℝ)) ^ 2 / (S.card : ℝ) ≤
          ∑ i : Fin d, (w i - γ * (t i : ℝ)) ^ 2 := by
        rw [hexpand]
        have hsq : 0 ≤ (S.card : ℝ) * (γ - (∑ i ∈ S, w i * (t i : ℝ)) / (S.card : ℝ)) ^ 2 :=
          mul_nonneg hk_pos.le (sq_nonneg _)
        have hident : (∑ i : Fin d, (w i) ^ 2 - 2 * γ * (∑ i ∈ S, w i * (t i : ℝ)) +
            γ ^ 2 * (S.card : ℝ)) -
            (∑ i : Fin d, (w i) ^ 2 - (∑ i ∈ S, w i * (t i : ℝ)) ^ 2 / (S.card : ℝ)) =
            (S.card : ℝ) * (γ - (∑ i ∈ S, w i * (t i : ℝ)) / (S.card : ℝ)) ^ 2 := by
          field_simp; ring
        linarith
      have htri : |∑ i ∈ S, w i * (t i : ℝ)| ≤ ∑ i ∈ S, w i := by
        calc |∑ i ∈ S, w i * (t i : ℝ)|
            ≤ ∑ i ∈ S, |w i * (t i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ S, w i := by
              refine Finset.sum_congr rfl (fun i hi => ?_)
              rw [abs_mul, abs_of_nonneg (ternaryExtremal_nonneg d i), htabs i hi, mul_one]
      have hrearr : ∑ i ∈ S, w i ≤ Real.sqrt (S.card : ℝ) := by
        have h1 := sum_le_prefix_of_antitone (ternaryExtremal_antitone d) S
        have hle : S.card ≤ d := by simpa using S.card_le_univ
        rw [sum_ternaryExtremal_filter_lt hle] at h1
        exact h1
      have hproj : (∑ i ∈ S, w i * (t i : ℝ)) ^ 2 / (S.card : ℝ) ≤ 1 := by
        rw [div_le_one hk_pos]
        have hle_sqrt : |∑ i ∈ S, w i * (t i : ℝ)| ≤ Real.sqrt (S.card : ℝ) :=
          le_trans htri hrearr
        have hsq_le : |∑ i ∈ S, w i * (t i : ℝ)| ^ 2 ≤ (Real.sqrt (S.card : ℝ)) ^ 2 := by
          nlinarith [abs_nonneg (∑ i ∈ S, w i * (t i : ℝ)), Real.sqrt_nonneg (S.card : ℝ)]
        rw [sq_abs, Real.sq_sqrt hk_pos.le] at hsq_le
        exact hsq_le
      have hrhs : (1 - alphaTern d) * ∑ i : Fin d, (w i) ^ 2 = ∑ i : Fin d, (w i) ^ 2 - 1 := by
        calc (1 - alphaTern d) * ∑ i : Fin d, (w i) ^ 2
            = ∑ i : Fin d, (w i) ^ 2 - alphaTern d * ∑ i : Fin d, (w i) ^ 2 := by ring
          _ = ∑ i : Fin d, (w i) ^ 2 - 1 := by rw [hα_mul]
      linarith

/-- Theorem 2 (`I082`): Exact harmonic sandwich for `α_tern(d)` across ALL `d ≥ 1`:
`4 / (4 + H_{d-1}) ≤ α_tern(d) ≤ 4 / (3 + H_d)`. -/
theorem alphaTern_harmonic_sandwich (d : ℕ) (hd : 0 < d) :
    4 / (4 + harmonicR (d - 1)) ≤ alphaTern d ∧
      alphaTern d ≤ 4 / (3 + harmonicR d) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  -- Now `d = m + 1` and `d - 1 = m`
  have hsum_split : ∑ i : Fin (m + 1), (ternaryExtremal (m + 1) i) ^ 2 =
      1 + ∑ j : Fin m, (Real.sqrt ((j.1 : ℝ) + 2) - Real.sqrt ((j.1 : ℝ) + 1)) ^ 2 := by
    rw [Fin.sum_univ_succ]
    congr 1
    · simp [ternaryExtremal]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [ternaryExtremal]
      ring_nf
  have hH_split : harmonicR (m + 1) = 1 + ∑ j : Fin m, (1 : ℝ) / ((j.1 : ℝ) + 2) := by
    unfold harmonicR
    rw [Fin.sum_univ_succ]
    congr 1
    · simp
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp
      ring_nf
  have hterm_bounds : ∀ j : Fin m,
      (1 : ℝ) / (4 * ((j.1 : ℝ) + 2)) ≤
        (Real.sqrt ((j.1 : ℝ) + 2) - Real.sqrt ((j.1 : ℝ) + 1)) ^ 2 ∧
      (Real.sqrt ((j.1 : ℝ) + 2) - Real.sqrt ((j.1 : ℝ) + 1)) ^ 2 ≤
        (1 : ℝ) / (4 * ((j.1 : ℝ) + 1)) := by
    intro j
    set a : ℝ := (j.1 : ℝ) + 1
    have ha_pos : 0 < a := by positivity
    have ha1_pos : 0 < a + 1 := by positivity
    have hconj : (Real.sqrt (a + 1) - Real.sqrt a) * (Real.sqrt (a + 1) + Real.sqrt a) = 1 := by
      calc (Real.sqrt (a + 1) - Real.sqrt a) * (Real.sqrt (a + 1) + Real.sqrt a)
          = Real.sqrt (a + 1) ^ 2 - Real.sqrt a ^ 2 := by ring
        _ = (a + 1) - a := by rw [Real.sq_sqrt ha1_pos.le, Real.sq_sqrt ha_pos.le]
        _ = 1 := by ring
    have hsum_pos : 0 < Real.sqrt (a + 1) + Real.sqrt a := by
      have h1 := Real.sqrt_pos.mpr ha1_pos
      have h2 := Real.sqrt_pos.mpr ha_pos
      linarith
    have hsq_eq : (Real.sqrt (a + 1) - Real.sqrt a) ^ 2 =
        1 / (Real.sqrt (a + 1) + Real.sqrt a) ^ 2 := by
      have hinv := eq_inv_of_mul_eq_one_left hconj
      rw [hinv, one_div, inv_pow]
    have hsqrt_le : Real.sqrt a ≤ Real.sqrt (a + 1) := Real.sqrt_le_sqrt (by linarith)
    have hlo_den : 4 * a ≤ (Real.sqrt (a + 1) + Real.sqrt a) ^ 2 := by
      have : (2 * Real.sqrt a) ^ 2 ≤ (Real.sqrt (a + 1) + Real.sqrt a) ^ 2 := by
        nlinarith [Real.sqrt_nonneg a]
      rw [mul_pow, Real.sq_sqrt ha_pos.le] at this
      linarith
    have hhi_den : (Real.sqrt (a + 1) + Real.sqrt a) ^ 2 ≤ 4 * (a + 1) := by
      have : (Real.sqrt (a + 1) + Real.sqrt a) ^ 2 ≤ (2 * Real.sqrt (a + 1)) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (a + 1)]
      rw [mul_pow, Real.sq_sqrt ha1_pos.le] at this
      linarith
    have hden_pos : 0 < (Real.sqrt (a + 1) + Real.sqrt a) ^ 2 := sq_pos_of_pos hsum_pos
    have ha2 : (j.1 : ℝ) + 2 = a + 1 := by dsimp [a]; ring
    rw [ha2, hsq_eq]
    constructor
    · exact one_div_le_one_div_of_le hden_pos hhi_den
    · exact one_div_le_one_div_of_le (by positivity) hlo_den
  have hsum_lo : (3 + harmonicR (m + 1)) / 4 ≤
      ∑ i : Fin (m + 1), (ternaryExtremal (m + 1) i) ^ 2 := by
    rw [hsum_split, hH_split]
    have h1 : ∑ j : Fin m, (1 : ℝ) / (4 * ((j.1 : ℝ) + 2)) ≤
        ∑ j : Fin m, (Real.sqrt ((j.1 : ℝ) + 2) - Real.sqrt ((j.1 : ℝ) + 1)) ^ 2 :=
      Finset.sum_le_sum (fun j _ => (hterm_bounds j).1)
    have h2 : ∑ j : Fin m, (1 : ℝ) / (4 * ((j.1 : ℝ) + 2)) =
        (∑ j : Fin m, (1 : ℝ) / ((j.1 : ℝ) + 2)) / 4 := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => by field_simp)
    linarith
  have hsum_hi : ∑ i : Fin (m + 1), (ternaryExtremal (m + 1) i) ^ 2 ≤
      (4 + harmonicR m) / 4 := by
    rw [hsum_split]
    have h1 : ∑ j : Fin m, (Real.sqrt ((j.1 : ℝ) + 2) - Real.sqrt ((j.1 : ℝ) + 1)) ^ 2 ≤
        ∑ j : Fin m, (1 : ℝ) / (4 * ((j.1 : ℝ) + 1)) :=
      Finset.sum_le_sum (fun j _ => (hterm_bounds j).2)
    have h2 : ∑ j : Fin m, (1 : ℝ) / (4 * ((j.1 : ℝ) + 1)) = harmonicR m / 4 := by
      unfold harmonicR
      rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => by field_simp)
    linarith
  have hHm_nonneg : 0 ≤ harmonicR m := Finset.sum_nonneg (fun j _ => by positivity)
  have hHm1_nonneg : 0 ≤ harmonicR (m + 1) := Finset.sum_nonneg (fun j _ => by positivity)
  have hS_pos : 0 < ∑ i : Fin (m + 1), (ternaryExtremal (m + 1) i) ^ 2 :=
    sum_ternaryExtremal_sq_pos (m + 1) (Nat.succ_pos m)
  have hα_eq : alphaTern (m + 1) = (∑ i : Fin (m + 1), (ternaryExtremal (m + 1) i) ^ 2)⁻¹ := rfl
  change 4 / (4 + harmonicR (m + 1 - 1)) ≤ alphaTern (m + 1) ∧
    alphaTern (m + 1) ≤ 4 / (3 + harmonicR (m + 1))
  rw [Nat.add_sub_cancel, hα_eq]
  constructor
  · have hinv := inv_anti₀ hS_pos hsum_hi
    simpa [inv_div] using hinv
  · have hpos : 0 < (3 + harmonicR (m + 1)) / 4 := by linarith
    have hinv := inv_anti₀ hpos hsum_lo
    simpa [inv_div] using hinv

end EF21Ternary
