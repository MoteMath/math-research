/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OctonionRopeWelch.Defs

/-!
# Theorems 5 & 6: Exact Worst-Case Softmax Top-K (Gap-Δ) & Quantized-Logit (±ε) L1 Laws

Pure-`Init` Lean 4 proofs over `Rat` (zero Mathlib, zero `Real.exp`):
1. `softmax_topk_gap_l1_exact`:
   For all `N K : Nat` (`0 < K`, `K ≤ N`), all `E : Rat` (`0 < E`), and all positive weights
   `w : Fin N → Rat` with `w j * E ≤ w i` for `i < K ≤ j`:
   - Exact identity: `‖p - q‖_1 = 2 * T / (H + T)`
   - Universal sharp upper bound: `‖p - q‖_1 ≤ 2 * (N - K) / (K * E + (N - K))`
   - Exact sharpness witness `w*(i) = if i < K then E else 1`.
2. `softmax_quantized_logit_l1_exact`:
   For all `N : Nat` (`2 ≤ N`), all `R : Rat` (`1 ≤ R`), and all positive weights `w, w' : Fin N → Rat`
   with `w i ≤ R * w' i` and `w' i ≤ R * w i`:
   - Universal sharp upper bound: `‖p - p'‖_1 ≤ 2 * (R - 1) / (R + 1)` (proved via the exact SOS
     identity `(R - 1) * (R * (1 - a) - a)^2 ≥ 0`)
   - Exact sharpness witness for EVERY `N ≥ 2`.
-/

namespace OctonionRopeWelch

/-! ## Helper Lemmas for `Rat` and `sumRat` -/

private theorem rat_le_of_sub_nonneg {a b : Rat} (h : 0 ≤ b - a) : a ≤ b := by
  have h1 : 0 + a ≤ (b - a) + a := Rat.add_le_add_right.mpr h
  have h2 : 0 + a = a := by grind
  have h3 : (b - a) + a = b := by grind
  rw [h2, h3] at h1
  exact h1

private theorem rat_sub_nonneg_of_le {a b : Rat} (h : a ≤ b) : 0 ≤ b - a := by
  have h1 : a + -a ≤ b + -a := Rat.add_le_add_right.mpr h
  have h2 : a + -a = 0 := by grind
  have h3 : b + -a = b - a := by grind
  rw [h2, h3] at h1
  exact h1

private theorem rat_add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr h1) (Rat.add_le_add_left.mpr h2)

private theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rw [Rat.lt_iff_le_and_ne] at h1 ⊢
  refine ⟨Rat.le_trans h1.1 h2, ?_⟩
  intro heq
  subst heq
  exact h1.2 (Rat.le_antisymm h1.1 h2)

private theorem rat_lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  rw [Rat.lt_iff_le_and_ne] at h2 ⊢
  refine ⟨Rat.le_trans h1 h2.1, ?_⟩
  intro heq
  subst heq
  exact h2.2 (Rat.le_antisymm h2.1 h1)

private theorem rat_add_lt_add_of_lt_of_le {a b c d : Rat} (h1 : a < b) (h2 : c ≤ d) : a + c < b + d := by
  have hle : a + c ≤ b + d := rat_add_le_add (Rat.le_of_lt h1) h2
  rw [Rat.lt_iff_le_and_ne] at h1 ⊢
  refine ⟨hle, ?_⟩
  intro heq
  have hbc : b + c ≤ b + d := Rat.add_le_add_left.mpr h2
  have hac : a + c ≤ b + c := Rat.add_le_add_right.mpr h1.1
  have hab : b + c ≤ a + c := by rw [heq]; exact hbc
  have heqc : a + c = b + c := Rat.le_antisymm hac hab
  have hab' : a = b := by grind
  exact h1.2 hab'

private theorem rat_add_lt_add_of_le_of_lt {a b c d : Rat} (h1 : a ≤ b) (h2 : c < d) : a + c < b + d := by
  have h := rat_add_lt_add_of_lt_of_le h2 h1
  have hL : c + a = a + c := by grind
  have hR : d + b = b + d := by grind
  rw [hL, hR] at h
  exact h

private theorem rat_lt_or_ge (a b : Rat) : a < b ∨ b ≤ a := by
  by_cases h : b ≤ a
  · exact Or.inr h
  · exact Or.inl (Rat.not_le.mp h)

private theorem rat_mul_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  have h := Rat.mul_le_mul_of_nonneg_left hb ha
  have hz : a * 0 = 0 := by grind
  rw [hz] at h
  exact h

private theorem rat_sq_nonneg (x : Rat) : 0 ≤ x * x := by
  cases @Rat.le_total 0 x with
  | inl h => exact rat_mul_nonneg h h
  | inr h =>
    have hn : 0 ≤ -x := by
      have h1 := rat_sub_nonneg_of_le h
      have h2 : 0 - x = -x := by grind
      rw [h2] at h1
      exact h1
    have hmul := rat_mul_nonneg hn hn
    have heq : (-x) * (-x) = x * x := by grind
    rw [heq] at hmul
    exact hmul

private theorem rat_mul_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have h := Rat.mul_lt_mul_of_pos_left hb ha
  have hz : a * 0 = 0 := by grind
  rw [hz] at h
  exact h

private theorem rat_ne_zero_of_pos {a : Rat} (ha : 0 < a) : a ≠ 0 := by
  intro h
  subst h
  exact Rat.lt_irrefl ha

private theorem rat_inv_pos {a : Rat} (ha : 0 < a) : 0 < a⁻¹ := by
  cases rat_lt_or_ge 0 a⁻¹ with
  | inl h => exact h
  | inr h =>
    have hmul : a * a⁻¹ ≤ a * 0 := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt ha)
    rw [Rat.mul_inv_cancel a (rat_ne_zero_of_pos ha), Rat.mul_zero] at hmul
    exact absurd hmul (by decide)

private theorem rat_div_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [Rat.div_def]
  exact rat_mul_pos ha (rat_inv_pos hb)

private theorem rat_div_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [Rat.div_def]
  exact rat_mul_nonneg ha (Rat.le_of_lt (rat_inv_pos hb))

private theorem rat_div_self {a : Rat} (ha : a ≠ 0) : a / a = 1 := by
  rw [Rat.div_def]
  exact Rat.mul_inv_cancel a ha

private theorem rat_inv_mul_inv {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have hab : a * b ≠ 0 := by
    intro h
    rcases Rat.mul_eq_zero.mp h with h1 | h1
    · exact ha h1
    · exact hb h1
  have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    have : (a * b) * (b⁻¹ * a⁻¹) = a * (b * b⁻¹) * a⁻¹ := by grind
    rw [this, Rat.mul_inv_cancel b hb, Rat.mul_one, Rat.mul_inv_cancel a ha]
  have h2 := congrArg (fun z => (a * b)⁻¹ * z) h1
  have hL : (a * b)⁻¹ * ((a * b) * (b⁻¹ * a⁻¹)) = b⁻¹ * a⁻¹ := by
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel (a * b) hab, Rat.one_mul]
  rw [hL, Rat.mul_one] at h2
  exact h2.symm

private theorem rat_div_le_div_iff {a b c d : Rat} (hb : 0 < b) (hd : 0 < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := by
  constructor
  · intro h
    have hbd : 0 < b * d := rat_mul_pos hb hd
    have h1 := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hbd)
    have hL : a / b * (b * d) = a * d := by
      rw [Rat.div_def]
      have : a * b⁻¹ * (b * d) = a * (b⁻¹ * b) * d := by grind
      rw [this, Rat.inv_mul_cancel b (rat_ne_zero_of_pos hb)]
      grind
    have hR : c / d * (b * d) = c * b := by
      rw [Rat.div_def]
      have : c * d⁻¹ * (b * d) = c * (d⁻¹ * d) * b := by grind
      rw [this, Rat.inv_mul_cancel d (rat_ne_zero_of_pos hd)]
      grind
    rw [hL, hR] at h1
    exact h1
  · intro h
    have hinv : 0 < (b * d)⁻¹ := rat_inv_pos (rat_mul_pos hb hd)
    have h1 := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hinv)
    have hL : a * d * (b * d)⁻¹ = a / b := by
      rw [Rat.div_def, rat_inv_mul_inv (rat_ne_zero_of_pos hb) (rat_ne_zero_of_pos hd)]
      have : a * d * (d⁻¹ * b⁻¹) = a * (d * d⁻¹) * b⁻¹ := by grind
      rw [this, Rat.mul_inv_cancel d (rat_ne_zero_of_pos hd)]
      grind
    have hR : c * b * (b * d)⁻¹ = c / d := by
      rw [Rat.div_def, rat_inv_mul_inv (rat_ne_zero_of_pos hb) (rat_ne_zero_of_pos hd)]
      have : c * b * (d⁻¹ * b⁻¹) = c * (b * b⁻¹) * d⁻¹ := by grind
      rw [this, Rat.mul_inv_cancel b (rat_ne_zero_of_pos hb)]
      grind
    rw [hL, hR] at h1
    exact h1

private theorem rat_abs_of_nonneg {x : Rat} (hx : 0 ≤ x) : x.abs = x := by
  simp [Rat.abs, hx]

private theorem rat_abs_of_nonpos {x : Rat} (hx : x ≤ 0) : x.abs = -x := by
  by_cases h0 : 0 ≤ x
  · have heq : x = 0 := Rat.le_antisymm hx h0
    subst heq
    decide
  · simp [Rat.abs, h0]

private theorem sumRat_add {n : Nat} (f g : Fin n → Rat) :
    sumRat (fun i => f i + g i) = sumRat f + sumRat g := by
  induction n with
  | zero => simp only [sumRat]; grind
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

private theorem sumRat_sub {n : Nat} (f g : Fin n → Rat) :
    sumRat (fun i => f i - g i) = sumRat f - sumRat g := by
  induction n with
  | zero => simp only [sumRat]; grind
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    grind

private theorem sumRat_const (n : Nat) (c : Rat) :
    sumRat (fun _ : Fin n => c) = (n : Rat) * c := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    rw [ih]
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      rw [Rat.natCast_add]; rfl
    rw [hcast]
    grind

private theorem sumRat_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    sumRat (fun i => c * f i) = c * sumRat f := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc), Rat.mul_add]

private theorem sumRat_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumRat (fun i => f i * c) = sumRat f * c := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    rw [ih (fun i => f i.castSucc), Rat.add_mul]

private theorem sumRat_div_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumRat (fun i => f i / c) = sumRat f / c := by
  simp only [Rat.div_def]
  exact sumRat_mul_right f c⁻¹

private theorem sumRat_nonneg {n : Nat} (f : Fin n → Rat) (h : ∀ i, 0 ≤ f i) :
    0 ≤ sumRat f := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    have h1 := ih (fun i => f i.castSucc) (fun i => h i.castSucc)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    have hadd := rat_add_le_add h1 h2
    have hz : (0 : Rat) + 0 = 0 := by grind
    rw [hz] at hadd
    exact hadd

private theorem sumRat_le_sumRat {n : Nat} (f g : Fin n → Rat) (h : ∀ i, f i ≤ g i) :
    sumRat f ≤ sumRat g := by
  induction n with
  | zero => simp [sumRat]
  | succ k ih =>
    simp only [sumRat]
    exact rat_add_le_add (ih (fun i => f i.castSucc) (fun i => g i.castSucc) (fun i => h i.castSucc))
                         (h ⟨k, Nat.lt_succ_self k⟩)

private theorem sumRat_pos_of_mem {n : Nat} (f : Fin n → Rat) (h0 : ∀ i, 0 ≤ f i)
    (i0 : Fin n) (hpos : 0 < f i0) : 0 < sumRat f := by
  induction n with
  | zero => exact Fin.elim0 i0
  | succ k ih =>
    simp only [sumRat]
    by_cases hlast : i0.val = k
    · have hi : i0 = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hlast
      subst hi
      have h1 := sumRat_nonneg (fun i : Fin k => f i.castSucc) (fun i => h0 i.castSucc)
      have hadd := rat_add_lt_add_of_le_of_lt h1 hpos
      have hz : (0 : Rat) + 0 = 0 := by grind
      rw [hz] at hadd
      exact hadd
    · have hlt : i0.val < k := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i0.isLt) hlast
      let i' : Fin k := ⟨i0.val, hlt⟩
      have h1 := ih (fun i => f i.castSucc) (fun i => h0 i.castSucc) i' hpos
      have h2 := h0 ⟨k, Nat.lt_succ_self k⟩
      have hadd := rat_add_lt_add_of_lt_of_le h1 h2
      have hz : (0 : Rat) + 0 = 0 := by grind
      rw [hz] at hadd
      exact hadd

private theorem sumRat_count_lt (N K : Nat) (hKN : K ≤ N) :
    sumRat (fun i : Fin N => if i.val < K then (1 : Rat) else 0) = (K : Rat) := by
  induction N with
  | zero =>
    have hK0 : K = 0 := by omega
    subst hK0
    simp [sumRat]
  | succ n ih =>
    simp only [sumRat]
    by_cases hlt : n < K
    · have hK : K = n + 1 := by omega
      subst hK
      have hcongr : (fun i : Fin n => if i.castSucc.val < n + 1 then (1 : Rat) else 0) =
                    (fun _ : Fin n => (1 : Rat)) := by
        funext i
        have : i.val < n + 1 := Nat.lt_succ_of_lt i.isLt
        simp [Fin.castSucc, this]
      rw [hcongr, sumRat_const]
      simp only [Nat.lt_succ_self, ite_true]
      have hcast : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by rw [Rat.natCast_add]; rfl
      rw [hcast]
      grind
    · have hKn : K ≤ n := by omega
      have hcongr : (fun i : Fin n => if i.castSucc.val < K then (1 : Rat) else 0) =
                    (fun i : Fin n => if i.val < K then (1 : Rat) else 0) := by
        funext i; rfl
      rw [hcongr, ih hKn]
      simp only [hlt, ite_false]
      grind

private theorem sumRat_count_ge (N K : Nat) (hKN : K ≤ N) :
    sumRat (fun i : Fin N => if i.val < K then (0 : Rat) else 1) = ((N - K : Nat) : Rat) := by
  have hsum :
      sumRat (fun i : Fin N => if i.val < K then (1 : Rat) else 0) +
      sumRat (fun i : Fin N => if i.val < K then (0 : Rat) else 1) = (N : Rat) := by
    rw [← sumRat_add]
    have hcongr : (fun i : Fin N => (if i.val < K then (1 : Rat) else 0) + (if i.val < K then (0 : Rat) else 1)) =
                  (fun _ : Fin N => (1 : Rat)) := by
      funext i; by_cases h : i.val < K <;> simp only [h, ite_true, ite_false] <;> grind
    rw [hcongr, sumRat_const]
    grind
  rw [sumRat_count_lt N K hKN] at hsum
  have hNK : (K : Rat) + ((N - K : Nat) : Rat) = (N : Rat) := by
    rw [← Rat.natCast_add]
    have : K + (N - K) = N := by omega
    rw [this]
  grind

/-! ## Theorem 5: Exact Softmax Top-K (Gap-Δ) L1 Law -/

theorem softmax_topk_gap_l1_exact (N K : Nat) (hK : 0 < K) (hKN : K ≤ N)
    (E : Rat) (hE : 0 < E) :
    (∀ (w : Fin N → Rat), (∀ i, 0 < w i) →
      (∀ i j : Fin N, i.val < K → K ≤ j.val → w j * E ≤ w i) →
      let H := sumRat (fun i : Fin N => if i.val < K then w i else 0)
      let T := sumRat (fun i : Fin N => if i.val < K then 0 else w i)
      l1DistRat (softmaxRat w) (topKSoftmaxRat K w) = (2 * T) / (H + T) ∧
      l1DistRat (softmaxRat w) (topKSoftmaxRat K w) ≤
        (2 * ((N - K : Nat) : Rat)) / ((K : Rat) * E + ((N - K : Nat) : Rat))) ∧
    (∃ (w : Fin N → Rat), (∀ i, 0 < w i) ∧
      (∀ i j : Fin N, i.val < K → K ≤ j.val → w j * E ≤ w i) ∧
      l1DistRat (softmaxRat w) (topKSoftmaxRat K w) =
        (2 * ((N - K : Nat) : Rat)) / ((K : Rat) * E + ((N - K : Nat) : Rat))) := by
  have hKpos : (0 : Rat) < (K : Rat) := Rat.natCast_lt_natCast.mpr hK
  have hNKnonneg : (0 : Rat) ≤ ((N - K : Nat) : Rat) := Rat.natCast_nonneg
  have hDenPos : 0 < (K : Rat) * E + ((N - K : Nat) : Rat) := by
    have hKE : 0 < (K : Rat) * E := rat_mul_pos hKpos hE
    have hadd := rat_add_lt_add_of_lt_of_le hKE hNKnonneg
    have hz : (0 : Rat) + 0 = 0 := by grind
    rw [hz] at hadd
    exact hadd
  have hmain :
      ∀ (w : Fin N → Rat), (∀ i, 0 < w i) →
      (∀ i j : Fin N, i.val < K → K ≤ j.val → w j * E ≤ w i) →
      let H := sumRat (fun i : Fin N => if i.val < K then w i else 0)
      let T := sumRat (fun i : Fin N => if i.val < K then 0 else w i)
      l1DistRat (softmaxRat w) (topKSoftmaxRat K w) = (2 * T) / (H + T) ∧
      l1DistRat (softmaxRat w) (topKSoftmaxRat K w) ≤
        (2 * ((N - K : Nat) : Rat)) / ((K : Rat) * E + ((N - K : Nat) : Rat)) := by
    intro w hw hgap
    dsimp only
    let H := sumRat (fun i : Fin N => if i.val < K then w i else 0)
    let T := sumRat (fun i : Fin N => if i.val < K then 0 else w i)
    have hZ : sumRat w = H + T := by
      change sumRat w = sumRat (fun i : Fin N => if i.val < K then w i else 0) +
                        sumRat (fun i : Fin N => if i.val < K then 0 else w i)
      rw [← sumRat_add]
      congr 1; funext i
      by_cases h : i.val < K <;> simp only [h, ite_true, ite_false] <;> grind
    have hHpos : 0 < H := by
      let i0 : Fin N := ⟨0, by omega⟩
      apply sumRat_pos_of_mem _ (fun i => by
        by_cases h : i.val < K
        · simp [h, Rat.le_of_lt (hw i)]
        · simp [h]) i0
      dsimp only [i0]
      simp [hK, hw ⟨0, by omega⟩]
    have hTnonneg : 0 ≤ T := sumRat_nonneg _ (fun i => by
      by_cases h : i.val < K
      · simp [h]
      · simp [h, Rat.le_of_lt (hw i)])
    have hZpos : 0 < H + T := by
      have hadd := rat_add_lt_add_of_lt_of_le hHpos hTnonneg
      have hz : (0 : Rat) + 0 = 0 := by grind
      rw [hz] at hadd
      exact hadd
    have hl1_eq : l1DistRat (softmaxRat w) (topKSoftmaxRat K w) = (2 * T) / (H + T) := by
      simp only [l1DistRat, softmaxRat, topKSoftmaxRat]
      have hpt :
          (fun i : Fin N => (w i / sumRat w - (if i.val < K then w i / H else 0)).abs) =
          (fun i : Fin N => (if i.val < K then w i / H - w i / (H + T) else 0) +
                            (if i.val < K then 0 else w i / (H + T))) := by
        funext i
        rw [hZ]
        by_cases h : i.val < K
        · simp only [h, ite_true, Rat.add_zero]
          have hle : w i / (H + T) ≤ w i / H := by
            rw [rat_div_le_div_iff hZpos hHpos]
            have hle' : H ≤ H + T := by
              have := Rat.add_le_add_left (c := H).mpr hTnonneg
              have hz : H + 0 = H := by grind
              rw [hz] at this
              exact this
            exact Rat.mul_le_mul_of_nonneg_left hle' (Rat.le_of_lt (hw i))
          have hnonpos : w i / (H + T) - w i / H ≤ 0 := by
            have hsub := rat_sub_nonneg_of_le hle
            have := Rat.add_le_add_right (c := w i / (H + T) - w i / H).mpr hsub
            have hL : 0 + (w i / (H + T) - w i / H) = w i / (H + T) - w i / H := by grind
            have hR : (w i / H - w i / (H + T)) + (w i / (H + T) - w i / H) = 0 := by grind
            rw [hL, hR] at this
            exact this
          rw [rat_abs_of_nonpos hnonpos]
          grind
        · simp only [h, ite_false, Rat.zero_add]
          have hsub0 : w i / (H + T) - 0 = w i / (H + T) := by grind
          rw [hsub0]
          exact rat_abs_of_nonneg (rat_div_nonneg (Rat.le_of_lt (hw i)) hZpos)
      rw [hpt, sumRat_add]
      have h1 : sumRat (fun i : Fin N => if i.val < K then w i / H - w i / (H + T) else 0) =
                H / H - H / (H + T) := by
        have hc : (fun i : Fin N => if i.val < K then w i / H - w i / (H + T) else 0) =
                  (fun i : Fin N => (if i.val < K then w i else 0) / H -
                                    (if i.val < K then w i else 0) / (H + T)) := by
          funext i; by_cases h : i.val < K <;> simp only [h, ite_true, ite_false, Rat.div_def] <;> grind
        rw [hc, sumRat_sub, sumRat_div_right, sumRat_div_right]
      have h2 : sumRat (fun i : Fin N => if i.val < K then 0 else w i / (H + T)) =
                T / (H + T) := by
        have hc : (fun i : Fin N => if i.val < K then 0 else w i / (H + T)) =
                  (fun i : Fin N => (if i.val < K then 0 else w i) / (H + T)) := by
          funext i; by_cases h : i.val < K <;> simp only [h, ite_true, ite_false, Rat.div_def] <;> grind
        rw [hc, sumRat_div_right]
      rw [h1, h2, rat_div_self (rat_ne_zero_of_pos hHpos)]
      have h1z : (1 : Rat) = (H + T) / (H + T) := (rat_div_self (rat_ne_zero_of_pos hZpos)).symm
      rw [h1z]
      simp only [Rat.div_def]
      grind
    refine ⟨hl1_eq, ?_⟩
    rw [hl1_eq, rat_div_le_div_iff hZpos hDenPos]
    have hcross : T * ((K : Rat) * E) ≤ H * ((N - K : Nat) : Rat) := by
      have hL : T * ((K : Rat) * E) =
                sumRat (fun i : Fin N => sumRat (fun j : Fin N =>
                  if i.val < K then (if j.val < K then 0 else w j * E) else 0)) := by
        have h1 : (fun i : Fin N => sumRat (fun j : Fin N =>
                    if i.val < K then (if j.val < K then 0 else w j * E) else 0)) =
                  (fun i : Fin N => (if i.val < K then (1 : Rat) else 0) * (T * E)) := by
          funext i
          by_cases hi : i.val < K
          · simp only [hi, ite_true, Rat.one_mul]
            have hc : (fun j : Fin N => if j.val < K then 0 else w j * E) =
                      (fun j : Fin N => (if j.val < K then 0 else w j) * E) := by
              funext j; by_cases hj : j.val < K <;> simp only [hj, ite_true, ite_false] <;> grind
            rw [hc, sumRat_mul_right]
          · simp only [hi, ite_false, Rat.zero_mul]
            exact (sumRat_const N 0).trans (by grind)
        rw [h1, sumRat_mul_right, sumRat_count_lt N K hKN]
        grind
      have hR : H * ((N - K : Nat) : Rat) =
                sumRat (fun i : Fin N => sumRat (fun j : Fin N =>
                  if i.val < K then (if j.val < K then 0 else w i) else 0)) := by
        have h1 : (fun i : Fin N => sumRat (fun j : Fin N =>
                    if i.val < K then (if j.val < K then 0 else w i) else 0)) =
                  (fun i : Fin N => (if i.val < K then w i else 0) * ((N - K : Nat) : Rat)) := by
          funext i
          by_cases hi : i.val < K
          · simp only [hi, ite_true]
            have hc : (fun j : Fin N => if j.val < K then 0 else w i) =
                      (fun j : Fin N => (if j.val < K then (0 : Rat) else 1) * w i) := by
              funext j; by_cases hj : j.val < K <;> simp only [hj, ite_true, ite_false] <;> grind
            rw [hc, sumRat_mul_right, sumRat_count_ge N K hKN]
            grind
          · simp only [hi, ite_false, Rat.zero_mul]
            exact (sumRat_const N 0).trans (by grind)
        rw [h1, sumRat_mul_right]
      rw [hL, hR]
      apply sumRat_le_sumRat
      intro i
      apply sumRat_le_sumRat
      intro j
      by_cases hi : i.val < K
      · by_cases hj : j.val < K
        · simp [hi, hj]
        · simp only [hi, hj, ite_true, ite_false]
          exact hgap i j hi (by omega)
      · simp [hi]
    have h2 : 2 * (T * ((K : Rat) * E)) ≤ 2 * (H * ((N - K : Nat) : Rat)) :=
      Rat.mul_le_mul_of_nonneg_left hcross (by decide)
    have hEqL : 2 * T * ((K : Rat) * E + ((N - K : Nat) : Rat)) =
                2 * (T * ((K : Rat) * E)) + 2 * T * ((N - K : Nat) : Rat) := by grind
    have hEqR : 2 * ((N - K : Nat) : Rat) * (H + T) =
                2 * (H * ((N - K : Nat) : Rat)) + 2 * T * ((N - K : Nat) : Rat) := by grind
    rw [hEqL, hEqR]
    exact Rat.add_le_add_right.mpr h2
  refine ⟨hmain, ?_⟩
  let wStar : Fin N → Rat := fun i => if i.val < K then E else 1
  have hwStar : ∀ i, 0 < wStar i := by
    intro i; dsimp [wStar]
    by_cases h : i.val < K
    · simp [h, hE]
    · simp [h]; decide
  have hgapStar : ∀ i j : Fin N, i.val < K → K ≤ j.val → wStar j * E ≤ wStar i := by
    intro i j hi hj
    have hj' : ¬ (j.val < K) := by omega
    simp only [wStar, hi, hj', ite_true, ite_false, Rat.one_mul]
    exact Rat.le_refl
  refine ⟨wStar, hwStar, hgapStar, ?_⟩
  have heq := (hmain wStar hwStar hgapStar).1
  rw [heq]
  have hH : sumRat (fun i : Fin N => if i.val < K then wStar i else 0) = (K : Rat) * E := by
    have hc : (fun i : Fin N => if i.val < K then wStar i else 0) =
              (fun i : Fin N => (if i.val < K then (1 : Rat) else 0) * E) := by
      funext i; dsimp [wStar]; by_cases h : i.val < K <;> simp only [h, ite_true, ite_false] <;> grind
    rw [hc, sumRat_mul_right, sumRat_count_lt N K hKN]
  have hT : sumRat (fun i : Fin N => if i.val < K then 0 else wStar i) = ((N - K : Nat) : Rat) := by
    have hc : (fun i : Fin N => if i.val < K then 0 else wStar i) =
              (fun i : Fin N => if i.val < K then (0 : Rat) else 1) := by
      funext i; dsimp [wStar]; by_cases h : i.val < K <;> simp [h]
    rw [hc, sumRat_count_ge N K hKN]
  rw [hH, hT]

/-! ## Theorem 6: Exact Quantized-Logit (±ε) Softmax L1 Law -/

theorem softmax_quantized_logit_l1_exact (N : Nat) (hN : 2 ≤ N)
    (R : Rat) (hR : 1 ≤ R) :
    (∀ (w w' : Fin N → Rat), (∀ i, 0 < w i) → (∀ i, 0 < w' i) →
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) →
      l1DistRat (softmaxRat w) (softmaxRat w') ≤ (2 * (R - 1)) / (R + 1)) ∧
    (∃ (w w' : Fin N → Rat), (∀ i, 0 < w i) ∧ (∀ i, 0 < w' i) ∧
      (∀ i, w i ≤ R * w' i ∧ w' i ≤ R * w i) ∧
      l1DistRat (softmaxRat w) (softmaxRat w') = (2 * (R - 1)) / (R + 1)) := by
  have hRpos : 0 < R := rat_lt_of_lt_of_le (by decide) hR
  have hRp1 : 0 < R + 1 := by
    have hadd := rat_add_lt_add_of_lt_of_le hRpos (by decide : (0 : Rat) ≤ 1)
    have hz : (0 : Rat) + 0 = 0 := by grind
    rw [hz] at hadd
    exact hadd
  have hRm1 : 0 ≤ R - 1 := rat_sub_nonneg_of_le hR
  constructor
  · intro w w' hw hw' hpert
    let Z := sumRat w
    let Z' := sumRat w'
    have hZpos : 0 < Z := sumRat_pos_of_mem w (fun i => Rat.le_of_lt (hw i)) ⟨0, by omega⟩ (hw ⟨0, by omega⟩)
    have hZ'pos : 0 < Z' := sumRat_pos_of_mem w' (fun i => Rat.le_of_lt (hw' i)) ⟨0, by omega⟩ (hw' ⟨0, by omega⟩)
    let p := softmaxRat w
    let p' := softmaxRat w'
    let W_A := sumRat (fun i : Fin N => if p' i ≤ p i then w i else 0)
    let W_B := sumRat (fun i : Fin N => if p' i ≤ p i then 0 else w i)
    let W'_A := sumRat (fun i : Fin N => if p' i ≤ p i then w' i else 0)
    let W'_B := sumRat (fun i : Fin N => if p' i ≤ p i then 0 else w' i)
    let a := W_A / Z
    let b := W_B / Z
    let a' := W'_A / Z'
    let b' := W'_B / Z'
    have hW_sum : W_A + W_B = Z := by
      change sumRat (fun i : Fin N => if p' i ≤ p i then w i else 0) +
             sumRat (fun i : Fin N => if p' i ≤ p i then 0 else w i) = sumRat w
      rw [← sumRat_add]
      congr 1; funext i; by_cases h : p' i ≤ p i <;> simp only [h, ite_true, ite_false] <;> grind
    have hW'_sum : W'_A + W'_B = Z' := by
      change sumRat (fun i : Fin N => if p' i ≤ p i then w' i else 0) +
             sumRat (fun i : Fin N => if p' i ≤ p i then 0 else w' i) = sumRat w'
      rw [← sumRat_add]
      congr 1; funext i; by_cases h : p' i ≤ p i <;> simp only [h, ite_true, ite_false] <;> grind
    have hab : a + b = 1 := by
      change W_A / Z + W_B / Z = 1
      simp only [Rat.div_def]
      rw [← Rat.add_mul, hW_sum, Rat.mul_inv_cancel Z (rat_ne_zero_of_pos hZpos)]
    have ha'b' : a' + b' = 1 := by
      change W'_A / Z' + W'_B / Z' = 1
      simp only [Rat.div_def]
      rw [← Rat.add_mul, hW'_sum, Rat.mul_inv_cancel Z' (rat_ne_zero_of_pos hZ'pos)]
    have hWA0 : 0 ≤ W_A := sumRat_nonneg _ (fun i => by by_cases h : p' i ≤ p i <;> simp [h, Rat.le_of_lt (hw i)])
    have hWB0 : 0 ≤ W_B := sumRat_nonneg _ (fun i => by by_cases h : p' i ≤ p i <;> simp [h, Rat.le_of_lt (hw i)])
    have hW'A0 : 0 ≤ W'_A := sumRat_nonneg _ (fun i => by by_cases h : p' i ≤ p i <;> simp [h, Rat.le_of_lt (hw' i)])
    have hW'B0 : 0 ≤ W'_B := sumRat_nonneg _ (fun i => by by_cases h : p' i ≤ p i <;> simp [h, Rat.le_of_lt (hw' i)])
    have hb0 : 0 ≤ b := rat_div_nonneg hWB0 hZpos
    have hl1 : l1DistRat p p' = 2 * (a - a') := by
      simp only [l1DistRat]
      have hpt :
          (fun i : Fin N => (p i - p' i).abs) =
          (fun i : Fin N => (if p' i ≤ p i then p i - p' i else 0) +
                            (if p' i ≤ p i then 0 else p' i - p i)) := by
        funext i
        by_cases h : p' i ≤ p i
        · simp only [h, ite_true, Rat.add_zero]
          exact rat_abs_of_nonneg (rat_sub_nonneg_of_le h)
        · simp only [h, ite_false, Rat.zero_add]
          have hlt : p i < p' i := Rat.not_le.mp h
          have hnp : p i - p' i ≤ 0 := by
            have hsub := rat_sub_nonneg_of_le (Rat.le_of_lt hlt)
            have := Rat.add_le_add_right (c := p i - p' i).mpr hsub
            have hL : 0 + (p i - p' i) = p i - p' i := by grind
            have hR : (p' i - p i) + (p i - p' i) = 0 := by grind
            rw [hL, hR] at this
            exact this
          rw [rat_abs_of_nonpos hnp]
          grind
      rw [hpt, sumRat_add]
      have h1 : sumRat (fun i : Fin N => if p' i ≤ p i then p i - p' i else 0) = a - a' := by
        have hc : (fun i : Fin N => if p' i ≤ p i then p i - p' i else 0) =
                  (fun i : Fin N => (if p' i ≤ p i then w i else 0) / Z -
                                    (if p' i ≤ p i then w' i else 0) / Z') := by
          funext i; by_cases h : p' i ≤ p i
          · simp only [h, ite_true]; rfl
          · simp only [h, ite_false, Rat.div_def]; grind
        rw [hc, sumRat_sub, sumRat_div_right, sumRat_div_right]
      have h2 : sumRat (fun i : Fin N => if p' i ≤ p i then 0 else p' i - p i) = b' - b := by
        have hc : (fun i : Fin N => if p' i ≤ p i then 0 else p' i - p i) =
                  (fun i : Fin N => (if p' i ≤ p i then 0 else w' i) / Z' -
                                    (if p' i ≤ p i then 0 else w i) / Z) := by
          funext i; by_cases h : p' i ≤ p i
          · simp only [h, ite_true, Rat.div_def]; grind
          · simp only [h, ite_false]; rfl
        rw [hc, sumRat_sub, sumRat_div_right, sumRat_div_right]
      rw [h1, h2]
      grind
    have hA_le : W_A ≤ R * W'_A := by
      change sumRat (fun i : Fin N => if p' i ≤ p i then w i else 0) ≤
             R * sumRat (fun i : Fin N => if p' i ≤ p i then w' i else 0)
      rw [← sumRat_mul_left]
      apply sumRat_le_sumRat
      intro i
      by_cases h : p' i ≤ p i
      · simp only [h, ite_true]; exact (hpert i).1
      · simp only [h, ite_false, Rat.mul_zero]; exact Rat.le_refl
    have hB_le : W'_B ≤ R * W_B := by
      change sumRat (fun i : Fin N => if p' i ≤ p i then 0 else w' i) ≤
             R * sumRat (fun i : Fin N => if p' i ≤ p i then 0 else w i)
      rw [← sumRat_mul_left]
      apply sumRat_le_sumRat
      intro i
      by_cases h : p' i ≤ p i
      · simp only [h, ite_true, Rat.mul_zero]; exact Rat.le_refl
      · simp only [h, ite_false]; exact (hpert i).2
    have hprodW : W_A * W'_B ≤ (R * W'_A) * (R * W_B) := by
      have h1 := Rat.mul_le_mul_of_nonneg_right hA_le hW'B0
      have h2 := Rat.mul_le_mul_of_nonneg_left hB_le (rat_mul_nonneg (Rat.le_of_lt hRpos) hW'A0)
      exact Rat.le_trans h1 h2
    have hprod : a * b' ≤ (R * R) * a' * b := by
      have hinv := rat_inv_pos (rat_mul_pos hZpos hZ'pos)
      have h1 := Rat.mul_le_mul_of_nonneg_right hprodW (Rat.le_of_lt hinv)
      have hL : W_A * W'_B * (Z * Z')⁻¹ = a * b' := by
        simp only [a, b', Rat.div_def, rat_inv_mul_inv (rat_ne_zero_of_pos hZpos) (rat_ne_zero_of_pos hZ'pos)]
        grind
      have hR' : (R * W'_A) * (R * W_B) * (Z * Z')⁻¹ = (R * R) * a' * b := by
        simp only [a', b, Rat.div_def, rat_inv_mul_inv (rat_ne_zero_of_pos hZpos) (rat_ne_zero_of_pos hZ'pos)]
        grind
      rw [hL, hR'] at h1
      exact h1
    have hDpos : 0 < (R * R) * b + a := by
      have hR2 : 1 ≤ R * R := by
        have h1 := Rat.mul_le_mul_of_nonneg_left hR (Rat.le_of_lt hRpos)
        have h2 : R * 1 = R := by grind
        rw [h2] at h1
        exact Rat.le_trans hR h1
      have h1 : 1 * b ≤ (R * R) * b := Rat.mul_le_mul_of_nonneg_right hR2 hb0
      have h1' : b ≤ (R * R) * b := by
        have : 1 * b = b := by grind
        rw [this] at h1; exact h1
      have h2 : b + a ≤ (R * R) * b + a := Rat.add_le_add_right.mpr h1'
      have hba : b + a = 1 := by grind
      rw [hba] at h2
      exact rat_lt_of_lt_of_le (by decide) h2
    have hstep1 : (a - a') * ((R * R) * b + a) ≤ (R * R - 1) * a * b := by
      have hsub := rat_sub_nonneg_of_le hprod
      have hid : (R * R - 1) * a * b - (a - a') * ((R * R) * b + a) =
                 (R * R) * a' * b - a * b' := by
        have hb'eq : b' = 1 - a' := by grind
        rw [hb'eq]
        grind
      apply rat_le_of_sub_nonneg
      rw [hid]
      exact hsub
    have hstep2 : (R + 1) * ((R * R - 1) * a * b) ≤ (R - 1) * ((R * R) * b + a) := by
      have hsos : 0 ≤ (R - 1) * ((R * b - a) * (R * b - a)) :=
        rat_mul_nonneg hRm1 (rat_sq_nonneg (R * b - a))
      have hid : (R - 1) * ((R * R) * b + a) - (R + 1) * ((R * R - 1) * a * b) =
                 (R - 1) * ((R * b - a) * (R * b - a)) := by
        have h1 : b = 1 - a := by grind
        rw [h1]
        grind
      apply rat_le_of_sub_nonneg
      rw [hid]
      exact hsos
    have hcomb : (R + 1) * (a - a') * ((R * R) * b + a) ≤ (R - 1) * ((R * R) * b + a) := by
      have h1 := Rat.mul_le_mul_of_nonneg_left hstep1 (Rat.le_of_lt hRp1)
      have h2 := Rat.le_trans h1 hstep2
      have hL : (R + 1) * ((a - a') * ((R * R) * b + a)) = (R + 1) * (a - a') * ((R * R) * b + a) := by grind
      rw [← hL]
      exact h2
    have hcancel : (R + 1) * (a - a') ≤ R - 1 := by
      have hinv := rat_inv_pos hDpos
      have h1 := Rat.mul_le_mul_of_nonneg_right hcomb (Rat.le_of_lt hinv)
      have hL : (R + 1) * (a - a') * ((R * R) * b + a) * ((R * R) * b + a)⁻¹ = (R + 1) * (a - a') := by
        have : (R + 1) * (a - a') * ((R * R) * b + a) * ((R * R) * b + a)⁻¹ =
               (R + 1) * (a - a') * (((R * R) * b + a) * ((R * R) * b + a)⁻¹) := by grind
        rw [this, Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hDpos)]
        grind
      have hR' : (R - 1) * ((R * R) * b + a) * ((R * R) * b + a)⁻¹ = R - 1 := by
        have : (R - 1) * ((R * R) * b + a) * ((R * R) * b + a)⁻¹ =
               (R - 1) * (((R * R) * b + a) * ((R * R) * b + a)⁻¹) := by grind
        rw [this, Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hDpos)]
        grind
      rw [hL, hR'] at h1
      exact h1
    change l1DistRat p p' ≤ (2 * (R - 1)) / (R + 1)
    rw [hl1]
    have hdiv : (2 * (a - a')) / 1 ≤ (2 * (R - 1)) / (R + 1) := by
      rw [rat_div_le_div_iff (by decide) hRp1]
      have h2 := Rat.mul_le_mul_of_nonneg_left hcancel (by decide : (0 : Rat) ≤ 2)
      have hEqL : 2 * (a - a') * (R + 1) = 2 * ((R + 1) * (a - a')) := by grind
      have hEqR : 2 * (R - 1) * 1 = 2 * (R - 1) := by grind
      rw [hEqL, hEqR]
      exact h2
    have hd1 : (2 * (a - a')) / 1 = 2 * (a - a') := by
      rw [Rat.div_def]
      have hinv1 : (1 : Rat)⁻¹ = 1 := by
        have h := Rat.mul_inv_cancel (1 : Rat) (by decide)
        rw [Rat.one_mul] at h
        exact h
      rw [hinv1]
      grind
    rw [hd1] at hdiv
    exact hdiv
  · -- Exact sharpness witness for EVERY N ≥ 2
    have hNm1_pos : (0 : Rat) < ((N - 1 : Nat) : Rat) := by
      have : (0 : Nat) < N - 1 := by omega
      exact Rat.natCast_lt_natCast.mpr this
    let wStar : Fin N → Rat := fun i => if i.val = 0 then R else 1 / ((N - 1 : Nat) : Rat)
    let w'Star : Fin N → Rat := fun i => if i.val = 0 then 1 else R / ((N - 1 : Nat) : Rat)
    have hwStar : ∀ i, 0 < wStar i := by
      intro i; dsimp [wStar]
      by_cases h : i.val = 0
      · simp [h, hRpos]
      · simp [h]; exact rat_div_pos (by decide) hNm1_pos
    have hw'Star : ∀ i, 0 < w'Star i := by
      intro i; dsimp [w'Star]
      by_cases h : i.val = 0
      · simp [h]; decide
      · simp [h]; exact rat_div_pos hRpos hNm1_pos
    have hpertStar : ∀ i, wStar i ≤ R * w'Star i ∧ w'Star i ≤ R * wStar i := by
      intro i; dsimp [wStar, w'Star]
      by_cases h : i.val = 0
      · simp only [h, ite_true, Rat.mul_one]
        refine ⟨Rat.le_refl, ?_⟩
        have h1 := Rat.mul_le_mul_of_nonneg_left hR (Rat.le_of_lt hRpos)
        have h2 : R * 1 = R := by grind
        rw [h2] at h1
        exact Rat.le_trans hR h1
      · simp only [h, ite_false]
        have h1 : 1 ≤ R * R := by
          have h' := Rat.mul_le_mul_of_nonneg_left hR (Rat.le_of_lt hRpos)
          have h1' : R * 1 = R := by grind
          rw [h1'] at h'
          exact Rat.le_trans hR h'
        constructor
        · have : R * (R / ((N - 1 : Nat) : Rat)) = (R * R) / ((N - 1 : Nat) : Rat) := by
            simp [Rat.div_def]; grind
          rw [this, rat_div_le_div_iff hNm1_pos hNm1_pos]
          exact Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hNm1_pos)
        · have : R * (1 / ((N - 1 : Nat) : Rat)) = R / ((N - 1 : Nat) : Rat) := by
            simp only [Rat.div_def]; grind
          rw [this]
          exact Rat.le_refl
    refine ⟨wStar, w'Star, hwStar, hw'Star, hpertStar, ?_⟩
    have hcount0 : sumRat (fun i : Fin N => if i.val = 0 then (1 : Rat) else 0) = 1 := by
      have hc : (fun i : Fin N => if i.val = 0 then (1 : Rat) else 0) =
                (fun i : Fin N => if i.val < 1 then (1 : Rat) else 0) := by
        funext i; by_cases h : i.val = 0 <;> simp [h, show (i.val < 1) ↔ (i.val = 0) by omega]
      rw [hc, sumRat_count_lt N 1 (by omega)]
      rfl
    have hcountRest : sumRat (fun i : Fin N => if i.val = 0 then (0 : Rat) else 1) = ((N - 1 : Nat) : Rat) := by
      have hc : (fun i : Fin N => if i.val = 0 then (0 : Rat) else 1) =
                (fun i : Fin N => if i.val < 1 then (0 : Rat) else 1) := by
        funext i; by_cases h : i.val = 0 <;> simp [h, show (i.val < 1) ↔ (i.val = 0) by omega]
      rw [hc, sumRat_count_ge N 1 (by omega)]
    have hZw : sumRat wStar = R + 1 := by
      have hc : wStar = (fun i : Fin N =>
          (if i.val = 0 then (1 : Rat) else 0) * R +
          (if i.val = 0 then (0 : Rat) else 1) * (1 / ((N - 1 : Nat) : Rat))) := by
        funext i; dsimp [wStar]; by_cases h : i.val = 0 <;> simp only [h, ite_true, ite_false] <;> grind
      rw [hc, sumRat_add, sumRat_mul_right, sumRat_mul_right, hcount0, hcountRest]
      rw [Rat.one_mul, Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hNm1_pos)]
    have hZw' : sumRat w'Star = R + 1 := by
      have hc : w'Star = (fun i : Fin N =>
          (if i.val = 0 then (1 : Rat) else 0) * 1 +
          (if i.val = 0 then (0 : Rat) else 1) * (R / ((N - 1 : Nat) : Rat))) := by
        funext i; dsimp [w'Star]; by_cases h : i.val = 0 <;> simp only [h, ite_true, ite_false] <;> grind
      rw [hc, sumRat_add, sumRat_mul_right, sumRat_mul_right, hcount0, hcountRest]
      rw [Rat.one_mul, Rat.div_def]
      have : ((N - 1 : Nat) : Rat) * (R * ((N - 1 : Nat) : Rat)⁻¹) =
             R * (((N - 1 : Nat) : Rat) * ((N - 1 : Nat) : Rat)⁻¹) := by grind
      rw [this, Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hNm1_pos)]
      grind
    simp only [l1DistRat, softmaxRat, hZw, hZw']
    have hpt :
        (fun i : Fin N => (wStar i / (R + 1) - w'Star i / (R + 1)).abs) =
        (fun i : Fin N =>
          (if i.val = 0 then (1 : Rat) else 0) * ((R - 1) / (R + 1)) +
          (if i.val = 0 then (0 : Rat) else 1) * ((R - 1) / (((N - 1 : Nat) : Rat) * (R + 1)))) := by
      funext i
      dsimp [wStar, w'Star]
      by_cases h : i.val = 0
      · simp only [h, ite_true, Rat.one_mul, Rat.zero_mul, Rat.add_zero]
        have hsub : R / (R + 1) - 1 / (R + 1) = (R - 1) / (R + 1) := by
          simp only [Rat.div_def]; grind
        rw [hsub]
        exact rat_abs_of_nonneg (rat_div_nonneg hRm1 hRp1)
      · simp only [h, ite_false, Rat.zero_mul, Rat.one_mul, Rat.zero_add]
        have hsub : 1 / ((N - 1 : Nat) : Rat) / (R + 1) - R / ((N - 1 : Nat) : Rat) / (R + 1) =
                    -((R - 1) / (((N - 1 : Nat) : Rat) * (R + 1))) := by
          simp only [Rat.div_def, rat_inv_mul_inv (rat_ne_zero_of_pos hNm1_pos) (rat_ne_zero_of_pos hRp1)]; grind
        rw [hsub]
        have hpos_rhs : 0 ≤ (R - 1) / (((N - 1 : Nat) : Rat) * (R + 1)) :=
          rat_div_nonneg hRm1 (rat_mul_pos hNm1_pos hRp1)
        have hnp : -((R - 1) / (((N - 1 : Nat) : Rat) * (R + 1))) ≤ 0 := by
          have := Rat.add_le_add_right (c := -((R - 1) / (((N - 1 : Nat) : Rat) * (R + 1)))).mpr hpos_rhs
          have hL : 0 + -((R - 1) / (((N - 1 : Nat) : Rat) * (R + 1))) = -((R - 1) / (((N - 1 : Nat) : Rat) * (R + 1))) := by grind
          have hR' : (R - 1) / (((N - 1 : Nat) : Rat) * (R + 1)) + -((R - 1) / (((N - 1 : Nat) : Rat) * (R + 1))) = 0 := by grind
          rw [hL, hR'] at this
          exact this
        rw [rat_abs_of_nonpos hnp]
        grind
    rw [hpt, sumRat_add, sumRat_mul_right, sumRat_mul_right, hcount0, hcountRest, Rat.one_mul]
    have hcancel_n : ((N - 1 : Nat) : Rat) * ((R - 1) / (((N - 1 : Nat) : Rat) * (R + 1))) =
                     (R - 1) / (R + 1) := by
      simp only [Rat.div_def, rat_inv_mul_inv (rat_ne_zero_of_pos hNm1_pos) (rat_ne_zero_of_pos hRp1)]
      have : ((N - 1 : Nat) : Rat) * ((R - 1) * ((R + 1)⁻¹ * ((N - 1 : Nat) : Rat)⁻¹)) =
             (((N - 1 : Nat) : Rat) * ((N - 1 : Nat) : Rat)⁻¹) * ((R - 1) * (R + 1)⁻¹) := by grind
      rw [this, Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hNm1_pos), Rat.one_mul]
    rw [hcancel_n]
    simp only [Rat.div_def]
    grind

end OctonionRopeWelch
