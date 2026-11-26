/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RingAttnKulisch.RatOrder

/-!
# Theorem 1: Exact Online-Softmax Monoid Associativity & Commutativity

Proves that over exact positive rational scale weights `w > 0`, the online-softmax
merge operation `onlineMerge : OnlineSoftmaxState → OnlineSoftmaxState → OnlineSoftmaxState`
preserves positivity, is strictly commutative and associative, preserves the exact
additive unnormalized invariants `totalDenom (s₁ ⊕ s₂) = totalDenom s₁ + totalDenom s₂`
and `totalNum (s₁ ⊕ s₂) = totalNum s₁ + totalNum s₂`, and produces the exact
order-independent normalized attention output `(w₁ * o₁ + w₂ * o₂) / (w₁ * l₁ + w₂ * l₂)`.
-/

namespace RingAttnKulisch

theorem onlineMerge_w_pos {s₁ s₂ : OnlineSoftmaxState}
    (h₁ : (0 : Rat) < s₁.w) (h₂ : (0 : Rat) < s₂.w) :
    (0 : Rat) < (onlineMerge s₁ s₂).w := by
  unfold onlineMerge
  dsimp only
  split
  · exact h₂
  · exact h₁

theorem onlineMerge_comm (s₁ s₂ : OnlineSoftmaxState) :
    onlineMerge s₁ s₂ = onlineMerge s₂ s₁ := by
  unfold onlineMerge
  dsimp only
  by_cases h12 : s₁.w ≤ s₂.w
  · by_cases h21 : s₂.w ≤ s₁.w
    · have heq : s₁.w = s₂.w := Rat.le_antisymm h12 h21
      simp only [heq]
      congr 1 <;> grind
    · simp only [h12, h21, ↓reduceIte]
      congr 1 <;> grind
  · have h21 : s₂.w ≤ s₁.w := by
      cases Rat.le_total (a := s₂.w) (b := s₁.w) with
      | inl h => exact h
      | inr h => exact absurd h h12
    simp only [h12, h21, ↓reduceIte]
    congr 1 <;> grind

theorem onlineMerge_totalDenom {s₁ s₂ : OnlineSoftmaxState}
    (h₁ : (0 : Rat) < s₁.w) (h₂ : (0 : Rat) < s₂.w) :
    totalDenom (onlineMerge s₁ s₂) = totalDenom s₁ + totalDenom s₂ := by
  unfold totalDenom onlineMerge
  dsimp only
  by_cases h12 : s₁.w ≤ s₂.w
  · simp only [h12, ↓reduceIte]
    have hne : s₂.w ≠ 0 := Rat.ne_of_gt h₂
    have hmul : ∀ a b : Rat, s₂.w * ((a / s₂.w) * b) = a * b := by
      intro a b
      rw [Rat.div_def]
      have : s₂.w * (a * s₂.w⁻¹ * b) = (s₂.w * s₂.w⁻¹) * (a * b) := by grind
      rw [this, Rat.mul_inv_cancel _ hne, Rat.one_mul]
    rw [Rat.mul_add, hmul, hmul]
  · simp only [h12, ↓reduceIte]
    have hne : s₁.w ≠ 0 := Rat.ne_of_gt h₁
    have hmul : ∀ a b : Rat, s₁.w * ((a / s₁.w) * b) = a * b := by
      intro a b
      rw [Rat.div_def]
      have : s₁.w * (a * s₁.w⁻¹ * b) = (s₁.w * s₁.w⁻¹) * (a * b) := by grind
      rw [this, Rat.mul_inv_cancel _ hne, Rat.one_mul]
    rw [Rat.mul_add, hmul, hmul]

theorem onlineMerge_totalNum {s₁ s₂ : OnlineSoftmaxState}
    (h₁ : (0 : Rat) < s₁.w) (h₂ : (0 : Rat) < s₂.w) :
    totalNum (onlineMerge s₁ s₂) = totalNum s₁ + totalNum s₂ := by
  unfold totalNum onlineMerge
  dsimp only
  by_cases h12 : s₁.w ≤ s₂.w
  · simp only [h12, ↓reduceIte]
    have hne : s₂.w ≠ 0 := Rat.ne_of_gt h₂
    have hmul : ∀ a b : Rat, s₂.w * ((a / s₂.w) * b) = a * b := by
      intro a b
      rw [Rat.div_def]
      have : s₂.w * (a * s₂.w⁻¹ * b) = (s₂.w * s₂.w⁻¹) * (a * b) := by grind
      rw [this, Rat.mul_inv_cancel _ hne, Rat.one_mul]
    rw [Rat.mul_add, hmul, hmul]
  · simp only [h12, ↓reduceIte]
    have hne : s₁.w ≠ 0 := Rat.ne_of_gt h₁
    have hmul : ∀ a b : Rat, s₁.w * ((a / s₁.w) * b) = a * b := by
      intro a b
      rw [Rat.div_def]
      have : s₁.w * (a * s₁.w⁻¹ * b) = (s₁.w * s₁.w⁻¹) * (a * b) := by grind
      rw [this, Rat.mul_inv_cancel _ hne, Rat.one_mul]
    rw [Rat.mul_add, hmul, hmul]

theorem onlineMerge_normOutput {s₁ s₂ : OnlineSoftmaxState}
    (h₁ : (0 : Rat) < s₁.w) (h₂ : (0 : Rat) < s₂.w)
    (hl : totalDenom s₁ + totalDenom s₂ ≠ 0) :
    normOutput (onlineMerge s₁ s₂) =
      (totalNum s₁ + totalNum s₂) / (totalDenom s₁ + totalDenom s₂) := by
  have hm_ne : (onlineMerge s₁ s₂).w ≠ 0 := Rat.ne_of_gt (onlineMerge_w_pos h₁ h₂)
  rw [← onlineMerge_totalNum h₁ h₂, ← onlineMerge_totalDenom h₁ h₂]
  unfold normOutput totalNum totalDenom
  have hl_ne : (onlineMerge s₁ s₂).l ≠ 0 := by
    intro h0
    apply hl
    rw [← onlineMerge_totalDenom h₁ h₂]
    unfold totalDenom
    rw [h0]
    grind
  have hcancel : ∀ m o l : Rat, m ≠ 0 → l ≠ 0 → (m * o) / (m * l) = o / l := by
    intro m o l hm' hl'
    have hml : m * l ≠ 0 := by
      intro h0
      cases Rat.mul_eq_zero.mp h0 with
      | inl h => exact hm' h
      | inr h => exact hl' h
    have h1 : ((m * o) / (m * l)) * (m * l) = (o / l) * (m * l) := by
      rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ hml, Rat.mul_one]
      rw [Rat.div_def]
      have : o * l⁻¹ * (m * l) = m * o * (l⁻¹ * l) := by grind
      rw [this, Rat.inv_mul_cancel _ hl', Rat.mul_one]
    have := congrArg (· * (m * l)⁻¹) h1
    simp only [Rat.mul_assoc, Rat.mul_inv_cancel _ hml, Rat.mul_one] at this
    exact this
  exact (hcancel _ _ _ hm_ne hl_ne).symm

theorem onlineMerge_w_assoc (a b c : Rat) :
    (if (if a ≤ b then b else a) ≤ c then c else (if a ≤ b then b else a)) =
    (if a ≤ (if b ≤ c then c else b) then (if b ≤ c then c else b) else a) := by
  by_cases hab : a ≤ b <;> by_cases hbc : b ≤ c <;> by_cases hac : a ≤ c
  · simp [hab, hbc, hac]
  · exact absurd (Rat.le_trans hab hbc) hac
  · simp [hab, hbc]
  · simp [hab, hbc]
  · simp [hab, hbc, hac]
  · simp [hab, hbc, hac]
  · have hba : b ≤ a := by
      cases Rat.le_total (a := b) (b := a) with
      | inl h => exact h
      | inr h => exact absurd h hab
    have hcb : c ≤ b := by
      cases Rat.le_total (a := c) (b := b) with
      | inl h => exact h
      | inr h => exact absurd h hbc
    have hca : c ≤ a := Rat.le_trans hcb hba
    have heq : a = c := Rat.le_antisymm hac hca
    have hbc_eq : b = c := Rat.le_antisymm (by rw [← heq]; exact hba) hcb
    simp [heq, hbc_eq]
  · simp [hab, hbc, hac]

theorem onlineMerge_assoc {s₁ s₂ s₃ : OnlineSoftmaxState}
    (h₁ : (0 : Rat) < s₁.w) (h₂ : (0 : Rat) < s₂.w) (h₃ : (0 : Rat) < s₃.w) :
    onlineMerge (onlineMerge s₁ s₂) s₃ = onlineMerge s₁ (onlineMerge s₂ s₃) := by
  have hw : (onlineMerge (onlineMerge s₁ s₂) s₃).w = (onlineMerge s₁ (onlineMerge s₂ s₃)).w :=
    onlineMerge_w_assoc s₁.w s₂.w s₃.w
  have hm_pos : (0 : Rat) < (onlineMerge (onlineMerge s₁ s₂) s₃).w :=
    onlineMerge_w_pos (onlineMerge_w_pos h₁ h₂) h₃
  have hm_ne : (onlineMerge (onlineMerge s₁ s₂) s₃).w ≠ 0 := Rat.ne_of_gt hm_pos
  have hd_eq : totalDenom (onlineMerge (onlineMerge s₁ s₂) s₃) =
      totalDenom (onlineMerge s₁ (onlineMerge s₂ s₃)) := by
    rw [onlineMerge_totalDenom (onlineMerge_w_pos h₁ h₂) h₃,
        onlineMerge_totalDenom h₁ h₂,
        onlineMerge_totalDenom h₁ (onlineMerge_w_pos h₂ h₃),
        onlineMerge_totalDenom h₂ h₃]
    grind
  have hn_eq : totalNum (onlineMerge (onlineMerge s₁ s₂) s₃) =
      totalNum (onlineMerge s₁ (onlineMerge s₂ s₃)) := by
    rw [onlineMerge_totalNum (onlineMerge_w_pos h₁ h₂) h₃,
        onlineMerge_totalNum h₁ h₂,
        onlineMerge_totalNum h₁ (onlineMerge_w_pos h₂ h₃),
        onlineMerge_totalNum h₂ h₃]
    grind
  unfold totalDenom at hd_eq
  unfold totalNum at hn_eq
  rw [← hw] at hd_eq hn_eq
  have hl : (onlineMerge (onlineMerge s₁ s₂) s₃).l = (onlineMerge s₁ (onlineMerge s₂ s₃)).l := by
    have := congrArg ((onlineMerge (onlineMerge s₁ s₂) s₃).w⁻¹ * ·) hd_eq
    simp only [← Rat.mul_assoc, Rat.inv_mul_cancel _ hm_ne, Rat.one_mul] at this
    exact this
  have ho : (onlineMerge (onlineMerge s₁ s₂) s₃).o = (onlineMerge s₁ (onlineMerge s₂ s₃)).o := by
    have := congrArg ((onlineMerge (onlineMerge s₁ s₂) s₃).w⁻¹ * ·) hn_eq
    simp only [← Rat.mul_assoc, Rat.inv_mul_cancel _ hm_ne, Rat.one_mul] at this
    exact this
  cases lhs : onlineMerge (onlineMerge s₁ s₂) s₃
  cases rhs : onlineMerge s₁ (onlineMerge s₂ s₃)
  rw [lhs, rhs] at hw hl ho
  dsimp only at hw hl ho
  rw [hw, hl, ho]

/-- Headline Theorem 1: Exact online-softmax monoid associativity, commutativity,
    positivity preservation, additive unnormalized invariants, and normalized output
    invariance over arbitrary positive rational weights `w > 0`. -/
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
        (totalNum s₁ + totalNum s₂) / (totalDenom s₁ + totalDenom s₂)) := by
  refine ⟨onlineMerge_comm, fun s₁ s₂ h₁ h₂ => onlineMerge_w_pos h₁ h₂,
    fun s₁ s₂ s₃ h₁ h₂ h₃ => onlineMerge_assoc h₁ h₂ h₃,
    fun s₁ s₂ h₁ h₂ => ⟨onlineMerge_totalDenom h₁ h₂, onlineMerge_totalNum h₁ h₂⟩,
    fun s₁ s₂ h₁ h₂ hl => onlineMerge_normOutput h₁ h₂ hl⟩

end RingAttnKulisch
