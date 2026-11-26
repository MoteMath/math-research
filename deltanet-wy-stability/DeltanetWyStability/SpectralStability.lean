/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltanetWyStability.RatAlg

/-!
# Theorem 1: Exact Spectral Stability Characterization for Gated DeltaNet
-/

namespace DeltanetWyStability

/-- Exact rank-1 quadratic form identity:
    `‖α (v - β ⟨k, v⟩ k)‖² = α² (‖v‖² - β (2 - β ‖k‖²) ⟨k, v⟩²)`. -/
theorem normSq_deltaNetStep {d : Nat} (α β : Rat) (k v : Fin d → Rat) :
    normSq (deltaNetStep α β k v) =
      (α * α) * (normSq v - β * (2 - β * normSq k) * (dot k v * dot k v)) := by
  unfold normSq deltaNetStep dot
  let p := sumFin (fun i => k i * v i)
  have h1 : sumFin (fun i => (α * (v i - β * p * k i)) * (α * (v i - β * p * k i))) =
      sumFin (fun i => (α * α) * (v i * v i - (2 * β * p) * (k i * v i) + (β * β * p * p) * (k i * k i))) := by
    apply sumFin_congr
    intro i
    grind
  change sumFin (fun i => (α * (v i - β * p * k i)) * (α * (v i - β * p * k i))) =
    (α * α) * (sumFin (fun i => v i * v i) - β * (2 - β * sumFin (fun i => k i * k i)) * (p * p))
  rw [h1, sumFin_mul_left, sumFin_add_fn, sumFin_sub_fn, sumFin_mul_left, sumFin_mul_left]
  change (α * α) * (sumFin (fun i => v i * v i) - (2 * β * p) * p + (β * β * p * p) * sumFin (fun i => k i * k i)) =
    (α * α) * (sumFin (fun i => v i * v i) - β * (2 - β * sumFin (fun i => k i * k i)) * (p * p))
  grind

/-- Pure-`Init` Cauchy–Schwarz inequality over `Fin d → Rat`. -/
theorem cauchy_schwarz_sq {d : Nat} (k v : Fin d → Rat) :
    dot k v * dot k v ≤ normSq k * normSq v := by
  let r := normSq k
  let p := dot k v
  change p * p ≤ r * normSq v
  have hr0 : 0 ≤ r := normSq_nonneg k
  by_cases hr : r = 0
  · -- When `normSq k = 0`, every coordinate `k i = 0`, so `dot k v = 0`.
    have hk0 : ∀ i : Fin d, k i = 0 := by
      intro i
      have hsplit := sumFin_split_at i (fun j => k j * k j)
      have hrest : 0 ≤ sumFin (fun j => if j = i then 0 else k j * k j) := by
        apply sumFin_nonneg
        intro j
        by_cases hj : j = i
        · simp [hj]
        · simp [hj]; exact rat_sq_nonneg (k j)
      have hsq0 : k i * k i ≤ 0 := by
        have hsum : sumFin (fun j => k j * k j) = 0 := hr
        grind
      have hsq_nonneg : 0 ≤ k i * k i := rat_sq_nonneg (k i)
      have hmul0 : k i * k i = 0 := by grind
      rcases Rat.mul_eq_zero.mp hmul0 with h | h <;> exact h
    have hp0 : p = 0 := by
      show sumFin (fun i => k i * v i) = 0
      rw [sumFin_congr (g := fun _ => 0)]
      · exact sumFin_zero d
      · intro i; rw [hk0 i]; grind
    rw [hp0, hr]
    grind
  · have hrpos : 0 < r := by grind
    let w : Fin d → Rat := fun i => r * v i - p * k i
    have hw : 0 ≤ normSq w := normSq_nonneg w
    have hw_eq : normSq w = r * (r * normSq v - p * p) := by
      unfold normSq dot w
      have h1 : sumFin (fun i => (r * v i - p * k i) * (r * v i - p * k i)) =
          sumFin (fun i => (r * r) * (v i * v i) - (2 * r * p) * (k i * v i) + (p * p) * (k i * k i)) := by
        apply sumFin_congr
        intro i
        grind
      rw [h1, sumFin_add_fn, sumFin_sub_fn, sumFin_mul_left, sumFin_mul_left, sumFin_mul_left]
      have hpr : sumFin (fun i => k i * v i) = p := rfl
      have hrr : sumFin (fun i => k i * k i) = r := rfl
      rw [hpr, hrr]
      grind
    rw [hw_eq] at hw
    rcases @Rat.le_total (p * p) (r * normSq v) with hle | hgt
    · exact hle
    · have hneg : 0 ≤ -(r * (r * normSq v - p * p)) := by
        have h1 : 0 ≤ p * p - r * normSq v := by grind
        have h2 := rat_mul_nonneg (by grind : 0 ≤ r) h1
        have heq : r * (p * p - r * normSq v) = -(r * (r * normSq v - p * p)) := by grind
        grind
      have hzero : r * (r * normSq v - p * p) = 0 := by grind
      rcases Rat.mul_eq_zero.mp hzero with h1 | h2
      · grind
      · grind

/-- Headline Theorem 1: Exact Spectral Stability Characterization for Gated DeltaNet. -/
theorem deltanet_spectral_stability_iff (d : Nat) (α β : Rat)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β)
    (k : Fin d → Rat) (hk : 0 < normSq k) :
    (∀ v : Fin d → Rat, normSq (deltaNetStep α β k v) ≤ normSq v) ↔
    β * normSq k ≤ (1 + α) / α := by
  let r := normSq k
  change (∀ v : Fin d → Rat, normSq (deltaNetStep α β k v) ≤ normSq v) ↔ β * r ≤ (1 + α) / α
  have hdiv : β * r ≤ (1 + α) / α ↔ α * β * r ≤ 1 + α := by
    rw [rat_le_div_iff hα0]
    have heq : β * r * α = α * β * r := by grind
    rw [heq]
  rw [hdiv]
  constructor
  · intro hstab
    have hkk := hstab k
    rw [normSq_deltaNetStep] at hkk
    have hdot : dot k k = r := rfl
    rw [hdot] at hkk
    have hfac : (α * α) * (r - β * (2 - β * r) * (r * r)) =
        (α * (β * r - 1)) * (α * (β * r - 1)) * r := by grind
    rw [hfac] at hkk
    rcases @Rat.le_total (α * β * r) (1 + α) with hle | hgt
    · exact hle
    · by_cases heq : α * β * r = 1 + α
      · grind
      · have hstrict : 1 < α * (β * r - 1) := by grind
        have hsq1 : 1 < (α * (β * r - 1)) * (α * (β * r - 1)) := by
          have h1 := rat_mul_pos (by grind : 0 < α * (β * r - 1) - 1) (by grind : 0 < α * (β * r - 1) + 1)
          grind
        have hmul := rat_mul_pos (by grind : 0 < (α * (β * r - 1)) * (α * (β * r - 1)) - 1) hk
        grind
  · intro hbound v
    rw [normSq_deltaNetStep]
    have hv0 : 0 ≤ normSq v := normSq_nonneg v
    have hαsq : α * α ≤ 1 := by
      have h := rat_mul_le_mul_nonneg (by grind : 0 ≤ α) (by grind : 0 ≤ α) hα1 hα1
      grind
    rcases @Rat.le_total (β * r) 2 with hbr | hbr
    · have hterm : 0 ≤ β * (2 - β * r) * (dot k v * dot k v) :=
        rat_mul_nonneg (rat_mul_nonneg hβ0 (by grind : 0 ≤ 2 - β * r)) (rat_sq_nonneg (dot k v))
      have h1 : normSq v - β * (2 - β * r) * (dot k v * dot k v) ≤ normSq v := by grind
      have h2 : (α * α) * (normSq v - β * (2 - β * r) * (dot k v * dot k v)) ≤ (α * α) * normSq v :=
        Rat.mul_le_mul_of_nonneg_left h1 (rat_sq_nonneg α)
      have h3 : (α * α) * normSq v ≤ 1 * normSq v :=
        rat_mul_le_mul_of_nonneg_right hαsq hv0
      grind
    · have hcs : dot k v * dot k v ≤ r * normSq v := cauchy_schwarz_sq k v
      have hc0 : 0 ≤ β * (β * r - 2) := rat_mul_nonneg hβ0 (by grind : 0 ≤ β * r - 2)
      have h1 : β * (β * r - 2) * (dot k v * dot k v) ≤ β * (β * r - 2) * (r * normSq v) :=
        Rat.mul_le_mul_of_nonneg_left hcs hc0
      have h2 : normSq v - β * (2 - β * r) * (dot k v * dot k v) ≤
          (β * r - 1) * (β * r - 1) * normSq v := by grind
      have h3 : (α * α) * (normSq v - β * (2 - β * r) * (dot k v * dot k v)) ≤
          (α * (β * r - 1)) * (α * (β * r - 1)) * normSq v := by
        have h := Rat.mul_le_mul_of_nonneg_left h2 (rat_sq_nonneg α)
        have heq : (α * α) * ((β * r - 1) * (β * r - 1) * normSq v) =
            (α * (β * r - 1)) * (α * (β * r - 1)) * normSq v := by grind
        rw [heq] at h
        exact h
      have hpos : 0 ≤ α * (β * r - 1) := rat_mul_nonneg (by grind : 0 ≤ α) (by grind : 0 ≤ β * r - 1)
      have hle1 : α * (β * r - 1) ≤ 1 := by grind
      have hsqle1 : (α * (β * r - 1)) * (α * (β * r - 1)) ≤ 1 := by
        have h := rat_mul_le_mul_nonneg hpos hpos hle1 hle1
        grind
      have h4 : (α * (β * r - 1)) * (α * (β * r - 1)) * normSq v ≤ 1 * normSq v :=
        rat_mul_le_mul_of_nonneg_right hsqle1 hv0
      grind

end DeltanetWyStability
