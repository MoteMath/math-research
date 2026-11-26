/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RagPopcntMatryoshka.RatOrder

/-!
# Theorem 4: Hypercube Sign-WHT Automatic Spectral Normalization

Proves:
1. Every sign-quantized vector `sgn(v) ∈ {-1, +1}^D` (including `sgn(H x)` for any WHT / orthogonal
   transform `H`) has exact constant squared norm `‖sgn(v)‖_2^2 = D`, independent of `‖x‖_2` or
   spectral concentration `β`.
2. Positive scalar multiplication invariance `sgn(c · v) = sgn(v)` for all `c > 0`, making
   hypercube inner products completely immune to norm-ratio hijack.
3. Exact prefix-truncation energy loss `‖x‖_2^2 = ‖x_{<dM}‖_2^2 + ‖x_{≥dM}‖_2^2` with
   `‖x_{≥dM}‖_2^2 ≥ 0`.
4. Exact unnormalized inner-product norm-ratio hijack vs hypercube immunity: any positive-dot
   distractor `x_bad` scaled by `c > dot_M(q, x_pos) / dot_M(q, x_bad)` hijacks unnormalized
   prefix retrieval, whereas `sgn` inner-product ranking is strictly preserved for all `c > 0`.
-/

namespace RagPopcntMatryoshka

theorem normSqInt_sgnVec {D : Nat} (v : Fin D → Rat) :
    normSqInt (sgnVec v) = (D : Int) := by
  unfold normSqInt dotInt sgnVec
  have hpoint : ∀ i : Fin D,
      (if (0 : Rat) ≤ v i then (1 : Int) else -1) *
      (if (0 : Rat) ≤ v i then (1 : Int) else -1) = 1 := by
    intro i
    split <;> rfl
  rw [finSumInt_congr hpoint, finSumInt_const]
  omega

theorem sgnVec_scale_pos {D : Nat} {c : Rat} (hc : (0 : Rat) < c) (v : Fin D → Rat) :
    sgnVec (scaleRat c v) = sgnVec v := by
  funext i
  unfold sgnVec scaleRat
  by_cases hv : (0 : Rat) ≤ v i
  · have hcv : (0 : Rat) ≤ c * v i := Rat.mul_nonneg (Rat.le_of_lt hc) hv
    simp [hv, hcv]
  · have hvlt : v i < 0 := Rat.not_le.mp hv
    have hcv : ¬((0 : Rat) ≤ c * v i) := by
      intro hle
      have hneg : (0 : Rat) < c * (-v i) := rat_mul_pos hc (by
        have h := rat_sub_pos hvlt
        have e : (0 : Rat) - v i = -v i := by grind
        rw [← e]; exact h)
      have hsum := rat_add_pos_of_pos_of_nonneg hneg hle
      have e : c * (-v i) + c * v i = 0 := by grind
      rw [e] at hsum
      exact Rat.lt_irrefl hsum
    simp [hv, hcv]

theorem normSqRat_eq_prefix_add_tail {D dM : Nat} (h : dM ≤ D) (x : Fin D → Rat) :
    normSqRat x = prefixNormSqRat dM h x + tailNormSqRat dM h x := by
  unfold normSqRat dotRat prefixNormSqRat prefixDotRat tailNormSqRat
  exact finSumRat_split_le h (fun i => x i * x i)

theorem tailNormSqRat_nonneg {D dM : Nat} (h : dM ≤ D) (x : Fin D → Rat) :
    (0 : Rat) ≤ tailNormSqRat dM h x :=
  finSumRat_nonneg (fun _ => rat_sq_nonneg _)

theorem prefixDotRat_scale_right {D dM : Nat} (h : dM ≤ D) (c : Rat) (q x : Fin D → Rat) :
    prefixDotRat dM h q (scaleRat c x) = c * prefixDotRat dM h q x := by
  unfold prefixDotRat scaleRat
  rw [← finSumRat_mul_left]
  exact finSumRat_congr (fun i => by grind)

theorem norm_ratio_hijack_vs_hypercube_immunity {D dM : Nat} (h : dM ≤ D)
    (q xPos xBad : Fin D → Rat) (c : Rat)
    (hbadPos : (0 : Rat) < prefixDotRat dM h q xBad)
    (hcPos : (0 : Rat) < c)
    (hcHijack : prefixDotRat dM h q xPos / prefixDotRat dM h q xBad < c) :
    prefixDotRat dM h q xPos < prefixDotRat dM h q (scaleRat c xBad) ∧
    dotInt (sgnVec q) (sgnVec (scaleRat c xBad)) = dotInt (sgnVec q) (sgnVec xBad) := by
  constructor
  · rw [prefixDotRat_scale_right]
    rw [rat_div_lt_iff hbadPos] at hcHijack
    exact hcHijack
  · rw [sgnVec_scale_pos hcPos]

/-- Headline Theorem 4 (`hypercube_sign_wht_automatic_spectral_normalization`). -/
theorem hypercube_sign_wht_automatic_spectral_normalization :
    (∀ (D : Nat) (v : Fin D → Rat), normSqInt (sgnVec v) = (D : Int)) ∧
    (∀ (D : Nat) (c : Rat) (v : Fin D → Rat), (0 : Rat) < c →
      sgnVec (scaleRat c v) = sgnVec v) ∧
    (∀ (D dM : Nat) (h : dM ≤ D) (x : Fin D → Rat),
      normSqRat x = prefixNormSqRat dM h x + tailNormSqRat dM h x ∧
      (0 : Rat) ≤ tailNormSqRat dM h x ∧
      prefixNormSqRat dM h x ≤ normSqRat x) ∧
    (∀ (D dM : Nat) (h : dM ≤ D) (q xPos xBad : Fin D → Rat) (c : Rat),
      (0 : Rat) < prefixDotRat dM h q xBad →
      (0 : Rat) < c →
      prefixDotRat dM h q xPos / prefixDotRat dM h q xBad < c →
      prefixDotRat dM h q xPos < prefixDotRat dM h q (scaleRat c xBad) ∧
      dotInt (sgnVec q) (sgnVec (scaleRat c xBad)) = dotInt (sgnVec q) (sgnVec xBad)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D v; exact normSqInt_sgnVec v
  · intro D c v hc; exact sgnVec_scale_pos hc v
  · intro D dM h x
    have hsplit := normSqRat_eq_prefix_add_tail h x
    have hnn := tailNormSqRat_nonneg h x
    refine ⟨hsplit, hnn, ?_⟩
    rw [hsplit]
    have h1 := rat_add_le_add (Rat.le_refl (a := prefixNormSqRat dM h x)) hnn
    have h0 : prefixNormSqRat dM h x + 0 = prefixNormSqRat dM h x := by grind
    rw [h0] at h1
    exact h1
  · intro D dM h q xPos xBad c hbadPos hcPos hcHijack
    exact norm_ratio_hijack_vs_hypercube_immunity h q xPos xBad c hbadPos hcPos hcHijack

end RagPopcntMatryoshka
