/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MlaKantorovichRope.KantorovichGL

/-!
# Theorem 5: Exact Pythagorean `R = 1105` Multi-Angle RoPE Rotations

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
- Exact factorization `1105 = 5 * 13 * 17` and `1105^2 = 1,221,025`.
- All 4 primitive Brahmagupta-Fibonacci Pythagorean pairs `(1104, 47)`, `(1073, 264)`,
  `(943, 576)`, `(817, 744)` sharing exact denominator `1105^2` with `Nat.gcd c s = 1`
  and strict ordering `1104 > 1073 > 943 > 817 > 744 > 576 > 264 > 47 > 0`.
- All 10 Wave 7C campaign Pythagorean RoPE pairs sharing denominator `1105^2`.
- Universal exact algebraic RoPE rotation laws for any `(c, s, R)` with `R ≠ 0` and `c^2 + s^2 = R^2`:
  exact orthogonality `R^T R = I_2` and `R R^T = I_2`, exact Euclidean norm conservation
  `‖R v‖_2^2 = ‖v‖_2^2`, exact inner-product invariance `⟨R q, R k⟩ = ⟨q, k⟩`,
  Brahmagupta-Fibonacci composition identity, and exact relative-position RoPE law.
-/

namespace MlaKantorovichRope

theorem ropeRotMat_orthogonal {c s R : Rat} (hR : R ≠ 0) (hpyth : c * c + s * s = R * R) :
    isOrthogonal (ropeRotMat c s R) ∧
    matMul (ropeRotMat c s R) (matTranspose (ropeRotMat c s R)) = matId 2 := by
  have hunit : (c / R) * (c / R) + (s / R) * (s / R) = 1 := by
    have hmul : ((c / R) * (c / R) + (s / R) * (s / R)) * (R * R) = R * R := by
      have h1 : (c / R) * (c / R) * (R * R) = c * c := by
        have hre : (c / R) * (c / R) * (R * R) = ((c / R) * R) * ((c / R) * R) := by grind
        rw [hre, rat_div_mul_cancel hR]
      have h2 : (s / R) * (s / R) * (R * R) = s * s := by
        have hre : (s / R) * (s / R) * (R * R) = ((s / R) * R) * ((s / R) * R) := by grind
        rw [hre, rat_div_mul_cancel hR]
      have hd : ((c / R) * (c / R) + (s / R) * (s / R)) * (R * R) =
          (c / R) * (c / R) * (R * R) + (s / R) * (s / R) * (R * R) := by grind
      rw [hd, h1, h2, hpyth]
    have hRR : R * R ≠ 0 := by
      intro h0
      cases Rat.mul_eq_zero.mp h0 with
      | inl h => exact hR h
      | inr h => exact hR h
    have hdiv := congrArg (fun x => x / (R * R)) hmul
    rw [rat_mul_div_cancel hRR, Rat.div_def (R * R), Rat.mul_inv_cancel (R * R) hRR] at hdiv
    exact hdiv
  constructor
  · unfold isOrthogonal
    funext i j
    unfold matMul matTranspose ropeRotMat matId
    rcases i with ⟨iv, hi⟩
    rcases j with ⟨jv, hj⟩
    have hiv : iv = 0 ∨ iv = 1 := by omega
    have hjv : jv = 0 ∨ jv = 1 := by omega
    rcases hiv with rfl | rfl <;> rcases hjv with rfl | rfl <;>
      simp only [finSum, Fin.mk.injEq, ↓reduceIte, Nat.one_ne_zero, Nat.zero_ne_one] <;> grind
  · funext i j
    unfold matMul matTranspose ropeRotMat matId
    rcases i with ⟨iv, hi⟩
    rcases j with ⟨jv, hj⟩
    have hiv : iv = 0 ∨ iv = 1 := by omega
    have hjv : jv = 0 ∨ jv = 1 := by omega
    rcases hiv with rfl | rfl <;> rcases hjv with rfl | rfl <;>
      simp only [finSum, Fin.mk.injEq, ↓reduceIte, Nat.one_ne_zero, Nat.zero_ne_one] <;> grind

theorem ropeApply_norm_and_dot_invariant {c s R : Rat} (hR : R ≠ 0)
    (hpyth : c * c + s * s = R * R) (q k : Fin 2 → Rat) :
    normSq (ropeApply c s R q) = normSq q ∧
    dot (ropeApply c s R q) (ropeApply c s R k) = dot q k := by
  have horth := (ropeRotMat_orthogonal hR hpyth).1
  have hdot : ∀ u v : Fin 2 → Rat, dot (ropeApply c s R u) (ropeApply c s R v) = dot u v := by
    intro u v
    unfold ropeApply
    rw [← dot_matVec_transpose (ropeRotMat c s R) (matVec (ropeRotMat c s R) u) v]
    rw [← matVec_matMul]
    unfold isOrthogonal at horth
    rw [horth, matVec_matId]
  exact ⟨hdot q q, hdot q k⟩

theorem brahmagupta_fibonacci_rope_composition {c1 s1 R1 c2 s2 R2 : Rat}
    (hR1 : R1 ≠ 0) (hR2 : R2 ≠ 0) (q k : Fin 2 → Rat) :
    (c1 * c2 - s1 * s2) * (c1 * c2 - s1 * s2) + (s1 * c2 + c1 * s2) * (s1 * c2 + c1 * s2) =
      (c1 * c1 + s1 * s1) * (c2 * c2 + s2 * s2) ∧
    ropeApply c1 s1 R1 (ropeApply c2 s2 R2 q) =
      ropeApply (c1 * c2 - s1 * s2) (s1 * c2 + c1 * s2) (R1 * R2) q ∧
    dot (ropeApply c1 s1 R1 q) (ropeApply c2 s2 R2 k) =
      dot (ropeApply (c1 * c2 + s1 * s2) (s1 * c2 - c1 * s2) (R1 * R2) q) k := by
  have hR12 : R1 * R2 ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hR1 h
    | inr h => exact hR2 h
  have hinv12 : (R1 * R2)⁻¹ = R1⁻¹ * R2⁻¹ := rat_mul_inv hR1 hR2
  refine ⟨by grind, ?_, ?_⟩
  · funext i
    unfold ropeApply matVec ropeRotMat
    rcases i with ⟨iv, hi⟩
    have hiv : iv = 0 ∨ iv = 1 := by omega
    rcases hiv with rfl | rfl <;>
      simp only [finSum, ↓reduceIte, Nat.one_ne_zero, Rat.div_def, hinv12] <;>
      grind
  · unfold dot ropeApply matVec ropeRotMat
    simp only [finSum, ↓reduceIte, Nat.one_ne_zero, Rat.div_def, hinv12]
    grind

/-- Theorem 5 (Exact Pythagorean `R = 1105` Multi-Angle RoPE Rotations):
    Verifies `1105 = 5 * 13 * 17` and `1105^2 = 1,221,025`, all 4 primitive Brahmagupta-Fibonacci
    Pythagorean RoPE pairs `(1104, 47)`, `(1073, 264)`, `(943, 576)`, `(817, 744)` with
    `Nat.gcd c s = 1` and strict angle ordering, all 10 Wave 7C campaign RoPE pairs, and the
    universal exact orthogonality, norm conservation, inner-product invariance, and
    Brahmagupta-Fibonacci relative-position composition laws. -/
theorem pythagorean_1105_multi_angle_rope_exact :
    (1105 = 5 * 13 * 17 ∧ 1105 * 1105 = 1221025) ∧
    (pythPrimitive1105.length = 4 ∧
     (∀ p ∈ pythPrimitive1105, p.1 * p.1 + p.2 * p.2 = 1105 * 1105 ∧ Nat.gcd p.1 p.2 = 1) ∧
     (1104 > 1073 ∧ 1073 > 943 ∧ 943 > 817 ∧ 817 > 744 ∧ 744 > 576 ∧ 576 > 264 ∧ 264 > 47 ∧ 47 > 0)) ∧
    (pythCampaign1105.length = 10 ∧
     (∀ p ∈ pythCampaign1105, p.1 * p.1 + p.2 * p.2 = 1105 * 1105)) ∧
    (∀ (c s R : Rat) (q k : Fin 2 → Rat), R ≠ 0 → c * c + s * s = R * R →
      isOrthogonal (ropeRotMat c s R) ∧
      matMul (ropeRotMat c s R) (matTranspose (ropeRotMat c s R)) = matId 2 ∧
      normSq (ropeApply c s R q) = normSq q ∧
      dot (ropeApply c s R q) (ropeApply c s R k) = dot q k) ∧
    (∀ (c1 s1 R1 c2 s2 R2 : Rat) (q k : Fin 2 → Rat), R1 ≠ 0 → R2 ≠ 0 →
      (c1 * c2 - s1 * s2) * (c1 * c2 - s1 * s2) + (s1 * c2 + c1 * s2) * (s1 * c2 + c1 * s2) =
        (c1 * c1 + s1 * s1) * (c2 * c2 + s2 * s2) ∧
      ropeApply c1 s1 R1 (ropeApply c2 s2 R2 q) =
        ropeApply (c1 * c2 - s1 * s2) (s1 * c2 + c1 * s2) (R1 * R2) q ∧
      dot (ropeApply c1 s1 R1 q) (ropeApply c2 s2 R2 k) =
        dot (ropeApply (c1 * c2 + s1 * s2) (s1 * c2 - c1 * s2) (R1 * R2) q) k) := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, ?_, by decide⟩
    intro p hp
    simp only [pythPrimitive1105, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  · refine ⟨by decide, ?_⟩
    intro p hp
    simp only [pythCampaign1105, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro c s R q k hR hpyth
    have ho := ropeRotMat_orthogonal hR hpyth
    have hi := ropeApply_norm_and_dot_invariant hR hpyth q k
    exact ⟨ho.1, ho.2, hi.1, hi.2⟩
  · intro c1 s1 R1 c2 s2 R2 q k hR1 hR2
    exact brahmagupta_fibonacci_rope_composition hR1 hR2 q k

end MlaKantorovichRope
