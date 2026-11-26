/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NsaBallBoundMoba.RatOrder

/-!
# Theorems 2 & 4: Zero-Sqrt Exact Ball-Bound & Quantization-Absorbing Ball-Bound

Proves:
- **Theorem 2 (`zero_sqrt_ball_bound_exact_soundness_zero_fn`):** Exact Cauchy–Schwarz
  pure-integer soundness for Zero-Sqrt Ball-Bound (`d + 1` scalars per block, zero
  square roots), certifying **exact `0` false negatives** for any block size `B ≥ 1`,
  any dimension `d`, any query `q`, and any threshold `T`.
- **Theorem 4 (`quantization_absorbing_ball_bound_zero_fn_all_precisions`):** Exact
  triangle-inequality / Cauchy–Schwarz soundness when the block summary `S_b` is
  quantized to ANY `S_hat` (covering `1-bit`, `INT2`, `MXFP4`, `INT4`, `FP8`, or any
  arbitrary integer summary) with squared error `ε_b^2 = ‖S_b - S_hat‖_2^2`: proves
  all three exact zero-FN forms (enlarged radius `(R + ε)^2`, zero-sqrt `2(R^2 + ε^2)`,
  and additive ceiling-sqrt `q^T S_hat + e_q + r_q`).
-/

namespace NsaBallBoundMoba

theorem blockSqRadius_ge_pointwise {d B : Nat} (ks : Fin B → Fin d → Int) (j : Fin B) :
    normSqInt (fun c => (B : Int) * ks j c - blockSum ks c) ≤ blockSqRadius ks := by
  unfold blockSqRadius
  exact le_intFinMaxNonneg (fun i => normSqInt (fun c => (B : Int) * ks i c - blockSum ks c)) j

theorem pointwise_ball_bound_sq {d B : Nat} (q : Fin d → Int) (ks : Fin B → Fin d → Int)
    (j : Fin B) :
    ((B : Int) * dotInt q (ks j) - dotInt q (blockSum ks)) *
    ((B : Int) * dotInt q (ks j) - dotInt q (blockSum ks)) ≤
      normSqInt q * blockSqRadius ks := by
  have hlin : (B : Int) * dotInt q (ks j) - dotInt q (blockSum ks) =
      dotInt q (fun c => (B : Int) * ks j c - blockSum ks c) := by
    rw [dotInt_sub_right, dotInt_smul_right]
  rw [hlin]
  have hcs := cauchy_schwarz_int q (fun c => (B : Int) * ks j c - blockSum ks c)
  have hr := blockSqRadius_ge_pointwise ks j
  have hmul : normSqInt q * normSqInt (fun c => (B : Int) * ks j c - blockSum ks c) ≤
      normSqInt q * blockSqRadius ks := by
    have hnn := normSqInt_nonneg q
    have hdiff : 0 ≤ normSqInt q * (blockSqRadius ks -
        normSqInt (fun c => (B : Int) * ks j c - blockSum ks c)) :=
      Int.mul_nonneg hnn (by omega)
    grind
  exact Int.le_trans hcs hmul

/-- Headline Theorem 2 (`zero_sqrt_ball_bound_exact_soundness_zero_fn`):
    Universal pure-integer Cauchy–Schwarz soundness of Zero-Sqrt Ball-Bound:
    1. Universal Cauchy–Schwarz over `ℤ^d` for all `d`.
    2. Pointwise squared deviation bound `(B (q^T k_j) - q^T S_b)^2 ≤ ‖q‖_2^2 R_b^2`.
    3. Zero-sqrt candidate soundness: if ANY key `k_j` satisfies `q^T k_j ≥ T`, then
       `q^T S_b ≥ B T ∨ (B T - q^T S_b)^2 ≤ ‖q‖_2^2 R_b^2` (exact `0` false negatives).
    4. Contrapositive pruning soundness: if `q^T S_b < B T` and
       `(B T - q^T S_b)^2 > ‖q‖_2^2 R_b^2`, then EVERY key in the block has `q^T k_j < T`.
    5. Exact `+1` scalar metadata overhead (`(d + 1) - d = 1`). -/
theorem zero_sqrt_ball_bound_exact_soundness_zero_fn :
    (∀ (d : Nat) (u v : Fin d → Int),
      dotInt u v * dotInt u v ≤ normSqInt u * normSqInt v) ∧
    (∀ (d B : Nat) (q : Fin d → Int) (ks : Fin B → Fin d → Int) (j : Fin B),
      ((B : Int) * dotInt q (ks j) - dotInt q (blockSum ks)) *
      ((B : Int) * dotInt q (ks j) - dotInt q (blockSum ks)) ≤
        normSqInt q * blockSqRadius ks) ∧
    (∀ (d B : Nat) (q : Fin d → Int) (ks : Fin B → Fin d → Int) (T : Int),
      1 ≤ B →
      (∃ j : Fin B, T ≤ dotInt q (ks j)) →
      ballBoundPass B q (blockSum ks) (blockSqRadius ks) T) ∧
    (∀ (d B : Nat) (q : Fin d → Int) (ks : Fin B → Fin d → Int) (T : Int),
      1 ≤ B →
      dotInt q (blockSum ks) < (B : Int) * T →
      normSqInt q * blockSqRadius ks <
        ((B : Int) * T - dotInt q (blockSum ks)) * ((B : Int) * T - dotInt q (blockSum ks)) →
      ∀ j : Fin B, dotInt q (ks j) < T) ∧
    (∀ d : Nat, (d + 1) - d = 1) := by
  refine ⟨fun _ u v => cauchy_schwarz_int u v,
          fun _ _ q ks j => pointwise_ball_bound_sq q ks j, ?_, ?_, fun _ => by omega⟩
  · intro d B q ks T hB ⟨j, hj⟩
    unfold ballBoundPass
    by_cases hmean : (B : Int) * T ≤ dotInt q (blockSum ks)
    · exact Or.inl hmean
    · right
      have hBT : (B : Int) * T ≤ (B : Int) * dotInt q (ks j) := by
        have h1 : 0 ≤ (B : Int) * (dotInt q (ks j) - T) := Int.mul_nonneg (by omega) (by omega)
        grind
      have hgap1 : 0 ≤ (B : Int) * T - dotInt q (blockSum ks) := by omega
      have hgap2 : (B : Int) * T - dotInt q (blockSum ks) ≤
          (B : Int) * dotInt q (ks j) - dotInt q (blockSum ks) := by omega
      have hsq_mono :
          ((B : Int) * T - dotInt q (blockSum ks)) * ((B : Int) * T - dotInt q (blockSum ks)) ≤
          ((B : Int) * dotInt q (ks j) - dotInt q (blockSum ks)) *
          ((B : Int) * dotInt q (ks j) - dotInt q (blockSum ks)) := by
        have hdiff : 0 ≤ ((B : Int) * dotInt q (ks j) - (B : Int) * T) *
            (((B : Int) * dotInt q (ks j) - dotInt q (blockSum ks)) +
             ((B : Int) * T - dotInt q (blockSum ks))) :=
          Int.mul_nonneg (by omega) (by omega)
        grind
      exact Int.le_trans hsq_mono (pointwise_ball_bound_sq q ks j)
  · intro d B q ks T hB hlt hprune j
    by_cases hge : T ≤ dotInt q (ks j)
    · have hBT : (B : Int) * T ≤ (B : Int) * dotInt q (ks j) := by
        have h1 : 0 ≤ (B : Int) * (dotInt q (ks j) - T) := Int.mul_nonneg (by omega) (by omega)
        grind
      have hsq_mono :
          ((B : Int) * T - dotInt q (blockSum ks)) * ((B : Int) * T - dotInt q (blockSum ks)) ≤
          ((B : Int) * dotInt q (ks j) - dotInt q (blockSum ks)) *
          ((B : Int) * dotInt q (ks j) - dotInt q (blockSum ks)) := by
        have hdiff : 0 ≤ ((B : Int) * dotInt q (ks j) - (B : Int) * T) *
            (((B : Int) * dotInt q (ks j) - dotInt q (blockSum ks)) +
             ((B : Int) * T - dotInt q (blockSum ks))) :=
          Int.mul_nonneg (by omega) (by omega)
        grind
      have hpt := pointwise_ball_bound_sq q ks j
      omega
    · omega

/-- Headline Theorem 4 (`quantization_absorbing_ball_bound_zero_fn_all_precisions`):
    Exact quantization-absorbing Ball-Bound soundness across ALL summary precisions
    (`1-bit`, `INT2`, `MXFP4`, `INT4`, `FP8`, or any arbitrary quantized summary `S_hat`):
    Let `eps2 = ‖S_b - S_hat‖_2^2` and `R2 = blockSqRadius ks`. Then:
    1. **Enlarged-Radius Form (`(R + ε)^2`):** For any `R, ε ≥ 0` with `R2 ≤ R^2` and
       `eps2 ≤ ε^2`, every key satisfies `‖B k_j - S_hat‖_2^2 ≤ (R + ε)^2`, and if ANY key
       satisfies `q^T k_j ≥ T`, then `ballBoundPass B q S_hat ((R + ε)^2) T` holds (`0` FN).
    2. **Zero-Sqrt Parallelogram Form (`2(R^2 + ε^2)`):** With ZERO square roots even for
       combining radii, if ANY key satisfies `q^T k_j ≥ T`, then
       `ballBoundPass B q S_hat (2 * (R2 + eps2)) T` holds (`0` FN).
    3. **Additive Ceiling-Sqrt Form (Pillar 2 kernel formula):** For any `r_q, e_q ≥ 0`
       with `‖q‖_2^2 R2 ≤ r_q^2` and `‖q‖_2^2 eps2 ≤ e_q^2`, every key satisfies
       `B (q^T k_j) ≤ q^T S_hat + e_q + r_q`, guaranteeing `0` FN for any threshold `T`. -/
theorem quantization_absorbing_ball_bound_zero_fn_all_precisions :
    (∀ (d B : Nat) (q : Fin d → Int) (ks : Fin B → Fin d → Int) (S_hat : Fin d → Int)
       (R eps T : Int),
      1 ≤ B → 0 ≤ R → 0 ≤ eps →
      blockSqRadius ks ≤ R * R →
      normSqInt (fun c => blockSum ks c - S_hat c) ≤ eps * eps →
      (∀ j : Fin B,
        normSqInt (fun c => (B : Int) * ks j c - S_hat c) ≤ (R + eps) * (R + eps)) ∧
      ((∃ j : Fin B, T ≤ dotInt q (ks j)) →
        ballBoundPass B q S_hat ((R + eps) * (R + eps)) T)) ∧
    (∀ (d B : Nat) (q : Fin d → Int) (ks : Fin B → Fin d → Int) (S_hat : Fin d → Int) (T : Int),
      1 ≤ B →
      (∃ j : Fin B, T ≤ dotInt q (ks j)) →
      ballBoundPass B q S_hat
        (2 * (blockSqRadius ks + normSqInt (fun c => blockSum ks c - S_hat c))) T) ∧
    (∀ (d B : Nat) (q : Fin d → Int) (ks : Fin B → Fin d → Int) (S_hat : Fin d → Int)
       (r_q e_q T : Int),
      1 ≤ B → 0 ≤ r_q → 0 ≤ e_q →
      normSqInt q * blockSqRadius ks ≤ r_q * r_q →
      normSqInt q * normSqInt (fun c => blockSum ks c - S_hat c) ≤ e_q * e_q →
      (∀ j : Fin B, (B : Int) * dotInt q (ks j) ≤ dotInt q S_hat + e_q + r_q) ∧
      ((∃ j : Fin B, T ≤ dotInt q (ks j)) → (B : Int) * T ≤ dotInt q S_hat + e_q + r_q)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d B q ks S_hat R eps T hB hR heps hR2 heps2
    have hrad : ∀ j : Fin B,
        normSqInt (fun c => (B : Int) * ks j c - S_hat c) ≤ (R + eps) * (R + eps) := by
      intro j
      let u : Fin d → Int := fun c => (B : Int) * ks j c - blockSum ks c
      let v : Fin d → Int := fun c => blockSum ks c - S_hat c
      have hsplit : (fun c => (B : Int) * ks j c - S_hat c) = (fun c => u c + v c) := by
        funext c; dsimp [u, v]; omega
      rw [hsplit, normSqInt_add_eq]
      have hu : normSqInt u ≤ R * R := Int.le_trans (blockSqRadius_ge_pointwise ks j) hR2
      have hv : normSqInt v ≤ eps * eps := heps2
      have hcs := cauchy_schwarz_int u v
      have hprod : normSqInt u * normSqInt v ≤ (R * eps) * (R * eps) := by
        have h1 : normSqInt u * normSqInt v ≤ (R * R) * normSqInt v := by
          have hnn := normSqInt_nonneg v
          have h := Int.mul_nonneg (by omega : 0 ≤ R * R - normSqInt u) hnn
          grind
        have h2 : (R * R) * normSqInt v ≤ (R * R) * (eps * eps) := by
          have h := Int.mul_nonneg (int_sq_nonneg R) (by omega : 0 ≤ eps * eps - normSqInt v)
          grind
        have h3 : (R * R) * (eps * eps) = (R * eps) * (R * eps) := by grind
        omega
      have hdot : dotInt u v ≤ R * eps :=
        int_le_of_sq_le_sq (Int.mul_nonneg hR heps) (Int.le_trans hcs hprod)
      grind
    refine ⟨hrad, ?_⟩
    intro ⟨j, hj⟩
    unfold ballBoundPass
    by_cases hmean : (B : Int) * T ≤ dotInt q S_hat
    · exact Or.inl hmean
    · right
      have hBT : (B : Int) * T ≤ (B : Int) * dotInt q (ks j) := by
        have h1 : 0 ≤ (B : Int) * (dotInt q (ks j) - T) := Int.mul_nonneg (by omega) (by omega)
        grind
      have hsq_mono :
          ((B : Int) * T - dotInt q S_hat) * ((B : Int) * T - dotInt q S_hat) ≤
          ((B : Int) * dotInt q (ks j) - dotInt q S_hat) *
          ((B : Int) * dotInt q (ks j) - dotInt q S_hat) := by
        have hdiff : 0 ≤ ((B : Int) * dotInt q (ks j) - (B : Int) * T) *
            (((B : Int) * dotInt q (ks j) - dotInt q S_hat) +
             ((B : Int) * T - dotInt q S_hat)) :=
          Int.mul_nonneg (by omega) (by omega)
        grind
      have hlin : (B : Int) * dotInt q (ks j) - dotInt q S_hat =
          dotInt q (fun c => (B : Int) * ks j c - S_hat c) := by
        rw [dotInt_sub_right, dotInt_smul_right]
      have hcs := cauchy_schwarz_int q (fun c => (B : Int) * ks j c - S_hat c)
      have hmul : normSqInt q * normSqInt (fun c => (B : Int) * ks j c - S_hat c) ≤
          normSqInt q * ((R + eps) * (R + eps)) := by
        have hradj := hrad j
        have h := Int.mul_nonneg (normSqInt_nonneg q)
          (by omega : 0 ≤ (R + eps) * (R + eps) - normSqInt (fun c => (B : Int) * ks j c - S_hat c))
        have hid : normSqInt q * ((R + eps) * (R + eps)) -
            normSqInt q * normSqInt (fun c => (B : Int) * ks j c - S_hat c) =
            normSqInt q * ((R + eps) * (R + eps) - normSqInt (fun c => (B : Int) * ks j c - S_hat c)) := by
          grind
        omega
      rw [← hlin] at hcs
      exact Int.le_trans hsq_mono (Int.le_trans hcs hmul)
  · intro d B q ks S_hat T hB ⟨j, hj⟩
    unfold ballBoundPass
    by_cases hmean : (B : Int) * T ≤ dotInt q S_hat
    · exact Or.inl hmean
    · right
      have hBT : (B : Int) * T ≤ (B : Int) * dotInt q (ks j) := by
        have h1 : 0 ≤ (B : Int) * (dotInt q (ks j) - T) := Int.mul_nonneg (by omega) (by omega)
        grind
      have hsq_mono :
          ((B : Int) * T - dotInt q S_hat) * ((B : Int) * T - dotInt q S_hat) ≤
          ((B : Int) * dotInt q (ks j) - dotInt q S_hat) *
          ((B : Int) * dotInt q (ks j) - dotInt q S_hat) := by
        have hdiff : 0 ≤ ((B : Int) * dotInt q (ks j) - (B : Int) * T) *
            (((B : Int) * dotInt q (ks j) - dotInt q S_hat) +
             ((B : Int) * T - dotInt q S_hat)) :=
          Int.mul_nonneg (by omega) (by omega)
        grind
      let u : Fin d → Int := fun c => (B : Int) * ks j c - blockSum ks c
      let v : Fin d → Int := fun c => blockSum ks c - S_hat c
      have hsplit : (fun c => (B : Int) * ks j c - S_hat c) = (fun c => u c + v c) := by
        funext c; dsimp [u, v]; omega
      have hpar : normSqInt (fun c => (B : Int) * ks j c - S_hat c) ≤
          2 * (blockSqRadius ks + normSqInt v) := by
        rw [hsplit]
        have h1 := normSqInt_add_le_two_mul u v
        have h2 : normSqInt u ≤ blockSqRadius ks := blockSqRadius_ge_pointwise ks j
        omega
      have hlin : (B : Int) * dotInt q (ks j) - dotInt q S_hat =
          dotInt q (fun c => (B : Int) * ks j c - S_hat c) := by
        rw [dotInt_sub_right, dotInt_smul_right]
      have hcs := cauchy_schwarz_int q (fun c => (B : Int) * ks j c - S_hat c)
      have hmul : normSqInt q * normSqInt (fun c => (B : Int) * ks j c - S_hat c) ≤
          normSqInt q * (2 * (blockSqRadius ks + normSqInt v)) := by
        have h := Int.mul_nonneg (normSqInt_nonneg q) (by omega : 0 ≤
          2 * (blockSqRadius ks + normSqInt v) - normSqInt (fun c => (B : Int) * ks j c - S_hat c))
        grind
      rw [← hlin] at hcs
      exact Int.le_trans hsq_mono (Int.le_trans hcs hmul)
  · intro d B q ks S_hat r_q e_q T hB hrq heq hR2 heps2
    have hpt : ∀ j : Fin B, (B : Int) * dotInt q (ks j) ≤ dotInt q S_hat + e_q + r_q := by
      intro j
      have hcs1 := pointwise_ball_bound_sq q ks j
      have hd1 : (B : Int) * dotInt q (ks j) - dotInt q (blockSum ks) ≤ r_q :=
        int_le_of_sq_le_sq hrq (Int.le_trans hcs1 hR2)
      have hlin2 : dotInt q (blockSum ks) - dotInt q S_hat =
          dotInt q (fun c => blockSum ks c - S_hat c) := (dotInt_sub_right q (blockSum ks) S_hat).symm
      have hcs2 := cauchy_schwarz_int q (fun c => blockSum ks c - S_hat c)
      rw [← hlin2] at hcs2
      have hd2 : dotInt q (blockSum ks) - dotInt q S_hat ≤ e_q :=
        int_le_of_sq_le_sq heq (Int.le_trans hcs2 heps2)
      omega
    refine ⟨hpt, ?_⟩
    intro ⟨j, hj⟩
    have hBT : (B : Int) * T ≤ (B : Int) * dotInt q (ks j) := by
      have h1 : 0 ≤ (B : Int) * (dotInt q (ks j) - T) := Int.mul_nonneg (by omega) (by omega)
      grind
    exact Int.le_trans hBT (hpt j)

end NsaBallBoundMoba
