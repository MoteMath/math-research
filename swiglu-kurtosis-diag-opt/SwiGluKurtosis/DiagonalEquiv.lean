/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SwiGluKurtosis.RatOrder

/-!
# Theorems 3 & 4: Zero-FLOP SwiGLU Diagonal Equivalence & AM-GM Optimal Scale Law

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
3. `swiglu_zero_flop_diagonal_equivalence_identity`
4. `swiglu_optimal_diagonal_scale_amgm_law`
-/

namespace SwiGluKurtosis

/-! ### Theorem 3: Exact Zero-FLOP SwiGLU Diagonal Equivalence -/

theorem gatedFFN_diag_equiv {d_out m : Nat} (φ : Rat → Rat)
    (W_down : Fin d_out → Fin m → Rat) (g u s : Fin m → Rat)
    (hs : ∀ j : Fin m, s j ≠ 0) :
    gatedFFN φ (invScaleCols s W_down) g (fun j => s j * u j) =
      gatedFFN φ W_down g u := by
  funext i
  unfold gatedFFN matVec hadamard invScaleCols
  apply finSum_congr
  intro j
  have hre : (W_down i j / s j) * (φ (g j) * (s j * u j)) =
      ((W_down i j / s j) * s j) * (φ (g j) * u j) := by grind
  rw [hre, rat_div_mul_cancel (hs j)]

theorem matVec_scaleRows {m d_in : Nat} (s : Fin m → Rat)
    (W_up : Fin m → Fin d_in → Rat) (x : Fin d_in → Rat) :
    matVec (scaleRows s W_up) x = fun j => s j * matVec W_up x j := by
  funext j
  unfold matVec scaleRows
  have h : ∀ k : Fin d_in, s j * W_up j k * x k = s j * (W_up j k * x k) := by
    intro k; grind
  rw [finSum_congr h, finSum_mul_left]

/-- Headline Theorem 3 (`swiglu_zero_flop_diagonal_equivalence_identity`). -/
theorem swiglu_zero_flop_diagonal_equivalence_identity :
    (∀ (d_out m : Nat) (φ : Rat → Rat) (W_down : Fin d_out → Fin m → Rat)
       (g u s : Fin m → Rat),
      (∀ j : Fin m, s j ≠ 0) →
      gatedFFN φ (invScaleCols s W_down) g (fun j => s j * u j) =
        gatedFFN φ W_down g u) ∧
    (∀ (d_out m d_in : Nat) (φ : Rat → Rat)
       (W_down : Fin d_out → Fin m → Rat)
       (W_gate W_up : Fin m → Fin d_in → Rat)
       (x : Fin d_in → Rat) (s : Fin m → Rat),
      (∀ j : Fin m, s j ≠ 0) →
      gatedFFN φ (invScaleCols s W_down) (matVec W_gate x) (matVec (scaleRows s W_up) x) =
        gatedFFN φ W_down (matVec W_gate x) (matVec W_up x)) ∧
    (∀ (φ : Rat → Rat) (w g u lam : Rat),
      lam ≠ 0 → (w * lam) * (φ g * (u / lam)) = w * (φ g * u)) := by
  refine ⟨fun _ _ φ W_down g u s hs => gatedFFN_diag_equiv φ W_down g u s hs, ?_, ?_⟩
  · intro d_out m d_in φ W_down W_gate W_up x s hs
    rw [matVec_scaleRows s W_up x]
    exact gatedFFN_diag_equiv φ W_down (matVec W_gate x) (matVec W_up x) s hs
  · intro φ w g u lam hlam
    have hre : (w * lam) * (φ g * (u / lam)) = w * (φ g * ((u / lam) * lam)) := by grind
    rw [hre, rat_div_mul_cancel hlam]

/-! ### Theorem 4: Exact AM-GM / SOS Optimal Diagonal Scale Law -/

theorem diagQuantMSE_amgm_sq (εa εw K lam : Rat) (hlam : lam ≠ 0) :
    sq (diagQuantMSE εa εw K lam) - 4 * sq K * εa * εw =
      sq (εa * sq (K / lam) - εw * sq lam) ∧
    4 * sq K * εa * εw ≤ sq (diagQuantMSE εa εw K lam) := by
  have h1 : sq (diagQuantMSE εa εw K lam) - 4 * sq K * εa * εw =
      sq (εa * sq (K / lam) - εw * sq lam) := by
    unfold diagQuantMSE sq
    have hcancel : (K / lam) * lam = K := rat_div_mul_cancel hlam
    have hprod : (K / lam) * (K / lam) * (lam * lam) = K * K := by
      have : (K / lam) * (K / lam) * (lam * lam) = ((K / lam) * lam) * ((K / lam) * lam) := by grind
      rw [this, hcancel]
    grind
  refine ⟨h1, ?_⟩
  apply rat_le_of_sub_nonneg
  rw [h1]
  exact rat_sq_nonneg _

theorem diagQuantMSE_sos_exact (εa εw K r lam : Rat)
    (hεw : (0 : Rat) < εw) (hlam : lam ≠ 0) (hr : εa = εw * sq r) :
    diagQuantMSE εa εw K lam - 2 * K * εw * r =
      εw * sq (sq lam - K * r) / sq lam ∧
    2 * K * εw * r ≤ diagQuantMSE εa εw K lam ∧
    (diagQuantMSE εa εw K lam = 2 * K * εw * r ↔ sq lam = K * r) := by
  have hlam2_pos : (0 : Rat) < sq lam := rat_sq_pos_of_ne_zero hlam
  have hlam2_ne : sq lam ≠ 0 := Rat.ne_of_gt hlam2_pos
  have hsos : diagQuantMSE εa εw K lam - 2 * K * εw * r =
      εw * sq (sq lam - K * r) / sq lam := by
    apply Eq.symm
    apply (rat_div_eq_iff hlam2_ne).mpr
    unfold diagQuantMSE sq at *
    rw [hr]
    have hcancel : (K / lam) * (K / lam) * (lam * lam) = K * K := by
      have : (K / lam) * (K / lam) * (lam * lam) = ((K / lam) * lam) * ((K / lam) * lam) := by grind
      rw [this, rat_div_mul_cancel hlam]
    grind
  have hle : 2 * K * εw * r ≤ diagQuantMSE εa εw K lam := by
    apply rat_le_of_sub_nonneg
    rw [hsos]
    exact rat_div_nonneg (Rat.mul_nonneg (Rat.le_of_lt hεw) (rat_sq_nonneg _)) hlam2_pos
  refine ⟨hsos, hle, ?_⟩
  constructor
  · intro heq
    have hsub0 : diagQuantMSE εa εw K lam - 2 * K * εw * r = 0 := by rw [heq]; grind
    rw [hsos] at hsub0
    have hnum0 : εw * sq (sq lam - K * r) = 0 := by
      have := (rat_div_eq_iff hlam2_ne).mp hsub0
      grind
    cases Rat.mul_eq_zero.mp hnum0 with
    | inl h0 => exact False.elim (Rat.ne_of_gt hεw h0)
    | inr hsq0 =>
      unfold sq at hsq0 ⊢
      cases Rat.mul_eq_zero.mp hsq0 with
      | inl hd => grind
      | inr hd => grind
  · intro hsq
    have hsub0 : diagQuantMSE εa εw K lam - 2 * K * εw * r = 0 := by
      rw [hsos, hsq]
      unfold sq; grind
    grind

theorem diagQuantMSE_beats_unscaled (εa εw K r lamStar : Rat)
    (hεw : (0 : Rat) < εw) (hlamStar : lamStar ≠ 0)
    (hr : εa = εw * sq r) (hopt : sq lamStar = K * r) (hne : K * r ≠ 1) :
    diagQuantMSE εa εw K 1 - diagQuantMSE εa εw K lamStar = εw * sq (K * r - 1) ∧
    diagQuantMSE εa εw K lamStar < diagQuantMSE εa εw K 1 := by
  have hopt_val : diagQuantMSE εa εw K lamStar = 2 * K * εw * r :=
    (diagQuantMSE_sos_exact εa εw K r lamStar hεw hlamStar hr).2.2.mpr hopt
  have h1_sos := (diagQuantMSE_sos_exact εa εw K r 1 hεw (by decide) hr).1
  have hdiff : diagQuantMSE εa εw K 1 - diagQuantMSE εa εw K lamStar = εw * sq (K * r - 1) := by
    rw [hopt_val, h1_sos]
    unfold sq; grind
  refine ⟨hdiff, ?_⟩
  apply rat_lt_of_sub_pos
  rw [hdiff]
  have hne0 : K * r - 1 ≠ 0 := by
    intro h0; exact hne (by grind)
  exact rat_mul_pos hεw (rat_sq_pos_of_ne_zero hne0)

theorem diagQuantMSE_clamped_at_K (εa εw K lam : Rat)
    (hεw : (0 : Rat) < εw) (hlam_pos : (0 : Rat) < lam) (hlam_lt : lam < K)
    (hclamp : sq K * εw ≤ εa) :
    diagQuantMSE εa εw K K < diagQuantMSE εa εw K lam := by
  have hK_pos : (0 : Rat) < K := rat_lt_trans hlam_pos hlam_lt
  have hK_ne : K ≠ 0 := Rat.ne_of_gt hK_pos
  have hlam_ne : lam ≠ 0 := Rat.ne_of_gt hlam_pos
  have hlam2_pos : (0 : Rat) < sq lam := rat_sq_pos_of_ne_zero hlam_ne
  apply rat_lt_of_sub_pos
  have hKdivK : K / K = 1 := (rat_div_eq_iff hK_ne).mpr (by grind)
  have hdiff : diagQuantMSE εa εw K lam - diagQuantMSE εa εw K K =
      (sq K - sq lam) * (εa - εw * sq lam) / sq lam := by
    apply Eq.symm
    apply (rat_div_eq_iff (Rat.ne_of_gt hlam2_pos)).mpr
    unfold diagQuantMSE sq
    rw [hKdivK]
    have hcancel : (K / lam) * (K / lam) * (lam * lam) = K * K := by
      have : (K / lam) * (K / lam) * (lam * lam) = ((K / lam) * lam) * ((K / lam) * lam) := by grind
      rw [this, rat_div_mul_cancel hlam_ne]
    grind
  rw [hdiff]
  have h1 : (0 : Rat) < sq K - sq lam := by
    apply rat_sub_pos
    unfold sq
    exact rat_lt_trans (rat_mul_lt_mul_of_pos_left hlam_lt hlam_pos)
      (rat_mul_lt_mul_of_pos_right hlam_lt hK_pos)
  have h2 : (0 : Rat) < εa - εw * sq lam := by
    apply rat_sub_pos
    have hmul : εw * sq lam < εw * sq K := rat_mul_lt_mul_of_pos_left (rat_lt_of_sub_pos h1) hεw
    have hcomm : εw * sq K = sq K * εw := by grind
    rw [hcomm] at hmul
    exact rat_lt_of_lt_of_le hmul hclamp
  exact rat_div_pos (rat_mul_pos h1 h2) hlam2_pos

/-- Headline Theorem 4 (`swiglu_optimal_diagonal_scale_amgm_law`). -/
theorem swiglu_optimal_diagonal_scale_amgm_law :
    (∀ (εa εw K lam : Rat), lam ≠ 0 →
      sq (diagQuantMSE εa εw K lam) - 4 * sq K * εa * εw =
        sq (εa * sq (K / lam) - εw * sq lam) ∧
      4 * sq K * εa * εw ≤ sq (diagQuantMSE εa εw K lam)) ∧
    (∀ (εa εw K r lam : Rat), (0 : Rat) < εw → lam ≠ 0 → εa = εw * sq r →
      diagQuantMSE εa εw K lam - 2 * K * εw * r =
        εw * sq (sq lam - K * r) / sq lam ∧
      2 * K * εw * r ≤ diagQuantMSE εa εw K lam ∧
      (diagQuantMSE εa εw K lam = 2 * K * εw * r ↔ sq lam = K * r)) ∧
    (∀ (εa εw K r lamStar : Rat), (0 : Rat) < εw → lamStar ≠ 0 →
      εa = εw * sq r → sq lamStar = K * r → K * r ≠ 1 →
      diagQuantMSE εa εw K 1 - diagQuantMSE εa εw K lamStar = εw * sq (K * r - 1) ∧
      diagQuantMSE εa εw K lamStar < diagQuantMSE εa εw K 1) ∧
    (∀ (εa εw K lam : Rat), (0 : Rat) < εw → (0 : Rat) < lam → lam < K →
      sq K * εw ≤ εa →
      diagQuantMSE εa εw K K < diagQuantMSE εa εw K lam) ∧
    (diagQuantMSE (1 / 16) (1 / 16) 4 2 = 1 / 2 ∧
     diagQuantMSE (1 / 16) (1 / 16) 4 1 = 17 / 16 ∧
     diagQuantMSE (1 / 16) (1 / 16) 4 2 < diagQuantMSE (1 / 16) (1 / 16) 4 1 ∧
     diagQuantMSE (1 / 16) (1 / 4096) 16 16 = 1 / 8 ∧
     diagQuantMSE (1 / 16) (1 / 4096) 16 1 = 65537 / 4096 ∧
     diagQuantMSE (1 / 16) (1 / 4096) 16 16 < diagQuantMSE (1 / 16) (1 / 4096) 16 1 ∧
     diagQuantMSE (1 / 16) (1 / 16777216) 16 16 = 4097 / 65536 ∧
     diagQuantMSE (1 / 16) (1 / 16777216) 16 16 < diagQuantMSE (1 / 16) (1 / 16777216) 16 1) := by
  refine ⟨diagQuantMSE_amgm_sq, diagQuantMSE_sos_exact, diagQuantMSE_beats_unscaled,
          diagQuantMSE_clamped_at_K, ?_⟩
  have hw4_opt : diagQuantMSE (1 / 16) (1 / 16) 4 2 = 1 / 2 := by
    simp [diagQuantMSE, sq]; grind
  have hw4_base : diagQuantMSE (1 / 16) (1 / 16) 4 1 = 17 / 16 := by
    simp [diagQuantMSE, sq]; grind
  have hw8_opt : diagQuantMSE (1 / 16) (1 / 4096) 16 16 = 1 / 8 := by
    simp [diagQuantMSE, sq]; grind
  have hw8_base : diagQuantMSE (1 / 16) (1 / 4096) 16 1 = 65537 / 4096 := by
    simp [diagQuantMSE, sq]; grind
  have hw16_opt : diagQuantMSE (1 / 16) (1 / 16777216) 16 16 = 4097 / 65536 := by
    simp [diagQuantMSE, sq]; grind
  have hw16_base : diagQuantMSE (1 / 16) (1 / 16777216) 16 1 = 268435457 / 16777216 := by
    simp [diagQuantMSE, sq]; grind
  refine ⟨hw4_opt, hw4_base, ?_, hw8_opt, hw8_base, ?_, hw16_opt, ?_⟩
  · rw [hw4_opt, hw4_base]
    apply rat_lt_of_sub_pos
    have h : (17 / 16 : Rat) - 1 / 2 = 9 / 16 := by grind
    rw [h]; exact rat_div_pos (by decide) (by decide)
  · rw [hw8_opt, hw8_base]
    apply rat_lt_of_sub_pos
    have h : (65537 / 4096 : Rat) - 1 / 8 = 65025 / 4096 := by grind
    rw [h]; exact rat_div_pos (by decide) (by decide)
  · rw [hw16_opt, hw16_base]
    apply rat_lt_of_sub_pos
    have h : (268435457 / 16777216 : Rat) - 4097 / 65536 = 267386625 / 16777216 := by grind
    rw [h]; exact rat_div_pos (by decide) (by decide)

end SwiGluKurtosis
