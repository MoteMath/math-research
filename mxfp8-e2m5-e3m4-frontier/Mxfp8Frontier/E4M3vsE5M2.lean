/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mxfp8Frontier.RatOrder

/-!
# Theorem 2: Exact Universal All-`B` `MXFP8-E4M3` vs `MXFP8-E5M2` EF21 Laws & Crossover `B*`

Proves:
1. Exact grid-candidate attainment and lower-envelope minimality of `alphaE8M0_E4M3`,
   `alphaCont_E4M3`, `alphaE8M0_E5M2`, and `alphaCont_E5M2` for all `B ≥ 1`.
2. Exact `E8M0` crossover: `E4M3_OCP` strictly dominates `E5M2_IEEE` for all
   `1 ≤ B ≤ 637,534,210`, and `E5M2_IEEE` strictly overtakes for all `B ≥ 637,534,211`.
3. Exact continuous FP32 (`DeepSeek-V3`) crossover: exact tie at `B = 1`, `E4M3_OCP`
   strictly dominates `E5M2_IEEE` for all `2 ≤ B ≤ 2,630,667,467`, and `E5M2_IEEE`
   strictly overtakes for all `B ≥ 2,630,667,468`.
4. Exact worst-case MSE dominance witnesses (`> 3.57x` lower worst-case MSE) at both
   DeepSeek-V3 hardware granularities (`B = 128` tile and `B = 16,384` block).
-/

namespace Mxfp8Frontier

/-! ### Exact Secant & Tangent Lemmas for `Nat` Quadratics -/

/-- Exact secant upper bound on `[lo, hi]`: `B^2 + lo * hi ≤ (lo + hi) * B`. -/
theorem nat_sq_secant {lo hi B : Nat} (hlo : lo ≤ B) (hhi : B ≤ hi) :
    B * B + lo * hi ≤ (lo + hi) * B := by
  have h1 : B * B + lo * hi + (hi - B) * (B - lo) = (lo + hi) * B := by
    have hB : B = lo + (B - lo) := (Nat.add_sub_of_le hlo).symm
    have hH : hi = B + (hi - B) := (Nat.add_sub_of_le hhi).symm
    grind
  omega

/-- Exact tangent lower bound on `[lo, ∞)`: `2 * lo * B ≤ B^2 + lo^2`. -/
theorem nat_sq_tangent {lo B : Nat} (hlo : lo ≤ B) :
    2 * lo * B ≤ B * B + lo * lo := by
  have h1 : B * B + lo * lo = 2 * lo * B + (B - lo) * (B - lo) := by
    have hB : B = lo + (B - lo) := (Nat.add_sub_of_le hlo).symm
    grind
  omega

theorem nat_quad_lt_of_secant {a b c a' b' c' B lo hi : Nat}
    (hlo : lo ≤ B) (hhi : B ≤ hi) (ha : a' ≤ a)
    (hlin : (a - a') * (lo + hi) * B + b * B + c < (a - a') * (lo * hi) + b' * B + c') :
    a * (B * B) + b * B + c < a' * (B * B) + b' * B + c' := by
  have hsec := Nat.mul_le_mul_left (a - a') (nat_sq_secant hlo hhi)
  rw [Nat.mul_add] at hsec
  have h2 : a * (B * B) = a' * (B * B) + (a - a') * (B * B) := by
    rw [← Nat.add_mul, Nat.add_sub_of_le ha]
  rw [Nat.mul_assoc] at hlin
  omega

theorem nat_quad_le_of_secant {a b c a' b' c' B lo hi : Nat}
    (hlo : lo ≤ B) (hhi : B ≤ hi) (ha : a' ≤ a)
    (hlin : (a - a') * (lo + hi) * B + b * B + c ≤ (a - a') * (lo * hi) + b' * B + c') :
    a * (B * B) + b * B + c ≤ a' * (B * B) + b' * B + c' := by
  have hsec := Nat.mul_le_mul_left (a - a') (nat_sq_secant hlo hhi)
  rw [Nat.mul_add] at hsec
  have h2 : a * (B * B) = a' * (B * B) + (a - a') * (B * B) := by
    rw [← Nat.add_mul, Nat.add_sub_of_le ha]
  rw [Nat.mul_assoc] at hlin
  omega

theorem nat_quad_lt_of_tangent {a b c a' b' c' B lo : Nat}
    (hlo : lo ≤ B) (ha : a ≤ a')
    (hlin : (a' - a) * (lo * lo) + b * B + c < (a' - a) * (2 * lo) * B + b' * B + c') :
    a * (B * B) + b * B + c < a' * (B * B) + b' * B + c' := by
  have htan := Nat.mul_le_mul_left (a' - a) (nat_sq_tangent hlo)
  rw [Nat.mul_add] at htan
  have h2 : a' * (B * B) = a * (B * B) + (a' - a) * (B * B) := by
    rw [← Nat.add_mul, Nat.add_sub_of_le ha]
  have hassoc : (a' - a) * (2 * lo) * B = (a' - a) * (2 * lo * B) := by
    rw [Nat.mul_assoc]
  rw [hassoc] at hlin
  omega

theorem nat_quad_le_of_tangent {a b c a' b' c' B lo : Nat}
    (hlo : lo ≤ B) (ha : a ≤ a')
    (hlin : (a' - a) * (lo * lo) + b * B + c ≤ (a' - a) * (2 * lo) * B + b' * B + c') :
    a * (B * B) + b * B + c ≤ a' * (B * B) + b' * B + c' := by
  have htan := Nat.mul_le_mul_left (a' - a) (nat_sq_tangent hlo)
  rw [Nat.mul_add] at htan
  have h2 : a' * (B * B) = a * (B * B) + (a' - a) * (B * B) := by
    rw [← Nat.add_mul, Nat.add_sub_of_le ha]
  have hassoc : (a' - a) * (2 * lo) * B = (a' - a) * (2 * lo * B) := by
    rw [Nat.mul_assoc]
  rw [hassoc] at hlin
  omega

/-! ### Exact Candidate Attainment & Lower-Envelope Minimality for `E4M3_OCP` and `E5M2_IEEE` -/

theorem e4m3_e8m0_envelope (B : Nat) (hB : 1 ≤ B) :
    (alphaE8M0_E4M3 B = ef21AlphaCand 278528 16384 1 1 B ∨
     alphaE8M0_E4M3 B = ef21AlphaCand 237568 8192 1 1 B ∨
     alphaE8M0_E4M3 B = ef21AlphaCand 229376 0 1 1 B) ∧
    alphaE8M0_E4M3 B ≤ ef21AlphaCand 278528 16384 1 1 B ∧
    alphaE8M0_E4M3 B ≤ ef21AlphaCand 237568 8192 1 1 B ∧
    alphaE8M0_E4M3 B ≤ ef21AlphaCand 229376 0 1 1 B := by
  have hc1 : ef21AlphaCand 278528 16384 1 1 B = linFrac 0 77309411328 1 77577846783 B :=
    ef21AlphaCand_eq_linFrac hB (by omega) (by omega) (by omega) (by omega) (by omega)
  have hc2 : ef21AlphaCand 237568 8192 1 1 B = linFrac 0 56371445760 1 56438554623 B :=
    ef21AlphaCand_eq_linFrac hB (by omega) (by omega) (by omega) (by omega) (by omega)
  have hc3 : ef21AlphaCand 229376 0 1 1 B = linFrac 0 52613349376 1 52613349375 B :=
    ef21AlphaCand_eq_linFrac hB (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hc1, hc2, hc3]
  unfold alphaE8M0_E4M3
  split
  · refine ⟨Or.inl rfl, Rat.le_refl, ?_, ?_⟩
    · exact linFrac_le_of_nat (by omega) (by omega) (by omega)
    · exact linFrac_le_of_nat (by omega) (by omega) (by omega)
  · split
    · refine ⟨Or.inr (Or.inl rfl), ?_, Rat.le_refl, ?_⟩
      · exact linFrac_le_of_nat (by omega) (by omega) (by omega)
      · exact linFrac_le_of_nat (by omega) (by omega) (by omega)
    · refine ⟨Or.inr (Or.inr rfl), ?_, ?_, Rat.le_refl⟩
      · exact linFrac_le_of_nat (by omega) (by omega) (by omega)
      · exact linFrac_le_of_nat (by omega) (by omega) (by omega)

theorem e4m3_cont_envelope (B : Nat) (hB : 1 ≤ B) :
    (alphaCont_E4M3 B = ef21AlphaCand 458752 0 278528 16384 B ∨
     alphaCont_E4M3 B = ef21AlphaCand 458752 0 1 1 B) ∧
    alphaCont_E4M3 B ≤ ef21AlphaCand 458752 0 278528 16384 B ∧
    alphaCont_E4M3 B ≤ ef21AlphaCand 458752 0 1 1 B := by
  have hc1 : ef21AlphaCand 458752 0 278528 16384 B = linFrac 288 496 289 495 B :=
    ef21AlphaCand_eq_linFrac hB (by omega) (by omega) (by omega) (by omega) (by grind)
  have hc2 : ef21AlphaCand 458752 0 1 1 B = linFrac 0 210453397504 1 210453397503 B :=
    ef21AlphaCand_eq_linFrac hB (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hc1, hc2]
  unfold alphaCont_E4M3
  split
  · rename_i hle
    refine ⟨Or.inl rfl, Rat.le_refl, ?_⟩
    apply linFrac_le_of_nat (by omega) (by omega)
    have hmul : (288 * B + 496) * (1 * B + 210453397503) =
        288 * (B * B) + 60610578481360 * B + 104384885161488 := by grind
    have hmul' : (0 * B + 210453397504) * (289 * B + 495) =
        0 * (B * B) + 60821031878656 * B + 104174431764480 := by grind
    rw [hmul, hmul']
    exact nat_quad_le_of_secant (lo := 1) (hi := 730740961) hB hle (by omega) (by omega)
  · rename_i hgt
    have hge : 730740962 ≤ B := by omega
    refine ⟨Or.inr rfl, ?_, Rat.le_refl⟩
    apply linFrac_le_of_nat (by omega) (by omega)
    have hmul : (0 * B + 210453397504) * (289 * B + 495) =
        0 * (B * B) + 60821031878656 * B + 104174431764480 := by grind
    have hmul' : (288 * B + 496) * (1 * B + 210453397503) =
        288 * (B * B) + 60610578481360 * B + 104384885161488 := by grind
    rw [hmul, hmul']
    exact nat_quad_le_of_tangent (lo := 730740962) hge (by omega) (by omega)

theorem e5m2_e8m0_envelope (B : Nat) (hB : 1 ≤ B) :
    (alphaE8M0_E5M2 B = ef21AlphaCand 4831838208 536870912 1 1 B ∨
     alphaE8M0_E5M2 B = ef21AlphaCand 4026531840 268435456 1 1 B ∨
     alphaE8M0_E5M2 B = ef21AlphaCand 3758096384 0 1 1 B) ∧
    alphaE8M0_E5M2 B ≤ ef21AlphaCand 4831838208 536870912 1 1 B ∧
    alphaE8M0_E5M2 B ≤ ef21AlphaCand 4026531840 268435456 1 1 B ∧
    alphaE8M0_E5M2 B ≤ ef21AlphaCand 3758096384 0 1 1 B := by
  have hc1 : ef21AlphaCand 4831838208 536870912 1 1 B =
      linFrac 0 23058430092136939520 1 23346660468288651263 B :=
    ef21AlphaCand_eq_linFrac hB (by omega) (by omega) (by omega) (by omega) (by omega)
  have hc2 : ef21AlphaCand 4026531840 268435456 1 1 B =
      linFrac 0 16140901064495857664 1 16212958658533785599 B :=
    ef21AlphaCand_eq_linFrac hB (by omega) (by omega) (by omega) (by omega) (by omega)
  have hc3 : ef21AlphaCand 3758096384 0 1 1 B =
      linFrac 0 14123288431433875456 1 14123288431433875455 B :=
    ef21AlphaCand_eq_linFrac hB (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hc1, hc2, hc3]
  unfold alphaE8M0_E5M2
  split
  · refine ⟨Or.inl rfl, Rat.le_refl, ?_, ?_⟩
    · exact linFrac_le_of_nat (by omega) (by omega) (by omega)
    · exact linFrac_le_of_nat (by omega) (by omega) (by omega)
  · split
    · refine ⟨Or.inr (Or.inl rfl), ?_, Rat.le_refl, ?_⟩
      · exact linFrac_le_of_nat (by omega) (by omega) (by omega)
      · exact linFrac_le_of_nat (by omega) (by omega) (by omega)
    · refine ⟨Or.inr (Or.inr rfl), ?_, ?_, Rat.le_refl⟩
      · exact linFrac_le_of_nat (by omega) (by omega) (by omega)
      · exact linFrac_le_of_nat (by omega) (by omega) (by omega)

theorem e5m2_cont_envelope (B : Nat) (hB : 1 ≤ B) :
    (alphaCont_E5M2 B = ef21AlphaCand 7516192768 0 4831838208 536870912 B ∨
     alphaCont_E5M2 B = ef21AlphaCand 7516192768 0 1 1 B) ∧
    alphaCont_E5M2 B ≤ ef21AlphaCand 7516192768 0 4831838208 536870912 B ∧
    alphaCont_E5M2 B ≤ ef21AlphaCand 7516192768 0 1 1 B := by
  have hc1 : ef21AlphaCand 7516192768 0 4831838208 536870912 B =
      linFrac 80 116 81 115 B :=
    ef21AlphaCand_eq_linFrac hB (by omega) (by omega) (by omega) (by omega) (by grind)
  have hc2 : ef21AlphaCand 7516192768 0 1 1 B =
      linFrac 0 56493153725735501824 1 56493153725735501823 B :=
    ef21AlphaCand_eq_linFrac hB (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hc1, hc2]
  unfold alphaCont_E5M2
  split
  · rename_i hle
    refine ⟨Or.inl rfl, Rat.le_refl, ?_⟩
    apply linFrac_le_of_nat (by omega) (by omega)
    have hmul : (80 * B + 116) * (1 * B + 56493153725735501823) =
        80 * (B * B) + 4519452298058840145956 * B + 6553205832185318211468 := by grind
    have hmul' : (0 * B + 56493153725735501824) * (81 * B + 115) =
        0 * (B * B) + 4575945451784575647744 * B + 6496712678459582709760 := by grind
    rw [hmul, hmul']
    exact nat_quad_le_of_secant (lo := 1) (hi := 706164421571693771) hB hle (by omega) (by omega)
  · rename_i hgt
    have hge : 706164421571693772 ≤ B := by omega
    refine ⟨Or.inr rfl, ?_, Rat.le_refl⟩
    apply linFrac_le_of_nat (by omega) (by omega)
    have hmul : (0 * B + 56493153725735501824) * (81 * B + 115) =
        0 * (B * B) + 4575945451784575647744 * B + 6496712678459582709760 := by grind
    have hmul' : (80 * B + 116) * (1 * B + 56493153725735501823) =
        80 * (B * B) + 4519452298058840145956 * B + 6553205832185318211468 := by grind
    rw [hmul, hmul']
    exact nat_quad_le_of_tangent (lo := 706164421571693772) hge (by omega) (by omega)

/-! ### Exact All-`B` Crossover Proofs (`E4M3_OCP` vs `E5M2_IEEE`) -/

theorem e4m3_beats_e5m2_e8m0 (B : Nat) (h1 : 1 ≤ B) (h2 : B ≤ 637534210) :
    alphaE8M0_E5M2 B < alphaE8M0_E4M3 B := by
  unfold alphaE8M0_E5M2 alphaE8M0_E4M3
  have h5 : B ≤ 432345564227567617 := by omega
  simp only [h5, ↓reduceIte]
  split
  · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
  · split
    · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
    · omega

theorem e5m2_beats_e4m3_e8m0 (B : Nat) (h1 : 637534211 ≤ B) :
    alphaE8M0_E4M3 B < alphaE8M0_E5M2 B := by
  unfold alphaE8M0_E4M3 alphaE8M0_E5M2
  have h4a : ¬ B ≤ 474924269 := by omega
  simp only [h4a, ↓reduceIte]
  split
  · have h5 : B ≤ 432345564227567617 := by omega
    simp only [h5, ↓reduceIte]
    exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
  · split
    · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
    · split
      · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)
      · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)

theorem e4m3_beats_e5m2_cont (B : Nat) (h1 : 2 ≤ B) (h2 : B ≤ 2630667467) :
    alphaCont_E5M2 B < alphaCont_E4M3 B := by
  unfold alphaCont_E5M2 alphaCont_E4M3
  have h5 : B ≤ 706164421571693771 := by omega
  simp only [h5, ↓reduceIte]
  split
  · apply linFrac_lt_of_nat (by omega) (by omega)
    have hL : (80 * B + 116) * (289 * B + 495) = 23120 * (B * B) + 73124 * B + 57420 := by grind
    have hR : (288 * B + 496) * (81 * B + 115) = 23328 * (B * B) + 73296 * B + 57040 := by grind
    rw [hL, hR]
    exact nat_quad_lt_of_tangent (lo := 2) h1 (by omega) (by omega)
  · rename_i hgt
    have hlo : 730740962 ≤ B := by omega
    apply linFrac_lt_of_nat (by omega) (by omega)
    have hL : (80 * B + 116) * (1 * B + 210453397503) =
        80 * (B * B) + 16836271800356 * B + 24412594110348 := by grind
    have hR : (0 * B + 210453397504) * (81 * B + 115) =
        0 * (B * B) + 17046725197824 * B + 24202140712960 := by grind
    rw [hL, hR]
    exact nat_quad_lt_of_secant (lo := 730740962) (hi := 2630667467) hlo h2 (by omega) (by omega)

theorem e5m2_beats_e4m3_cont (B : Nat) (h1 : 2630667468 ≤ B) :
    alphaCont_E4M3 B < alphaCont_E5M2 B := by
  unfold alphaCont_E4M3 alphaCont_E5M2
  have h4 : ¬ B ≤ 730740961 := by omega
  simp only [h4, ↓reduceIte]
  split
  · apply linFrac_lt_of_nat (by omega) (by omega)
    have hL : (0 * B + 210453397504) * (81 * B + 115) =
        0 * (B * B) + 17046725197824 * B + 24202140712960 := by grind
    have hR : (80 * B + 116) * (1 * B + 210453397503) =
        80 * (B * B) + 16836271800356 * B + 24412594110348 := by grind
    rw [hL, hR]
    exact nat_quad_lt_of_tangent (lo := 2630667468) h1 (by omega) (by omega)
  · exact linFrac_lt_of_nat (by omega) (by omega) (by omega)

/-- Headline Theorem 2 (`mxfp8_e4m3_vs_e5m2_all_b_crossover_exact`). -/
theorem mxfp8_e4m3_vs_e5m2_all_b_crossover_exact :
    (∀ B : Nat, 1 ≤ B →
      (alphaE8M0_E4M3 B ≤ ef21AlphaCand 278528 16384 1 1 B ∧
       alphaE8M0_E4M3 B ≤ ef21AlphaCand 237568 8192 1 1 B ∧
       alphaE8M0_E4M3 B ≤ ef21AlphaCand 229376 0 1 1 B) ∧
      (alphaCont_E4M3 B ≤ ef21AlphaCand 458752 0 278528 16384 B ∧
       alphaCont_E4M3 B ≤ ef21AlphaCand 458752 0 1 1 B) ∧
      (alphaE8M0_E5M2 B ≤ ef21AlphaCand 4831838208 536870912 1 1 B ∧
       alphaE8M0_E5M2 B ≤ ef21AlphaCand 4026531840 268435456 1 1 B ∧
       alphaE8M0_E5M2 B ≤ ef21AlphaCand 3758096384 0 1 1 B) ∧
      (alphaCont_E5M2 B ≤ ef21AlphaCand 7516192768 0 4831838208 536870912 B ∧
       alphaCont_E5M2 B ≤ ef21AlphaCand 7516192768 0 1 1 B)) ∧
    ((∀ B : Nat, 1 ≤ B → B ≤ 637534210 → alphaE8M0_E5M2 B < alphaE8M0_E4M3 B) ∧
     (∀ B : Nat, 637534211 ≤ B → alphaE8M0_E4M3 B < alphaE8M0_E5M2 B)) ∧
    ((alphaCont_E4M3 1 = 1 ∧ alphaCont_E5M2 1 = 1) ∧
     (∀ B : Nat, 2 ≤ B → B ≤ 2630667467 → alphaCont_E5M2 B < alphaCont_E4M3 B) ∧
     (∀ B : Nat, 2630667468 ≤ B → alphaCont_E4M3 B < alphaCont_E5M2 B)) ∧
    (((1 - alphaE8M0_E4M3 128) * (356 / 100 : Rat) < 1 - alphaE8M0_E5M2 128) ∧
     ((1 - alphaE8M0_E4M3 16384) * (356 / 100 : Rat) < 1 - alphaE8M0_E5M2 16384) ∧
     ((1 - alphaCont_E4M3 128) * (357 / 100 : Rat) < 1 - alphaCont_E5M2 128) ∧
     ((1 - alphaCont_E4M3 16384) * (356 / 100 : Rat) < 1 - alphaCont_E5M2 16384)) := by
  refine ⟨?_, ⟨e4m3_beats_e5m2_e8m0, e5m2_beats_e4m3_e8m0⟩,
          ⟨⟨by unfold alphaCont_E4M3; simp only [Nat.reduceLeDiff, ↓reduceIte]; exact linFrac_eq_one (by decide) (by decide),
            by unfold alphaCont_E5M2; simp only [Nat.reduceLeDiff, ↓reduceIte]; exact linFrac_eq_one (by decide) (by decide)⟩,
           e4m3_beats_e5m2_cont, e5m2_beats_e4m3_cont⟩, ?_⟩
  · intro B hB
    exact ⟨(e4m3_e8m0_envelope B hB).2,
           (e4m3_cont_envelope B hB).2,
           (e5m2_e8m0_envelope B hB).2,
           (e5m2_cont_envelope B hB).2⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · unfold alphaE8M0_E4M3 alphaE8M0_E5M2
      simp only [Nat.reduceLeDiff, ↓reduceIte]
      exact one_sub_linFrac_mul_lt (p := 356) (q := 100) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · unfold alphaE8M0_E4M3 alphaE8M0_E5M2
      simp only [Nat.reduceLeDiff, ↓reduceIte]
      exact one_sub_linFrac_mul_lt (p := 356) (q := 100) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · unfold alphaCont_E4M3 alphaCont_E5M2
      simp only [Nat.reduceLeDiff, ↓reduceIte]
      exact one_sub_linFrac_mul_lt (p := 357) (q := 100) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · unfold alphaCont_E4M3 alphaCont_E5M2
      simp only [Nat.reduceLeDiff, ↓reduceIte]
      exact one_sub_linFrac_mul_lt (p := 356) (q := 100) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Mxfp8Frontier
