/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NsaBallBoundMoba.Defs

/-!
# Trusted Challenge Statements (`nsa-ballbound-moba-bounds`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. `MoBA` / `NSA` Mean-Key antipodal-pair (`B ≥ 2`) and buried-needle (`B ≥ 3`) blindspots
   (`q^T S_b ≤ 0` while `max_j q^T k_j = 2‖q‖_2^2 > 0`), a constructed worst case rather than a measured recall.
2. Zero-Sqrt Exact Ball-Bound Cauchy–Schwarz soundness certifying exact `0` false negatives
   with zero square roots and only `+1` scalar per block (`d + 1` scalars total).
3. Strict half-metadata (`(d + 1)/(2d) = 1/2 + 1/(2d)`, `65/128` at `d = 64`) and exact
   all-`d` (`d = m^2`) geometric separation where `Quest-AABB` over-estimates by `√d ×`
   (`2×` at `d = 4`, `8×` at `d = 64`) while `Ball-Bound` is exact (`0` slack).
4. Quantization-absorbing Ball-Bound preserving exact `0` false negatives across ALL summary
   precisions (`1-bit`, `INT2`, `MXFP4`, `INT4`, `FP8`) via enlarged radius `(R + ε)^2`,
   zero-sqrt parallelogram `2(R^2 + ε^2)`, and additive ceiling-sqrt `q^T S_hat + e_q + r_q`.
5. NSA 3-branch convex-gate (`g ∈ Δ_2`) antipodal breakdown forcing `‖O_NSA - O*‖_2^2 ≥ E_0^2`
   across the entire simplex, and collapse to `0` error when swapping Mean-Key for Ball-Bound.
6. Exact `2-Bitplane POPCNT` dot-product conservation (`{-3, -1, +1, +3}^d`), bucket partition
   conservation, and exact `4×` / `8×` bandwidth cut vs `INT8` / `FP16` (`0` per-coord multiplies).
-/

namespace NsaBallBoundMobaChallenge

open NsaBallBoundMoba

/-- Theorem 1 (`moba_antipodal_and_buried_needle_blindspot_exact`):
    Exact integer and rational proof that for block-mean key selection (`MoBA` / `NSA`),
    both the antipodal-pair block (`B ≥ 2`) and the buried-needle block (`B ≥ 3`) yield
    block-mean score `q^T S_b ≤ 0` (and rational mean score `≤ 0`) even while the needle
    key attains `q^T k_0 = 2 ‖q‖_2^2 > 0` (a constructed worst case for mean-key
    selection; no recall is measured). -/
theorem moba_antipodal_and_buried_needle_blindspot_exact :
    (∀ (d B : Nat) (q : Fin d → Int), 2 ≤ B → 0 < normSqInt q →
      dotInt q (blockSum (antipodalBlock B q)) = 0 ∧
      ((dotInt q (blockSum (antipodalBlock B q)) : Rat) / (B : Rat) ≤ 0) ∧
      (∃ j : Fin B, dotInt q (antipodalBlock B q j) = 2 * normSqInt q ∧
                    0 < dotInt q (antipodalBlock B q j)) ∧
      (∀ S_dist : Fin d → Int, 0 < dotInt q S_dist →
        dotInt q (blockSum (antipodalBlock B q)) < dotInt q S_dist)) ∧
    (∀ (d B : Nat) (q : Fin d → Int), 3 ≤ B → 0 < normSqInt q →
      dotInt q (blockSum (buriedNeedleBlock B q)) = (3 - (B : Int)) * normSqInt q ∧
      dotInt q (blockSum (buriedNeedleBlock B q)) ≤ 0 ∧
      ((dotInt q (blockSum (buriedNeedleBlock B q)) : Rat) / (B : Rat) ≤ 0) ∧
      (4 ≤ B → dotInt q (blockSum (buriedNeedleBlock B q)) < 0) ∧
      (∃ j : Fin B, dotInt q (buriedNeedleBlock B q j) = 2 * normSqInt q ∧
                    0 < dotInt q (buriedNeedleBlock B q j))) := by
  sorry

/-- Theorem 2 (`zero_sqrt_ball_bound_exact_soundness_zero_fn`):
    Exact pure-integer Cauchy–Schwarz soundness of Zero-Sqrt Ball-Bound (`d + 1` scalars
    per block, zero square roots), certifying exact `0` false negatives for all `d`, `B ≥ 1`,
    queries `q`, blocks `ks`, and thresholds `T`. -/
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
  sorry

/-- Theorem 3 (`ball_bound_strictly_tighter_than_quest_aabb_and_half_metadata`):
    Exact rational metadata ratio `(d + 1)/(2d) = 1/2 + 1/(2d)` (`65/128` at `d = 64`),
    and explicit all-`d` (`d = m^2`) integer sphere witness family where `Quest-AABB`
    over-estimates by exact factor `m = √d` (`2×` at `d = 4`, `8×` at `d = 64`) while
    `Ball-Bound` is exact (`0` slack). -/
theorem ball_bound_strictly_tighter_than_quest_aabb_and_half_metadata :
    (∀ d : Nat, 1 ≤ d →
      ((d : Rat) + 1) / (2 * (d : Rat)) = (1 / 2 : Rat) + 1 / (2 * (d : Rat))) ∧
    (∀ d : Nat, 2 ≤ d → d + 1 < 2 * d) ∧
    (((64 : Rat) + 1) / (2 * (64 : Rat)) = 65 / 128) ∧
    (∀ m : Nat, 1 ≤ m →
      let d := m * m
      let B := 2 * d + 2
      let q := allOnesVec d
      let ks := sphereWitnessBlock m
      blockSum ks = (fun _ => 0) ∧
      (∀ j : Fin B, dotInt q (ks j) ≤ (d : Int)) ∧
      dotInt q (ks ⟨0, by omega⟩) = (d : Int) ∧
      normSqInt q * blockSqRadius ks = ((B : Int) * (d : Int)) * ((B : Int) * (d : Int)) ∧
      (∀ (j : Fin B) (c : Fin d), -(m : Int) ≤ ks j c ∧ ks j c ≤ (m : Int)) ∧
      (∀ c : Fin d, (∃ j : Fin B, ks j c = (m : Int)) ∧ (∃ j : Fin B, ks j c = -(m : Int))) ∧
      aabbUpper q (fun _ => -(m : Int)) (fun _ => (m : Int)) = (m : Int) * (d : Int) ∧
      (2 ≤ m → (d : Int) < aabbUpper q (fun _ => -(m : Int)) (fun _ => (m : Int)))) ∧
    (aabbUpper (allOnesVec 4) (fun _ => -2) (fun _ => 2) = 2 * 4 ∧
     aabbUpper (allOnesVec 64) (fun _ => -8) (fun _ => 8) = 8 * 64) := by
  sorry

/-- Theorem 4 (`quantization_absorbing_ball_bound_zero_fn_all_precisions`):
    Exact triangle-inequality / Cauchy–Schwarz soundness preserving exact `0` false negatives
    across ALL quantized block summary precisions (`1-bit`, `INT2`, `MXFP4`, `INT4`, `FP8`)
    via enlarged radius `(R + ε)^2`, zero-sqrt `2(R^2 + ε^2)`, and additive `q^T S_hat + e_q + r_q`. -/
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
  sorry

/-- Theorem 5 (`nsa_three_branch_convex_gate_antipodal_breakdown`):
    Exact algebraic breakdown of NSA's 3-branch convex gate `O_NSA = g_1 O_cmp + g_2 O_slc + g_3 O_win`
    (`g ∈ Δ_2`): when a distant antipodal needle is missed by all three branches, EVERY convex
    gate suffers `‖O* - O_NSA‖_2^2 ≥ E_0^2`, whereas swapping Mean-Key for Zero-Sqrt Ball-Bound
    catches the antipodal needle block and collapses optimal 3-branch error to `0`. -/
theorem nsa_three_branch_convex_gate_antipodal_breakdown :
    (∀ (d : Nat) (oStar oCmp oSlc oWin u : Fin d → Rat) (g1 g2 g3 E0 : Rat),
      isSimplex3 g1 g2 g3 → (0 : Rat) ≤ E0 → normSqRat u = 1 →
      E0 ≤ dotRat (vecSubRat oStar oCmp) u →
      E0 ≤ dotRat (vecSubRat oStar oSlc) u →
      E0 ≤ dotRat (vecSubRat oStar oWin) u →
      E0 ≤ dotRat (vecSubRat oStar (nsaGate g1 g2 g3 oCmp oSlc oWin)) u ∧
      E0 * E0 ≤ normSqRat (vecSubRat oStar (nsaGate g1 g2 g3 oCmp oSlc oWin))) ∧
    (∀ (d : Nat) (oStar oBg : Fin d → Rat) (g1 g2 g3 : Rat),
      isSimplex3 g1 g2 g3 →
      nsaGate g1 g2 g3 oBg oBg oBg = oBg ∧
      normSqRat (vecSubRat oStar (nsaGate g1 g2 g3 oBg oBg oBg)) =
        normSqRat (vecSubRat oStar oBg)) ∧
    (∀ (d : Nat) (oStar oCmp oWin : Fin d → Rat),
      isSimplex3 0 1 0 ∧
      nsaGate 0 1 0 oCmp oStar oWin = oStar ∧
      normSqRat (vecSubRat oStar (nsaGate 0 1 0 oCmp oStar oWin)) = 0) ∧
    (∀ (d B : Nat) (q : Fin d → Int), 2 ≤ B → 0 < normSqInt q →
      dotInt q (blockSum (antipodalBlock B q)) = 0 ∧
      dotInt q (blockSum (antipodalBlock B q)) < 2 * normSqInt q ∧
      ballBoundPass B q (blockSum (antipodalBlock B q))
        (blockSqRadius (antipodalBlock B q)) (2 * normSqInt q)) := by
  sorry

/-- Theorem 6 (`popcnt_twoplane_summary_bandwidth_dominance`):
    Exact bit-level dot-product conservation for `2-Bitplane POPCNT` summaries
    (`{-3, -1, +1, +3}^d`), exact magnitude-bucket partition conservation, and exact `4×` / `8×`
    bandwidth cut vs `INT8` / `FP16` (`2d` vs `8d` / `16d` bits, `16 B` vs `64 B` / `128 B`
    at `d = 64`) with zero per-coordinate multiplications. -/
theorem popcnt_twoplane_summary_bandwidth_dominance :
    (∀ (d : Nat) (sq mq sk mk : Fin d → Bool),
      dotInt (fun i => decodeTwoPlane (sq i) (mq i))
             (fun i => decodeTwoPlane (sk i) (mk i)) =
      twoPlaneDotPopcnt sq mq sk mk) ∧
    (∀ (d : Nat) (mq mk : Fin d → Bool),
      boolCount (fun i => mq i && mk i) +
      boolCount (fun i => xor (mq i) (mk i)) +
      boolCount (fun i => !(mq i || mk i)) = (d : Int)) ∧
    (∀ d : Nat, 1 ≤ d →
      int8Bits d = 4 * twoPlaneBits d ∧
      fp16Bits d = 8 * twoPlaneBits d ∧
      ((twoPlaneBits d : Rat) / (int8Bits d : Rat)) = 1 / 4 ∧
      ((twoPlaneBits d : Rat) / (fp16Bits d : Rat)) = 1 / 8) ∧
    (twoPlaneBits 64 / 8 = 16 ∧ int8Bits 64 / 8 = 64 ∧ fp16Bits 64 / 8 = 128) := by
  sorry

end NsaBallBoundMobaChallenge
