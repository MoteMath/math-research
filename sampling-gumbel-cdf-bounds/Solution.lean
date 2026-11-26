/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SamplingHorizons

/-!
# Verified Solutions (`sampling-gumbel-cdf-bounds`)
-/

namespace SamplingHorizonsChallenge

open SamplingHorizons

theorem gumbel_max_impossible_token_horizon_exact :
    (∀ (b : Nat), 1 ≤ b → ∀ (G : Rat → Rat) (gMin gMax z1 z2 : Rat),
      (∀ u : Rat, invPow2Rat b ≤ u → u ≤ 1 - invPow2Rat b → gMin ≤ G u ∧ G u ≤ gMax) →
      gMax - gMin < z1 - z2 →
      (∀ r1 r2 : Fin (2 ^ b), z2 + G (uniformGridVal b r2) < z1 + G (uniformGridVal b r1)) ∧
      gumbelWinCount2 b G z1 z2 = 0 ∧
      gumbelWinProb2 b G z1 z2 = 0) ∧
    (∀ (b : Nat), 1 ≤ b → ∀ (G : Rat → Rat) (z1 z2 : Rat),
      z1 - z2 < G (1 - invPow2Rat b) - G (invPow2Rat b) →
      ∃ r1 r2 : Fin (2 ^ b), z1 + G (uniformGridVal b r1) < z2 + G (uniformGridVal b r2)) ∧
    ((2 : Rat) < expLower 9 (1733 / 2500) ∧
     (13591 / 5000 : Rat) < expLower 8 1 ∧
     pow2Rat 24 * 24 * (1733 / 2500) < ratPow (13591 / 5000) 19 * expLower 3 (9 / 20) ∧
     (1945 / 100 : Rat) < 20 ∧
     pow2Rat 8 * 8 * (1733 / 2500) < ratPow (13591 / 5000) 7 * expLower 3 (13 / 50) ∧
     (726 / 100 : Rat) < 8) :=
  SamplingHorizons.gumbel_max_impossible_token_horizon_exact

theorem specdec_exact_losslessness_vs_finite_residual_crash :
    (∀ (n : Nat) (p q : Fin n → Rat), finSum p = 1 → 0 < specDecZ p q →
      specDecAcceptProb p q + specDecZ p q = 1 ∧
      (∀ v : Fin n, specDecOut p q v = p v) ∧
      tvDist (specDecOut p q) p = 0) ∧
    (∀ (n : Nat) (fl : Rat → Rat) (p q : Fin n → Rat), finSum p = 1 →
      (∀ v : Fin n, fl (p v) ≤ fl (q v)) →
      specDecFlZ fl p q = 0 ∧
      tvDist (specDecCrashedUnnorm p q) p = (1 / 2 : Rat) * specDecZ p q ∧
      (∀ v0 : Fin n, p v0 ≤ q v0 → tvDist (specDecFallbackDist p q v0) p = specDecZ p q)) ∧
    (let pE4M3 : Fin 64 → Rat := fun v => if v.val = 0 then 1 - 63 * invPow2Rat 11 else invPow2Rat 11
     let qE4M3 : Fin 64 → Rat := fun v => if v.val = 0 then 1 else 0
     let flE4M3 : Rat → Rat := fun x =>
       if ratAbs x ≤ invPow2Rat 10 then 0
       else if ratAbs (x - 1) < invPow2Rat 5 then 1 else x
     finSum pE4M3 = 1 ∧ finSum qE4M3 = 1 ∧
     specDecZ pE4M3 qE4M3 = 63 / 2048 ∧ (0 : Rat) < specDecZ pE4M3 qE4M3 ∧
     rneRoundsToGrid (invPow2Rat 4) 16 (pE4M3 ⟨0, by decide⟩) ∧
     (∀ v : Fin 64, v.val ≠ 0 → rneRoundsToGrid (invPow2Rat 9) 0 (pE4M3 v)) ∧
     specDecFlZ flE4M3 pE4M3 qE4M3 = 0 ∧
     tvDist (specDecFallbackDist pE4M3 qE4M3 ⟨0, by decide⟩) pE4M3 = 63 / 2048) ∧
    (let pBF16 : Fin 2 → Rat := fun v =>
       if v.val = 0 then (1 / 2 : Rat) + invPow2Rat 10 else (1 / 2 : Rat) - invPow2Rat 10
     let qBF16 : Fin 2 → Rat := fun _ => 1 / 2
     let flBF16 : Rat → Rat := fun x =>
       if ratAbs (x - 1 / 2) ≤ invPow2Rat 10 then 1 / 2 else x
     finSum pBF16 = 1 ∧ finSum qBF16 = 1 ∧
     specDecZ pBF16 qBF16 = 1 / 1024 ∧ (0 : Rat) < specDecZ pBF16 qBF16 ∧
     rneRoundsToGrid (invPow2Rat 8) 128 (pBF16 ⟨0, by decide⟩) ∧
     rneRoundsToGrid (invPow2Rat 9) 256 (pBF16 ⟨1, by decide⟩) ∧
     specDecFlZ flBF16 pBF16 qBF16 = 0) :=
  SamplingHorizons.specdec_exact_losslessness_vs_finite_residual_crash

theorem specdec_q32_integer_exact_zero_leak :
    (qDenom 32 = 4294967296) ∧
    (∀ (B n : Nat) (P Q : Fin n → Int),
      finSumInt P = qDenom B → finSumInt Q = qDenom B →
      specDecIntAccept P Q + specDecIntZ P Q = qDenom B ∧
      ((∃ v : Fin n, P v ≠ Q v) → 0 < specDecIntZ P Q) ∧
      finSum (qToRat B P) = 1 ∧
      (∀ v : Fin n, specDecOut (qToRat B P) (qToRat B Q) v = qToRat B P v) ∧
      tvDist (specDecOut (qToRat B P) (qToRat B Q)) (qToRat B P) = 0) ∧
    (∀ (B : Nat) (u Pv Qv : Int), 0 < Qv →
      (qAcceptTest B u Pv Qv ↔ (u : Rat) / pow2Rat B < (Pv : Rat) / (Qv : Rat)) ∧
      (Qv ≤ Pv → u < qDenom B → qAcceptTest B u Pv Qv) ∧
      (Pv < Qv → ¬ qAcceptTest B (qDenom B) Pv Qv)) :=
  SamplingHorizons.specdec_q32_integer_exact_zero_leak

theorem descending_cdf_swamping_erasure_law :
    (swampCutoffHalf 7 = 1 / 512 ∧
     swampCutoffHalf 10 = 1 / 4096 ∧
     swampCutoffHalf 23 = 1 / 33554432) ∧
    (∀ (m k : Nat) (p : Rat), (0 : Rat) ≤ p →
      (p < swampCutoffHalf m ∨ (p = swampCutoffHalf m ∧ k % 2 = 0)) →
      rneRoundsToGrid (invPow2Rat (m + 1)) k ((k : Rat) * invPow2Rat (m + 1) + p)) ∧
    (∀ (m V : Nat) (add : Rat → Rat → Rat) (S : Rat) (p : Fin V → Rat) (k0 : Nat) (hk0 : k0 < V),
      (∀ x : Rat, (0 : Rat) ≤ x → x ≤ swampCutoffHalf m → add S x = S) →
      (∀ i : Fin V, (0 : Rat) ≤ p i) →
      (∀ i j : Fin V, i.val ≤ j.val → p j ≤ p i) →
      p ⟨k0, hk0⟩ ≤ swampCutoffHalf m →
      (∀ j : Fin V, k0 ≤ j.val → p j ≤ swampCutoffHalf m ∧ add S (p j) = S) ∧
      seqCdf add S (fun i : Fin (V - k0) => p ⟨k0 + i.val, by omega⟩) = S) ∧
    (32768 - 19647 = 13121 ∧ 0 < 32768 - 19647 ∧ swampCutoffHalf 23 = invPow2Rat 25) :=
  SamplingHorizons.descending_cdf_swamping_erasure_law

theorem fenwick_pairwise_tree_zero_swamping_exact :
    (∀ (add : Rat → Rat → Rat),
      (∀ x : Rat, isDyadicPow2 x → add x x = x + x) →
      ∀ (k r : Nat),
        pairwiseTreeSum add k (invPow2Rat r) = pow2Rat k * invPow2Rat r ∧
        pairwiseTreeSum add k (invPow2Rat r) - pow2Rat k * invPow2Rat r = 0) ∧
    (∀ (add : Rat → Rat → Rat) (k r : Nat),
      (∀ x : Rat, isDyadicPow2 x → add x x = x + x) →
      add (1 / 2 : Rat) (invPow2Rat r) = 1 / 2 →
      seqCdf add (1 / 2 : Rat) (fun _ : Fin (2 ^ k) => invPow2Rat r) = 1 / 2 ∧
      pairwiseTreeSum add k (invPow2Rat r) = pow2Rat k * invPow2Rat r) ∧
    (∀ (add : Rat → Rat → Rat) (r : Nat),
      (∀ x : Rat, isDyadicPow2 x → add x x = x + x) →
      1 ≤ r →
      pairwiseTreeSum add (r - 1) (invPow2Rat r) = 1 / 2) :=
  SamplingHorizons.fenwick_pairwise_tree_zero_swamping_exact

theorem top_p_nucleus_mass_shortfall_lower_bound :
    (∀ (m nHead K : Nat) (add : Rat → Rat → Rat) (S t : Rat)
      (p pEff : Fin (nHead + K) → Rat),
      (1 / 2 : Rat) ≤ S → S ≤ 1 - (K : Rat) * t →
      (0 : Rat) ≤ t → t ≤ swampCutoffHalf m →
      (∀ x : Rat, (0 : Rat) ≤ x → x ≤ swampCutoffHalf m → add S x = S) →
      finSum p = 1 → finSum pEff = 1 →
      (∀ j : Fin K, p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ = t) →
      (∀ j : Fin K, pEff ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ = 0) →
      seqCdf add S (fun j : Fin K => p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩) = S ∧
      (K : Rat) * t ≤ 1 - S ∧
      (finSum (fun i : Fin nHead => p ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right nHead K)⟩) = S →
        1 - S = (K : Rat) * t) ∧
      (K : Rat) * t ≤ tvDist p pEff) ∧
    (let nHead : Nat := 84
     let K : Nat := 128172
     let S : Rat := 7 / 16
     let t : Rat := (9 / 16 : Rat) / (128172 : Rat)
     nHead + K = 128256 ∧
     (1 / 4 : Rat) ≤ S ∧ S < 1 / 2 ∧
     (0 : Rat) < t ∧ t < swampCutoffQuarter 7 ∧
     (K : Rat) * t = 9 / 16 ∧
     (1 / 2 : Rat) < (K : Rat) * t ∧
     ∀ (p pEff : Fin (nHead + K) → Rat),
       finSum p = 1 → finSum pEff = 1 →
       (∀ j : Fin K, p ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ = t) →
       (∀ j : Fin K, pEff ⟨nHead + j.val, Nat.add_lt_add_left j.isLt nHead⟩ = 0) →
       (1 / 2 : Rat) < tvDist p pEff) :=
  SamplingHorizons.top_p_nucleus_mass_shortfall_lower_bound

end SamplingHorizonsChallenge
