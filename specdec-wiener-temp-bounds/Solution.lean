/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecWienerTemp

/-!
# Verified Solutions (`specdec-wiener-temp-bounds`)
-/

namespace SpecDecWienerTempChallenge

open SpecDecWienerTemp

theorem wiener_mmse_temperature_uniquely_minimizes_logit_mse :
    (∀ sz2 sq2 T : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 → T ≠ 0 →
      logitMSE sz2 sq2 T - wienerOptMSE sz2 sq2 =
        (sz2 + sq2) * (1 / T - sz2 / (sz2 + sq2)) * (1 / T - sz2 / (sz2 + sq2))) ∧
    (∀ sz2 sq2 : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 →
      (1 : Rat) < wienerTemp sz2 sq2 ∧
      logitMSE sz2 sq2 (wienerTemp sz2 sq2) = wienerOptMSE sz2 sq2) ∧
    (∀ sz2 sq2 T : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 → T ≠ 0 →
      wienerOptMSE sz2 sq2 ≤ logitMSE sz2 sq2 T ∧
      (logitMSE sz2 sq2 T = wienerOptMSE sz2 sq2 ↔ T = wienerTemp sz2 sq2) ∧
      (T ≠ wienerTemp sz2 sq2 → wienerOptMSE sz2 sq2 < logitMSE sz2 sq2 T)) ∧
    (∀ sz2 szt2 cov beta : Rat, (0 : Rat) < szt2 →
      generalProjMSE sz2 szt2 cov beta - wienerProjOptMSE sz2 szt2 cov =
        szt2 * (beta - wienerProjGain szt2 cov) * (beta - wienerProjGain szt2 cov) ∧
      wienerProjOptMSE sz2 szt2 cov ≤ generalProjMSE sz2 szt2 cov beta) :=
  SpecDecWienerTemp.wiener_mmse_temperature_uniquely_minimizes_logit_mse

theorem wiener_mmse_strictly_beats_variance_matching_and_uncalibrated :
    (∀ sz2 sq2 : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 →
      logitMSE sz2 sq2 1 = sq2 ∧
      logitMSE sz2 sq2 1 - logitMSE sz2 sq2 (wienerTemp sz2 sq2) = (sq2 * sq2) / (sz2 + sq2) ∧
      logitMSE sz2 sq2 (wienerTemp sz2 sq2) < logitMSE sz2 sq2 1) ∧
    (∀ sz2 sq2 Tvar : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 → (0 : Rat) < Tvar →
      Tvar * Tvar = wienerTemp sz2 sq2 →
      (1 : Rat) < Tvar ∧
      Tvar < wienerTemp sz2 sq2 ∧
      logitMSE sz2 sq2 Tvar = 2 * sz2 * (1 - 1 / Tvar) ∧
      logitMSE sz2 sq2 Tvar - logitMSE sz2 sq2 (wienerTemp sz2 sq2) =
        sz2 * ((Tvar - 1) * (Tvar - 1)) / (Tvar * Tvar) ∧
      logitMSE sz2 sq2 (wienerTemp sz2 sq2) < logitMSE sz2 sq2 Tvar ∧
      logitMSE sz2 sq2 Tvar < logitMSE sz2 sq2 1 ∧
      (logitMSE sz2 sq2 1 - logitMSE sz2 sq2 Tvar) /
        (logitMSE sz2 sq2 1 - logitMSE sz2 sq2 (wienerTemp sz2 sq2)) =
        1 - 1 / ((Tvar + 1) * (Tvar + 1)) ∧
      (3 / 4 : Rat) < 1 - 1 / ((Tvar + 1) * (Tvar + 1)) ∧
      1 - 1 / ((Tvar + 1) * (Tvar + 1)) < 1) ∧
    (∀ sz2 sq2 T : Rat, (0 : Rat) < sz2 → (0 : Rat) < sq2 →
      (1 : Rat) ≤ T → T < wienerTemp sz2 sq2 →
      logitMSE sz2 sq2 (wienerTemp sz2 sq2) < logitMSE sz2 sq2 T) :=
  SpecDecWienerTemp.wiener_mmse_strictly_beats_variance_matching_and_uncalibrated

theorem quantized_draft_tv_acceptance_lower_bound_exact :
    (∀ {n : Nat} (p q : Fin n → Rat), isProbDist p → isProbDist q →
      acceptRate p q = 1 - tvDist p q ∧
      (0 : Rat) ≤ acceptRate p q ∧ acceptRate p q ≤ 1 ∧ acceptRate p p = 1) ∧
    (∀ {n : Nat} (p q : Fin n → Rat) (r : Rat),
      isProbDist p → r ≤ 1 → (∀ i : Fin n, r * p i ≤ q i) →
      r ≤ acceptRate p q) ∧
    (∀ {n : Nat} (w wt : Fin n → Rat) (δ : Rat),
      (∀ i : Fin n, (0 : Rat) ≤ w i) → (0 : Rat) < finSum w →
      (0 : Rat) ≤ δ → δ < 1 →
      (∀ i : Fin n, (1 - δ) * w i ≤ wt i) →
      (∀ i : Fin n, wt i ≤ (1 + δ) * w i) →
      (1 - δ) / (1 + δ) ≤ acceptRate (normProb w) (normProb wt) ∧
      tvDist (normProb w) (normProb wt) ≤ (2 * δ) / (1 + δ)) ∧
    (∀ {n : Nat} (p q η : Fin n → Rat),
      isProbDist p → isProbDist q →
      (∀ i : Fin n, ratAbs (p i - q i) ≤ η i) →
      1 - finSum η / 2 ≤ acceptRate p q) ∧
    (∀ {n : Nat} (p : Fin n → Rat), isProbDist p →
      (∀ i : Fin n, (0 : Rat) ≤ 1 - 2 * p i + renyi2Collision p) ∧
      finSum (fun i => p i * (1 - 2 * p i + renyi2Collision p)) = 1 - renyi2Collision p ∧
      finSum (fun i => p i * (1 - 2 * p i + renyi2Collision p)) ≤ 1 - renyi2Collision p ∧
      (∀ s : Fin n → Rat, (∀ i : Fin n, s i * s i ≤ 1 - 2 * p i + renyi2Collision p) →
        finSum (fun i => p i * s i) * finSum (fun i => p i * s i) ≤ 1 - renyi2Collision p)) :=
  SpecDecWienerTemp.quantized_draft_tv_acceptance_lower_bound_exact

theorem expected_specdec_yield_and_speedup_exact :
    (∀ (α : Rat) (γ : Nat),
      (1 - α) * specYieldSum α γ = 1 - ratPow α (γ + 1) ∧
      (α ≠ 1 → specYieldSum α γ = specYieldClosed α γ) ∧
      specYieldSum 1 γ = (γ : Rat) + 1) ∧
    (∀ (α c : Rat) (γ : Nat), α ≠ 1 → (0 : Rat) ≤ c →
      specSpeedup α γ c = specSpeedupClosed α γ c) ∧
    (∀ (α c : Rat) (γ : Nat), (0 : Rat) ≤ c →
      (specSpeedup α γ c ≤ specSpeedup α (γ + 1) c ↔
        c * specYieldSum α γ ≤ ratPow α (γ + 1) * (1 + (γ : Rat) * c)) ∧
      (specSpeedup α γ c < specSpeedup α (γ + 1) c ↔
        c * specYieldSum α γ < ratPow α (γ + 1) * (1 + (γ : Rat) * c))) ∧
    (∀ (α c : Rat) (γ : Nat),
      specMargin α (γ + 1) c - specMargin α γ c =
        (α - 1) * ratPow α (γ + 1) * (1 + ((γ + 1 : Nat) : Rat) * c)) ∧
    (∀ (α c : Rat) (γ0 : Nat),
      (0 : Rat) ≤ α → α ≤ 1 → (0 : Rat) ≤ c → specMargin α γ0 c ≤ 0 →
      ∀ k : Nat, specSpeedup α (γ0 + k) c ≤ specSpeedup α γ0 c) :=
  SpecDecWienerTemp.expected_specdec_yield_and_speedup_exact

theorem sub4bit_self_speculative_dominance_over_fp8_bf16 :
    (∀ (α : Rat) (γ : Nat), (0 : Rat) ≤ α → α ≤ 1 →
      specSpeedup α γ (draftCost 1 16) ≤ 1 ∧
      specSpeedup α γ (draftCost 1 8) < 2) ∧
    (∀ (α c : Rat) (γ : Nat), (0 : Rat) ≤ α → α ≤ 1 → (0 : Rat) < c → c < 1 →
      specSpeedup α γ c < 1 / c) ∧
    (∀ (α1 α2 b1 b2 c0 : Rat) (γ1 γ2 : Nat),
      (0 : Rat) ≤ c0 → (0 : Rat) ≤ b1 → (0 : Rat) ≤ b2 →
      (specSpeedup α2 γ2 (draftCost c0 b2) < specSpeedup α1 γ1 (draftCost c0 b1) ↔
        specYieldSum α2 γ2 * (16 + (γ1 : Rat) * c0 * b1) <
        specYieldSum α1 γ1 * (16 + (γ2 : Rat) * c0 * b2))) ∧
    ((2976 / 1000 : Rat) < specSpeedup (89214 / 100000) 8 (draftCost 1 2) ∧
     specSpeedup (89214 / 100000) 8 (draftCost 1 2) < 2977 / 1000 ∧
     (2520 / 1000 : Rat) < specSpeedup (90707 / 100000) 7 (draftCost 1 3) ∧
     specSpeedup (90707 / 100000) 7 (draftCost 1 3) < 2521 / 1000 ∧
     (2508 / 1000 : Rat) < specSpeedup (95375 / 100000) 10 (draftCost 1 4) ∧
     specSpeedup (95375 / 100000) 10 (draftCost 1 4) < 2509 / 1000 ∧
     specSpeedup (98628 / 100000) 14 (draftCost 1 8) < 176 / 100 ∧
     (∀ (α : Rat) (γ : Nat), (0 : Rat) ≤ α → α ≤ 1 →
       specSpeedup α γ (draftCost 1 8) < specSpeedup (89214 / 100000) 8 (draftCost 1 2) ∧
       specSpeedup α γ (draftCost 1 8) < specSpeedup (90707 / 100000) 7 (draftCost 1 3) ∧
       specSpeedup α γ (draftCost 1 8) < specSpeedup (95375 / 100000) 10 (draftCost 1 4))) ∧
    ((6 : Rat) < specSpeedup (95375 / 100000) 20 (draftCost (1 / 4) 4) ∧
     specSpeedup (98628 / 100000) 26 (draftCost (1 / 4) 8) < 54 / 10) :=
  SpecDecWienerTemp.sub4bit_self_speculative_dominance_over_fp8_bf16

theorem wiener_temperature_exact_acceptance_rescue_witnesses :
    (finSum sigProb = 1 ∧
     finSum noiseProb = 1 ∧
     finSum (fun i : Fin 2 => sigProb i * (sigVal i : Rat)) = 0 ∧
     finSum (fun j : Fin 3 => noiseProb j * (noiseVal j : Rat)) = 0 ∧
     finSum (fun i : Fin 2 => sigProb i * ((sigVal i : Rat) * (sigVal i : Rat))) = 16 ∧
     finSum (fun j : Fin 3 => noiseProb j * ((noiseVal j : Rat) * (noiseVal j : Rat))) = 48 ∧
     finSum (fun i : Fin 2 => sigProb i * finSum (fun j : Fin 3 =>
       noiseProb j * ((sigVal i : Rat) * (noiseVal j : Rat)))) = 0 ∧
     wienerTemp 16 48 = 4 ∧
     (2 : Rat) * 2 = wienerTemp 16 48) ∧
    (expectedBinAccept (3 / 2) 1 < expectedBinAccept (3 / 2) 2 ∧
     expectedBinAccept (3 / 2) 2 < expectedBinAccept (3 / 2) 4 ∧
     expectedBinAccept (5 / 4) 1 < expectedBinAccept (5 / 4) 2 ∧
     expectedBinAccept (5 / 4) 2 < expectedBinAccept (5 / 4) 4) ∧
    (expectedTriAccept (3 / 2) 1 < expectedTriAccept (3 / 2) 2 ∧
     expectedTriAccept (3 / 2) 2 < expectedTriAccept (3 / 2) 4 ∧
     expectedTriAccept (5 / 4) 1 < expectedTriAccept (5 / 4) 2 ∧
     expectedTriAccept (5 / 4) 2 < expectedTriAccept (5 / 4) 4) ∧
    (∀ s_deq z_hat T : Rat, T ≠ 0 →
      (s_deq * z_hat) / T = (s_deq / T) * z_hat) :=
  SpecDecWienerTemp.wiener_temperature_exact_acceptance_rescue_witnesses

end SpecDecWienerTempChallenge
