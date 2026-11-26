/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mrope3dCoprime.RatOrder

/-!
# Theorems 5 & 6: `Q32` Modular 3D Phase Homomorphism & Cross-Modal `BF16` / `FP16` Drift Collapse

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
5. `q32_3d_modular_phase_exact_relative_invariance`: exact zero-error 3D relative-position
   homomorphism `(Φ(T2, H2, W2) - Φ(T1, H1, W1)) mod 2^32 = Φ(T2 - T1, H2 - H1, W2 - W1)`
   for ALL `(Ti, Hi, Wi) ∈ ℤ^3`, cross-modal text-diagonal `(m, m, m)` invariance at arbitrary `m`,
   and full period `2^32` along any axis with odd frequency `ω_a`.
6. `cross_modal_fp_phase_drift_vs_q32_exact`: at `m = 131,072 = 2^17`, `BF16` (`p = 7`) has
   `ulp(2^17) = 2^{10} = 1024`, collapsing EVERY video coordinate `(T, H, W) ∈ [0,255]×[0,63]×[0,63]`
   in `m - T, m - H, m - W` identically to `2^17`, and `FP16` overflows to `+Inf` (`2^17 > 65504`),
   while `Q32` modular phase remains exact (`0` drift) and injective on every axis.
-/

namespace Mrope3dCoprime

/-! ### Part 1: `Q32` Modular 3D Phase & Odd-Frequency Full Period (Theorem 5) -/

/-- Exact modular subtraction identity `(a % M - b % M) % M = (a - b) % M` for `M > 0`. -/
theorem int_emod_sub_emod (a b M : Int) :
    (a % M - b % M) % M = (a - b) % M := by
  rw [Int.sub_emod, Int.emod_emod, Int.emod_emod, ← Int.sub_emod]

/-- Odd multiplier cancellation modulo `2^k`: for any `k : Nat`, `ω % 2 = 1` implies
    `(Δ * ω) % 2^k = 0 ↔ Δ % 2^k = 0`. -/
theorem odd_mul_emod_pow2_eq_zero (k : Nat) :
    ∀ (ω Δ : Int), ω % 2 = 1 → ((Δ * ω) % (2 ^ k : Int) = 0 ↔ Δ % (2 ^ k : Int) = 0) := by
  induction k with
  | zero =>
    intro ω Δ _
    simp
  | succ k ih =>
    intro ω Δ hodd
    have hpow : (2 ^ (k + 1) : Int) = 2 * (2 ^ k : Int) := by
      rw [Int.pow_succ, Int.mul_comm]
    constructor
    · intro h0
      have hdvd : (2 ^ (k + 1) : Int) ∣ Δ * ω := Int.dvd_of_emod_eq_zero h0
      rw [hpow] at hdvd
      rcases hdvd with ⟨q, hq⟩
      have h2_mul : (Δ * ω) % 2 = 0 := by
        rw [hq]
        have h : 2 * (2 ^ k : Int) * q = 2 * ((2 ^ k : Int) * q) := by grind
        rw [h]
        exact Int.mul_emod_right 2 _
      have hΔ_even : Δ % 2 = 0 := by
        have hmul_mod := Int.mul_emod Δ ω 2
        rw [hodd, h2_mul] at hmul_mod
        omega
      have hΔ_eq : Δ = 2 * (Δ / 2) := by omega
      have hq' : (Δ / 2) * ω = (2 ^ k : Int) * q := by
        have h2eq : 2 * ((Δ / 2) * ω) = 2 * ((2 ^ k : Int) * q) := by
          calc 2 * ((Δ / 2) * ω) = (2 * (Δ / 2)) * ω := by grind
            _ = Δ * ω := by rw [← hΔ_eq]
            _ = 2 * (2 ^ k : Int) * q := hq
            _ = 2 * ((2 ^ k : Int) * q) := by grind
        omega
      have hdvd_k : (2 ^ k : Int) ∣ (Δ / 2) * ω := ⟨q, hq'⟩
      have hmod_k : ((Δ / 2) * ω) % (2 ^ k : Int) = 0 := Int.emod_eq_zero_of_dvd hdvd_k
      have hΔ2_mod : (Δ / 2) % (2 ^ k : Int) = 0 := (ih ω (Δ / 2) hodd).mp hmod_k
      rcases Int.dvd_of_emod_eq_zero hΔ2_mod with ⟨r, hr⟩
      apply Int.emod_eq_zero_of_dvd
      rw [hpow]
      refine ⟨r, ?_⟩
      calc Δ = 2 * (Δ / 2) := hΔ_eq
        _ = 2 * ((2 ^ k : Int) * r) := by rw [hr]
        _ = 2 * (2 ^ k : Int) * r := by grind
    · intro h0
      rcases Int.dvd_of_emod_eq_zero h0 with ⟨r, hr⟩
      apply Int.emod_eq_zero_of_dvd
      refine ⟨r * ω, ?_⟩
      calc Δ * ω = ((2 ^ (k + 1) : Int) * r) * ω := by rw [hr]
        _ = (2 ^ (k + 1) : Int) * (r * ω) := by grind

/-- **Theorem 5 (`q32_3d_modular_phase_exact_relative_invariance`)**:
    Proves exact zero-error 3D relative-position homomorphism for `Q32` modular integer phase
    for ALL `(T1, H1, W1), (T2, H2, W2) ∈ ℤ^3`, cross-modal text-diagonal `(m, m, m)` invariance
    at arbitrary `m ∈ ℤ` (including `m = 131,072` and beyond), exact shift invariance, and full
    period `2^32` along every axis with an odd frequency `ω_a`. -/
theorem q32_3d_modular_phase_exact_relative_invariance :
    (∀ ωT ωH ωW T1 H1 W1 T2 H2 W2 : Int,
      q32PhaseDiff (q32Phase ωT ωH ωW T2 H2 W2) (q32Phase ωT ωH ωW T1 H1 W1) =
        q32Phase ωT ωH ωW (T2 - T1) (H2 - H1) (W2 - W1)) ∧
    (∀ ωT ωH ωW m T H W : Int,
      q32PhaseDiff (q32Phase ωT ωH ωW T H W) (q32Phase ωT ωH ωW m m m) =
        q32Phase ωT ωH ωW (T - m) (H - m) (W - m)) ∧
    (∀ ωT ωH ωW T1 H1 W1 T2 H2 W2 sT sH sW : Int,
      q32PhaseDiff (q32Phase ωT ωH ωW (T2 + sT) (H2 + sH) (W2 + sW))
                   (q32Phase ωT ωH ωW (T1 + sT) (H1 + sH) (W1 + sW)) =
        q32PhaseDiff (q32Phase ωT ωH ωW T2 H2 W2) (q32Phase ωT ωH ωW T1 H1 W1)) ∧
    (∀ ωT ωH ωW T H W : Int,
      q32Phase ωT ωH ωW (T + Q32_MOD) H W = q32Phase ωT ωH ωW T H W ∧
      q32Phase ωT ωH ωW T (H + Q32_MOD) W = q32Phase ωT ωH ωW T H W ∧
      q32Phase ωT ωH ωW T H (W + Q32_MOD) = q32Phase ωT ωH ωW T H W) ∧
    (∀ ω Δ : Int, ω % 2 = 1 → ((Δ * ω) % Q32_MOD = 0 ↔ Δ % Q32_MOD = 0)) ∧
    (∀ ωT ωH ωW T H W Δ : Int, 0 < Δ → Δ < Q32_MOD →
      (ωT % 2 = 1 → q32Phase ωT ωH ωW (T + Δ) H W ≠ q32Phase ωT ωH ωW T H W) ∧
      (ωH % 2 = 1 → q32Phase ωT ωH ωW T (H + Δ) W ≠ q32Phase ωT ωH ωW T H W) ∧
      (ωW % 2 = 1 → q32Phase ωT ωH ωW T H (W + Δ) ≠ q32Phase ωT ωH ωW T H W)) := by
  have hhom : ∀ ωT ωH ωW T1 H1 W1 T2 H2 W2 : Int,
      q32PhaseDiff (q32Phase ωT ωH ωW T2 H2 W2) (q32Phase ωT ωH ωW T1 H1 W1) =
        q32Phase ωT ωH ωW (T2 - T1) (H2 - H1) (W2 - W1) := by
    intro ωT ωH ωW T1 H1 W1 T2 H2 W2
    unfold q32PhaseDiff q32Phase
    rw [int_emod_sub_emod]
    congr 1
    grind
  have hodd32 : ∀ ω Δ : Int, ω % 2 = 1 → ((Δ * ω) % Q32_MOD = 0 ↔ Δ % Q32_MOD = 0) :=
    fun ω Δ hodd => odd_mul_emod_pow2_eq_zero 32 ω Δ hodd
  refine ⟨hhom, ?_, ?_, ?_, hodd32, ?_⟩
  · intro ωT ωH ωW m T H W
    exact hhom ωT ωH ωW m m m T H W
  · intro ωT ωH ωW T1 H1 W1 T2 H2 W2 sT sH sW
    rw [hhom, hhom]
    have h1 : (T2 + sT) - (T1 + sT) = T2 - T1 := by grind
    have h2 : (H2 + sH) - (H1 + sH) = H2 - H1 := by grind
    have h3 : (W2 + sW) - (W1 + sW) = W2 - W1 := by grind
    rw [h1, h2, h3]
  · intro ωT ωH ωW T H W
    refine ⟨?_, ?_, ?_⟩
    · unfold q32Phase
      have h : (T + Q32_MOD) * ωT + H * ωH + W * ωW =
          (T * ωT + H * ωH + W * ωW) + Q32_MOD * ωT := by grind
      rw [h, Int.add_mul_emod_self_left]
    · unfold q32Phase
      have h : T * ωT + (H + Q32_MOD) * ωH + W * ωW =
          (T * ωT + H * ωH + W * ωW) + Q32_MOD * ωH := by grind
      rw [h, Int.add_mul_emod_self_left]
    · unfold q32Phase
      have h : T * ωT + H * ωH + (W + Q32_MOD) * ωW =
          (T * ωT + H * ωH + W * ωW) + Q32_MOD * ωW := by grind
      rw [h, Int.add_mul_emod_self_left]
  · intro ωT ωH ωW T H W Δ hΔpos hΔlt
    have hΔmod_ne : Δ % Q32_MOD ≠ 0 := by
      have h : Δ % Q32_MOD = Δ := Int.emod_eq_of_lt (by omega) hΔlt
      rw [h]; omega
    refine ⟨?_, ?_, ?_⟩
    · intro hodd heq
      have hdiff : q32PhaseDiff (q32Phase ωT ωH ωW (T + Δ) H W) (q32Phase ωT ωH ωW T H W) = 0 := by
        rw [heq]; unfold q32PhaseDiff; simp
      rw [hhom] at hdiff
      have hsimp : q32Phase ωT ωH ωW (T + Δ - T) (H - H) (W - W) = (Δ * ωT) % Q32_MOD := by
        unfold q32Phase
        have h : (T + Δ - T) * ωT + (H - H) * ωH + (W - W) * ωW = Δ * ωT := by grind
        rw [h]
      rw [hsimp] at hdiff
      exact hΔmod_ne ((hodd32 ωT Δ hodd).mp hdiff)
    · intro hodd heq
      have hdiff : q32PhaseDiff (q32Phase ωT ωH ωW T (H + Δ) W) (q32Phase ωT ωH ωW T H W) = 0 := by
        rw [heq]; unfold q32PhaseDiff; simp
      rw [hhom] at hdiff
      have hsimp : q32Phase ωT ωH ωW (T - T) (H + Δ - H) (W - W) = (Δ * ωH) % Q32_MOD := by
        unfold q32Phase
        have h : (T - T) * ωT + (H + Δ - H) * ωH + (W - W) * ωW = Δ * ωH := by grind
        rw [h]
      rw [hsimp] at hdiff
      exact hΔmod_ne ((hodd32 ωH Δ hodd).mp hdiff)
    · intro hodd heq
      have hdiff : q32PhaseDiff (q32Phase ωT ωH ωW T H (W + Δ)) (q32Phase ωT ωH ωW T H W) = 0 := by
        rw [heq]; unfold q32PhaseDiff; simp
      rw [hhom] at hdiff
      have hsimp : q32Phase ωT ωH ωW (T - T) (H - H) (W + Δ - W) = (Δ * ωW) % Q32_MOD := by
        unfold q32Phase
        have h : (T - T) * ωT + (H - H) * ωH + (W + Δ - W) * ωW = Δ * ωW := by grind
        rw [h]
      rw [hsimp] at hdiff
      exact hΔmod_ne ((hodd32 ωW Δ hodd).mp hdiff)

/-! ### Part 2: Cross-Modal `BF16` ULP Collapse & `FP16` Overflow vs `Q32` Exact (Theorem 6) -/

/-- **Theorem 6 (`cross_modal_fp_phase_drift_vs_q32_exact`)**:
    Proves that for cross-modal attention from text diagonal `(m, m, m)` at `m = 131,072 = 2^{17}`
    to video `(T, H, W) ∈ [0, 255] × [0, 63] × [0, 63]`:
    (1) `BF16` (`p = 7`) has exact `ulp(2^{17}) = 2^{10} = 1024` (and `ulp(2^{16}) = 512` below `2^{17}`),
        so EVERY relative coordinate `m - T`, `m - H`, `m - W` (and `m + T`, `m + H`, `m + W`)
        lies inside the RNE snap-to-`2^{17}` zone, collapsing the entire `256 × 64 × 64` video grid
        to a single constant `2^{17}`;
    (2) `FP16` (`FP16_MAX = (2 - 2^{-10}) * 2^{15} = 65,504`) overflows to `+Inf` at `m = 131,072`
        and at every cross-modal difference `m - T` for `T ∈ [0, 255]`;
    (3) `Q32` modular integer phase maintains exact zero-drift relative invariance at `m = 131,072`
        and strict injectivity across all distinct video coordinates `T1 ≠ T2 ∈ [0, 255]` (and
        `H1 ≠ H2, W1 ≠ W2 ∈ [0, 63]`) whenever `ωT, ωH, ωW` are odd. -/
theorem cross_modal_fp_phase_drift_vs_q32_exact :
    (pow2Rat 17 = 131072 ∧
      fpUlpAtPow2 7 17 = 1024 ∧
      fpUlpAtPow2 7 16 = 512 ∧
      FP16_MAX = (2 - invPow2Rat 10) * pow2Rat 15 ∧
      fp16Overflows (pow2Rat 17)) ∧
    (∀ T H W : Nat, T ≤ 255 → H ≤ 63 → W ≤ 63 →
      rneSnapsToPow2 7 17 (pow2Rat 17 - (T : Rat)) ∧
      rneSnapsToPow2 7 17 (pow2Rat 17 - (H : Rat)) ∧
      rneSnapsToPow2 7 17 (pow2Rat 17 - (W : Rat)) ∧
      rneSnapsToPow2 7 17 (pow2Rat 17 + (T : Rat)) ∧
      fp16Overflows (pow2Rat 17 - (T : Rat))) ∧
    (∀ ωT ωH ωW : Int, ∀ T H W : Nat,
      q32PhaseDiff (q32Phase ωT ωH ωW T H W) (q32Phase ωT ωH ωW 131072 131072 131072) =
        q32Phase ωT ωH ωW ((T : Int) - 131072) ((H : Int) - 131072) ((W : Int) - 131072)) ∧
    (∀ ωT ωH ωW : Int, ωT % 2 = 1 → ωH % 2 = 1 → ωW % 2 = 1 →
      (∀ T1 T2 H W : Nat, T1 ≤ 255 → T2 ≤ 255 → T1 ≠ T2 →
        q32PhaseDiff (q32Phase ωT ωH ωW T1 H W) (q32Phase ωT ωH ωW 131072 131072 131072) ≠
        q32PhaseDiff (q32Phase ωT ωH ωW T2 H W) (q32Phase ωT ωH ωW 131072 131072 131072)) ∧
      (∀ T H1 H2 W : Nat, H1 ≤ 63 → H2 ≤ 63 → H1 ≠ H2 →
        q32PhaseDiff (q32Phase ωT ωH ωW T H1 W) (q32Phase ωT ωH ωW 131072 131072 131072) ≠
        q32PhaseDiff (q32Phase ωT ωH ωW T H2 W) (q32Phase ωT ωH ωW 131072 131072 131072)) ∧
      (∀ T H W1 W2 : Nat, W1 ≤ 63 → W2 ≤ 63 → W1 ≠ W2 →
        q32PhaseDiff (q32Phase ωT ωH ωW T H W1) (q32Phase ωT ωH ωW 131072 131072 131072) ≠
        q32PhaseDiff (q32Phase ωT ωH ωW T H W2) (q32Phase ωT ωH ωW 131072 131072 131072))) := by
  have hconst : pow2Rat 17 = 131072 ∧
      fpUlpAtPow2 7 17 = 1024 ∧
      fpUlpAtPow2 7 16 = 512 ∧
      FP16_MAX = (2 - invPow2Rat 10) * pow2Rat 15 ∧
      fp16Overflows (pow2Rat 17) := by
    have hp17 : pow2Rat 17 = 131072 := by unfold pow2Rat; rfl
    have hp16 : pow2Rat 16 = 65536 := by unfold pow2Rat; rfl
    have hp15 : pow2Rat 15 = 32768 := by unfold pow2Rat; rfl
    have hp10 : pow2Rat 10 = 1024 := by unfold pow2Rat; rfl
    have hp7 : pow2Rat 7 = 128 := by unfold pow2Rat; rfl
    refine ⟨hp17, ?_, ?_, ?_, ?_⟩
    · unfold fpUlpAtPow2; rw [hp17, hp7]; grind
    · unfold fpUlpAtPow2; rw [hp16, hp7]; grind
    · unfold FP16_MAX invPow2Rat; rw [hp10, hp15]; grind
    · unfold fp16Overflows FP16_MAX; rw [hp17]; decide
  have hlow : fpUlpAtPow2 7 16 / 2 = 256 := by rw [hconst.2.2.1]; grind
  have hhi : fpUlpAtPow2 7 17 / 2 = 512 := by rw [hconst.2.1]; grind
  have hsnap_sub : ∀ d : Nat, d ≤ 256 → rneSnapsToPow2 7 17 (pow2Rat 17 - (d : Rat)) := by
    intro d hd
    unfold rneSnapsToPow2
    have h16 : (17 - 1 : Nat) = 16 := by decide
    rw [h16, hlow, hhi]
    have hd_le : (d : Rat) ≤ (256 : Rat) := rat_natCast_le hd
    have hd_nn : (0 : Rat) ≤ (d : Rat) := rat_natCast_nonneg d
    constructor
    · apply rat_le_of_sub_nonneg
      have heq : (pow2Rat 17 - (d : Rat)) - (pow2Rat 17 - 256) = (256 : Rat) - (d : Rat) := by grind
      rw [heq]; exact rat_sub_nonneg hd_le
    · apply rat_le_of_sub_nonneg
      have heq : (pow2Rat 17 + 512) - (pow2Rat 17 - (d : Rat)) = (512 : Rat) + (d : Rat) := by grind
      rw [heq]; exact rat_add_nonneg (by decide) hd_nn
  have hsnap_add : ∀ d : Nat, d ≤ 512 → rneSnapsToPow2 7 17 (pow2Rat 17 + (d : Rat)) := by
    intro d hd
    unfold rneSnapsToPow2
    have h16 : (17 - 1 : Nat) = 16 := by decide
    rw [h16, hlow, hhi]
    have hd_le : (d : Rat) ≤ (512 : Rat) := rat_natCast_le hd
    have hd_nn : (0 : Rat) ≤ (d : Rat) := rat_natCast_nonneg d
    constructor
    · apply rat_le_of_sub_nonneg
      have heq : (pow2Rat 17 + (d : Rat)) - (pow2Rat 17 - 256) = (256 : Rat) + (d : Rat) := by grind
      rw [heq]; exact rat_add_nonneg (by decide) hd_nn
    · apply rat_le_of_sub_nonneg
      have heq : (pow2Rat 17 + 512) - (pow2Rat 17 + (d : Rat)) = (512 : Rat) - (d : Rat) := by grind
      rw [heq]; exact rat_sub_nonneg hd_le
  refine ⟨hconst, ?_, ?_, ?_⟩
  · intro T H W hT hH hW
    refine ⟨hsnap_sub T (by omega), hsnap_sub H (by omega), hsnap_sub W (by omega),
            hsnap_add T (by omega), ?_⟩
    unfold fp16Overflows FP16_MAX
    rw [hconst.1]
    have hT_le : (T : Rat) ≤ (255 : Rat) := rat_natCast_le hT
    apply rat_lt_of_sub_pos
    have h1 : (65313 : Rat) ≤ (131072 : Rat) - (T : Rat) - 65504 := by
      apply rat_le_of_sub_nonneg
      have heq : ((131072 : Rat) - (T : Rat) - 65504) - 65313 = (255 : Rat) - (T : Rat) := by grind
      rw [heq]; exact rat_sub_nonneg hT_le
    exact rat_lt_of_lt_of_le (by decide) h1
  · intro ωT ωH ωW T H W
    exact q32_3d_modular_phase_exact_relative_invariance.2.1 ωT ωH ωW 131072 T H W
  · intro ωT ωH ωW hωT hωH hωW
    have hhom := q32_3d_modular_phase_exact_relative_invariance.1
    have hodd := q32_3d_modular_phase_exact_relative_invariance.2.2.2.2.1
    -- Helper: if `((a - b) * ω) % Q32_MOD = 0` with `ω` odd and `0 ≤ a, b ≤ 255`, then `a = b`.
    have hinj_coord : ∀ (ω : Int) (a b : Nat), ω % 2 = 1 → a ≤ 255 → b ≤ 255 →
        (((a : Int) - (b : Int)) * ω) % Q32_MOD = 0 → a = b := by
      intro ω a b hω ha hb h0
      have hmod := (hodd ω ((a : Int) - (b : Int)) hω).mp h0
      have hlt : -Q32_MOD < (a : Int) - (b : Int) ∧ (a : Int) - (b : Int) < Q32_MOD := by
        unfold Q32_MOD; omega
      rcases Int.dvd_of_emod_eq_zero hmod with ⟨k, hk⟩
      have hk0 : k = 0 := by
        apply Classical.byContradiction
        intro hkne
        have hpos : k ≥ 1 ∨ k ≤ -1 := by omega
        rcases hpos with h1 | h1
        · have hge : Q32_MOD * 1 ≤ Q32_MOD * k :=
            Int.mul_le_mul_of_nonneg_left h1 (by unfold Q32_MOD; decide)
          omega
        · have hle : Q32_MOD * k ≤ Q32_MOD * (-1) :=
            Int.mul_le_mul_of_nonneg_left h1 (by unfold Q32_MOD; decide)
          omega
      subst hk0
      omega
    refine ⟨?_, ?_, ?_⟩
    · intro T1 T2 H W hT1 hT2 hne heq
      rw [hhom, hhom] at heq
      have h0 : q32PhaseDiff (q32Phase ωT ωH ωW ((T1 : Int) - 131072) ((H : Int) - 131072) ((W : Int) - 131072))
                             (q32Phase ωT ωH ωW ((T2 : Int) - 131072) ((H : Int) - 131072) ((W : Int) - 131072)) = 0 := by
        rw [heq]; unfold q32PhaseDiff; simp
      rw [hhom] at h0
      have hsimp : q32Phase ωT ωH ωW (((T1 : Int) - 131072) - ((T2 : Int) - 131072))
          (((H : Int) - 131072) - ((H : Int) - 131072))
          (((W : Int) - 131072) - ((W : Int) - 131072)) = (((T1 : Int) - (T2 : Int)) * ωT) % Q32_MOD := by
        unfold q32Phase; congr 1; grind
      rw [hsimp] at h0
      exact hne (hinj_coord ωT T1 T2 hωT hT1 hT2 h0)
    · intro T H1 H2 W hH1 hH2 hne heq
      rw [hhom, hhom] at heq
      have h0 : q32PhaseDiff (q32Phase ωT ωH ωW ((T : Int) - 131072) ((H1 : Int) - 131072) ((W : Int) - 131072))
                             (q32Phase ωT ωH ωW ((T : Int) - 131072) ((H2 : Int) - 131072) ((W : Int) - 131072)) = 0 := by
        rw [heq]; unfold q32PhaseDiff; simp
      rw [hhom] at h0
      have hsimp : q32Phase ωT ωH ωW (((T : Int) - 131072) - ((T : Int) - 131072))
          (((H1 : Int) - 131072) - ((H2 : Int) - 131072))
          (((W : Int) - 131072) - ((W : Int) - 131072)) = (((H1 : Int) - (H2 : Int)) * ωH) % Q32_MOD := by
        unfold q32Phase; congr 1; grind
      rw [hsimp] at h0
      exact hne (hinj_coord ωH H1 H2 hωH (by omega) (by omega) h0)
    · intro T H W1 W2 hW1 hW2 hne heq
      rw [hhom, hhom] at heq
      have h0 : q32PhaseDiff (q32Phase ωT ωH ωW ((T : Int) - 131072) ((H : Int) - 131072) ((W1 : Int) - 131072))
                             (q32Phase ωT ωH ωW ((T : Int) - 131072) ((H : Int) - 131072) ((W2 : Int) - 131072)) = 0 := by
        rw [heq]; unfold q32PhaseDiff; simp
      rw [hhom] at h0
      have hsimp : q32Phase ωT ωH ωW (((T : Int) - 131072) - ((T : Int) - 131072))
          (((H : Int) - 131072) - ((H : Int) - 131072))
          (((W1 : Int) - 131072) - ((W2 : Int) - 131072)) = (((W1 : Int) - (W2 : Int)) * ωW) % Q32_MOD := by
        unfold q32Phase; congr 1; grind
      rw [hsimp] at h0
      exact hne (hinj_coord ωW W1 W2 hωW (by omega) (by omega) h0)

end Mrope3dCoprime
