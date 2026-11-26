/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RopeQ32Coprime.Defs

/-!
# Pillar 1 & 3: Exact `Q32` Odd-Frequency Modular Phase Bijection & Zero-Drift Additivity

Proves Theorem 3 (`q32_modular_odd_dyadic_zero_drift_exact`) via Hensel lifting of the
multiplicative inverse of any odd `ω` modulo `2^b` (`b = 32` specialization included).
Zero Mathlib, zero `decide` on large moduli.
-/

namespace RopeQ32Coprime

/-! ### Hensel Lifting of Odd Multiplicative Inverse Modulo `2^b` -/

theorem odd_mul_inv_mod_pow2 (b omega : Nat) (hb : 1 ≤ b) (hodd : omega % 2 = 1) :
    ∃ u : Nat, u < 2 ^ b ∧ (omega * u) % (2 ^ b) = 1 := by
  induction b with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      refine ⟨1, by decide, ?_⟩
      simp [Nat.mul_one, hodd]
    | succ k' =>
      have hk : 1 ≤ k' + 1 := Nat.succ_le_succ (Nat.zero_le k')
      obtain ⟨u, hu_lt, hu_inv⟩ := ih hk
      let M := 2 ^ (k' + 1)
      have hM_def : M = 2 ^ (k' + 1) := rfl
      have hM_pos : 0 < M := Nat.pow_pos (by decide)
      have hM2 : 2 ^ (k' + 2) = 2 * M := by
        rw [hM_def, Nat.pow_succ, Nat.mul_comm]
      have hmod_cases : (omega * u) % (2 * M) = 1 ∨ (omega * u) % (2 * M) = 1 + M := by
        have hdm := Nat.div_add_mod (omega * u) (2 * M)
        have hlt := Nat.mod_lt (omega * u) (show 0 < 2 * M by omega)
        have hsub : ((omega * u) % (2 * M)) % M = 1 := by
          have : (omega * u) % M = ((omega * u) % (2 * M)) % M := by
            have h1 : (omega * u) % (2 * M) + 2 * M * ((omega * u) / (2 * M)) = omega * u := by
              omega
            have h2 : 2 * M * ((omega * u) / (2 * M)) = M * (2 * ((omega * u) / (2 * M))) := by
              rw [Nat.mul_comm 2 M, Nat.mul_assoc]
            conv => lhs; rw [← h1, h2, Nat.add_mul_mod_self_left]
          rw [← this, hM_def, hu_inv]
        have hdm_M := Nat.div_add_mod ((omega * u) % (2 * M)) M
        have hq_lt : ((omega * u) % (2 * M)) / M < 2 := by
          rw [Nat.div_lt_iff_lt_mul hM_pos]
          have h2M : 2 * M = M * 2 := Nat.mul_comm 2 M
          omega
        match hq : ((omega * u) % (2 * M)) / M with
        | 0 => left; rw [hq, Nat.mul_zero, Nat.zero_add, hsub] at hdm_M; exact hdm_M.symm
        | 1 => right; rw [hq, Nat.mul_one, hsub] at hdm_M; omega
        | _ + 2 => exfalso; rw [hq] at hq_lt; omega
      have hu_lt_M : u < M := hu_lt
      cases hmod_cases with
      | inl h1 =>
        refine ⟨u, ?_, ?_⟩
        · rw [hM2]; omega
        · rw [hM2]; exact h1
      | inr h2 =>
        refine ⟨u + M, ?_, ?_⟩
        · rw [hM2]; omega
        · rw [hM2]
          have hdist : omega * (u + M) = omega * u + omega * M := Nat.mul_add omega u M
          rw [hdist]
          have hodd_decomp : omega = 2 * (omega / 2) + 1 := by omega
          have homegaM : (omega * M) % (2 * M) = M := by
            conv => lhs; rw [hodd_decomp]
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
            have : (2 * (omega / 2 * M) + M) = M + (2 * M) * (omega / 2) := by
              have hcomm : 2 * (omega / 2 * M) = (2 * M) * (omega / 2) := by
                rw [Nat.mul_comm (omega / 2) M, ← Nat.mul_assoc]
              omega
            rw [this, Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt (by omega)
          rw [Nat.add_mod, h2, homegaM]
          have hsum : 1 + M + M = 1 + 2 * M * 1 := by omega
          rw [hsum, Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt (by omega)

/-! ### Universal `b`-Bit Bijection, Exact Period, Zero Collisions, and Relative Additivity -/

theorem modPhase_inj_on_range {b omega m₁ m₂ : Nat} (hb : 1 ≤ b) (hodd : omega % 2 = 1)
    (hm₁ : m₁ < 2 ^ b) (hm₂ : m₂ < 2 ^ b)
    (heq : modPhase b omega m₁ = modPhase b omega m₂) : m₁ = m₂ := by
  obtain ⟨u, _, hu⟩ := odd_mul_inv_mod_pow2 b omega hb hodd
  unfold modPhase at heq
  have hmul : (m₁ * omega * u) % (2 ^ b) = (m₂ * omega * u) % (2 ^ b) := by
    rw [Nat.mul_mod (m₁ * omega) u, heq, ← Nat.mul_mod (m₂ * omega) u]
  have hred : ∀ m : Nat, (m * omega * u) % (2 ^ b) = m % (2 ^ b) := by
    intro m
    rw [Nat.mul_assoc, Nat.mul_mod m (omega * u), hu, Nat.mul_one, Nat.mod_mod]
  rw [hred m₁, hred m₂, Nat.mod_eq_of_lt hm₁, Nat.mod_eq_of_lt hm₂] at hmul
  exact hmul

theorem modPhase_surj_on_range {b omega y : Nat} (hb : 1 ≤ b) (hodd : omega % 2 = 1)
    (hy : y < 2 ^ b) :
    ∃ m : Nat, m < 2 ^ b ∧ modPhase b omega m = y := by
  obtain ⟨u, _, hu⟩ := odd_mul_inv_mod_pow2 b omega hb hodd
  refine ⟨(y * u) % (2 ^ b), Nat.mod_lt _ (Nat.pow_pos (by decide)), ?_⟩
  unfold modPhase
  rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_comm u omega, Nat.mul_mod y (omega * u),
      hu, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hy]

theorem modPhase_periodic (b omega m : Nat) :
    modPhase b omega (m + 2 ^ b) = modPhase b omega m := by
  unfold modPhase
  rw [Nat.add_mul, Nat.add_mul_mod_self_left]

theorem modPhase_min_period {b omega m d : Nat} (hb : 1 ≤ b) (hodd : omega % 2 = 1)
    (hd_pos : 0 < d) (hd_lt : d < 2 ^ b) :
    modPhase b omega (m + d) ≠ modPhase b omega m := by
  intro heq
  obtain ⟨u, _, hu⟩ := odd_mul_inv_mod_pow2 b omega hb hodd
  unfold modPhase at heq
  have hmul : ((m + d) * omega * u) % (2 ^ b) = (m * omega * u) % (2 ^ b) := by
    rw [Nat.mul_mod ((m + d) * omega) u, heq, ← Nat.mul_mod (m * omega) u]
  have hred : ∀ x : Nat, (x * omega * u) % (2 ^ b) = x % (2 ^ b) := by
    intro x
    rw [Nat.mul_assoc, Nat.mul_mod x (omega * u), hu, Nat.mul_one, Nat.mod_mod]
  rw [hred (m + d), hred m] at hmul
  let M := 2 ^ b
  have hM_def : M = 2 ^ b := rfl
  have hM_pos : 0 < M := Nat.pow_pos (by decide)
  have hmul' : (m + d) % M = m % M := hmul
  have hadd : (m % M + d) % M = m % M := by
    rw [← Nat.mod_add_mod] at hmul'
    exact hmul'
  have hm_lt : m % M < M := Nat.mod_lt m hM_pos
  have hd_lt' : d < M := hd_lt
  by_cases hsum : m % M + d < M
  · rw [Nat.mod_eq_of_lt hsum] at hadd
    omega
  · have hsub : m % M + d - M < M := by omega
    have hmod : (m % M + d) % M = m % M + d - M := by
      have h1 : m % M + d = (m % M + d - M) + M * 1 := by omega
      conv => lhs; rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsub]
    rw [hmod] at hadd
    omega

theorem modPhase_no_consecutive_collision {b omega : Nat} (hb : 1 ≤ b) (hodd : omega % 2 = 1)
    (m : Nat) :
    modPhase b omega (m + 1) ≠ modPhase b omega m := by
  have h1lt : 1 < 2 ^ b := by
    have : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb
    omega
  exact modPhase_min_period hb hodd (by decide) h1lt

theorem modPhase_add_rel {b omega m n : Nat} (hmn : m ≤ n) :
    (modPhase b omega m + modPhase b omega (n - m)) % (2 ^ b) = modPhase b omega n := by
  unfold modPhase
  rw [← Nat.add_mod, ← Nat.add_mul, Nat.add_sub_of_le hmn]

theorem modPhase_sub_rel {b omega m n : Nat} (hmn : m ≤ n) :
    (modPhase b omega n + 2 ^ b - modPhase b omega m) % (2 ^ b) = modPhase b omega (n - m) := by
  have hadd := modPhase_add_rel (b := b) (omega := omega) hmn
  let M := 2 ^ b
  have hM_pos : 0 < M := Nat.pow_pos (by decide)
  have ha_lt : modPhase b omega m < M := Nat.mod_lt _ hM_pos
  have hb_lt : modPhase b omega (n - m) < M := Nat.mod_lt _ hM_pos
  have hc_lt : modPhase b omega n < M := Nat.mod_lt _ hM_pos
  have hadd' : (modPhase b omega m + modPhase b omega (n - m)) % M = modPhase b omega n := hadd
  change (modPhase b omega n + M - modPhase b omega m) % M = modPhase b omega (n - m)
  by_cases hsum : modPhase b omega m + modPhase b omega (n - m) < M
  · rw [Nat.mod_eq_of_lt hsum] at hadd'
    have h1 : modPhase b omega n + M - modPhase b omega m =
        modPhase b omega (n - m) + M * 1 := by omega
    rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb_lt]
  · have hsub : modPhase b omega m + modPhase b omega (n - m) - M < M := by omega
    have hmod : (modPhase b omega m + modPhase b omega (n - m)) % M =
        modPhase b omega m + modPhase b omega (n - m) - M := by
      have h1 : modPhase b omega m + modPhase b omega (n - m) =
          (modPhase b omega m + modPhase b omega (n - m) - M) + M * 1 := by omega
      conv => lhs; rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsub]
    rw [hmod] at hadd'
    have h1 : modPhase b omega n + M - modPhase b omega m = modPhase b omega (n - m) := by omega
    rw [h1, Nat.mod_eq_of_lt hb_lt]

/-! ### Headline Theorem 3: `q32_modular_odd_dyadic_zero_drift_exact` -/

theorem q32_modular_odd_dyadic_zero_drift_exact :
    (∀ (omega : Nat), omega % 2 = 1 →
      Function.Injective (q32PhaseFin omega) ∧
      Function.Surjective (q32PhaseFin omega) ∧
      (∀ m : Nat, q32Phase omega (m + q32Mod) = q32Phase omega m) ∧
      (∀ m d : Nat, 0 < d → d < q32Mod → q32Phase omega (m + d) ≠ q32Phase omega m) ∧
      (∀ m : Nat, q32Phase omega (m + 1) ≠ q32Phase omega m) ∧
      (∀ m n : Nat, m ≤ n →
        (q32Phase omega m + q32Phase omega (n - m)) % q32Mod = q32Phase omega n ∧
        (q32Phase omega n + q32Mod - q32Phase omega m) % q32Mod = q32Phase omega (n - m))) ∧
    (∀ (b omega : Nat), 1 ≤ b → omega % 2 = 1 →
      (∃ u : Nat, u < 2 ^ b ∧ (omega * u) % (2 ^ b) = 1) ∧
      (∀ m : Nat, modPhase b omega (m + 1) ≠ modPhase b omega m)) := by
  constructor
  · intro omega hodd
    have hb : (1 : Nat) ≤ 32 := by decide
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      apply Fin.ext
      exact modPhase_inj_on_range hb hodd a.isLt b.isLt (congrArg Fin.val hab)
    · intro y
      obtain ⟨m, hm_lt, hm_eq⟩ := modPhase_surj_on_range hb hodd y.isLt
      exact ⟨⟨m, hm_lt⟩, Fin.ext hm_eq⟩
    · intro m
      exact modPhase_periodic 32 omega m
    · intro m d hd_pos hd_lt
      exact modPhase_min_period hb hodd hd_pos hd_lt
    · intro m
      exact modPhase_no_consecutive_collision hb hodd m
    · intro m n hmn
      exact ⟨modPhase_add_rel hmn, modPhase_sub_rel hmn⟩
  · intro b omega hb hodd
    exact ⟨odd_mul_inv_mod_pow2 b omega hb hodd,
           fun m => modPhase_no_consecutive_collision hb hodd m⟩

end RopeQ32Coprime
