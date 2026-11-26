/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VcacheIprXorvdc.IprPhaseTransition

/-!
# Theorems 4 & 5: Rank-1 Attention Sink IPR Crossover & Rank-1 Split WHT Orthogonality

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
4. `rank1_attention_sink_ipr_crossover_exact`:
   - Exact simplex & closed-form `IPR(α, L) = α^2 + (1 - α)^2 / (L - 1)` for `L ≥ 2`.
   - Exact sink-dominance phase flip: `α ∈ [3/4, 1] → IPR(α, L) > 9/16` and `N_eff(α, L) < 16/9 < 2`
     for every `L ≥ 2` (flipping the phase back to RNE regardless of context length).
   - High-precision sink exemption (`e_0 = 0`) leaves only the bulk error scaled by `(1 - α)`
     over uniform bulk weights with restored `N_eff = L - 1`.
5. `rank1_split_wht_orthogonality_and_output_inversion`:
   - Universal Sylvester Walsh–Hadamard orthogonality `H_{2^m}^T H_{2^m} = 2^m I_{2^m}` for all `m`.
   - Exact commutation of attention linearity with `H`, single output-side inverse `H^T / d`
     (zero per-token cost), Rank-1 mean-split invariance, and inter-token dynamic-range elimination.
-/

namespace VcacheIprXorvdc

/-! ### Theorem 4 Helpers: Rank-1 Attention Sink -/

theorem sinkWeights_sum_and_ipr {L : Nat} (hL : 2 ≤ L) (alpha : Rat) :
    finSum (sinkWeights L alpha) = 1 ∧
    ipr (sinkWeights L alpha) = alpha * alpha + (1 - alpha) * (1 - alpha) / ((L - 1 : Nat) : Rat) := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, L = m + 1 := ⟨L - 1, by omega⟩
  have hm : 0 < m := by omega
  have hmne : (m : Rat) ≠ 0 := rat_natCast_ne_zero hm
  have hsum : finSum (sinkWeights (m + 1) alpha) = 1 := by
    rw [finSum_split_zero]
    have h0 : sinkWeights (m + 1) alpha ⟨0, Nat.zero_lt_succ m⟩ = alpha := by
      simp [sinkWeights]
    have hrest : finSum (fun j : Fin m => sinkWeights (m + 1) alpha ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) =
        finSum (fun _ : Fin m => (1 - alpha) / (m : Rat)) := by
      apply finSum_congr
      intro j
      simp [sinkWeights]
    rw [h0, hrest, finSum_const]
    grind
  have hipr : ipr (sinkWeights (m + 1) alpha) =
      alpha * alpha + (1 - alpha) * (1 - alpha) / (m : Rat) := by
    unfold ipr
    rw [finSum_split_zero]
    have h0 : sinkWeights (m + 1) alpha ⟨0, Nat.zero_lt_succ m⟩ *
        sinkWeights (m + 1) alpha ⟨0, Nat.zero_lt_succ m⟩ = alpha * alpha := by
      simp [sinkWeights]
    have hrest : finSum (fun j : Fin m =>
        sinkWeights (m + 1) alpha ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ *
        sinkWeights (m + 1) alpha ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) =
        finSum (fun _ : Fin m => ((1 - alpha) / (m : Rat)) * ((1 - alpha) / (m : Rat))) := by
      apply finSum_congr
      intro j
      simp [sinkWeights]
    rw [h0, hrest, finSum_const]
    grind
  simpa using And.intro hsum hipr

theorem rank1_attention_sink_ipr_crossover_exact :
    (∀ (L : Nat) (alpha : Rat), 2 ≤ L → (0 : Rat) ≤ alpha → alpha ≤ 1 →
      (∀ j : Fin L, (0 : Rat) ≤ sinkWeights L alpha j) ∧
      finSum (sinkWeights L alpha) = 1 ∧
      ipr (sinkWeights L alpha) =
        alpha * alpha + (1 - alpha) * (1 - alpha) / ((L - 1 : Nat) : Rat)) ∧
    (∀ (L : Nat) (alpha : Rat), 2 ≤ L → (3 / 4 : Rat) ≤ alpha → alpha ≤ 1 →
      (9 / 16 : Rat) < ipr (sinkWeights L alpha) ∧
      neff (sinkWeights L alpha) < 16 / 9 ∧
      neff (sinkWeights L alpha) < 2) ∧
    (∀ (L : Nat) (alpha : Rat) (e : Fin L → Rat) (hL : 2 ≤ L),
      e ⟨0, by omega⟩ = 0 →
      finSum (fun j : Fin L => sinkWeights L alpha j * e j) =
        (1 - alpha) * finSum (fun k : Fin (L - 1) =>
          uniformWeights (L - 1) k * e ⟨k.val + 1, by omega⟩) ∧
      finSum (uniformWeights (L - 1)) = 1 ∧
      ipr (uniformWeights (L - 1)) = 1 / ((L - 1 : Nat) : Rat) ∧
      neff (uniformWeights (L - 1)) = ((L - 1 : Nat) : Rat)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L alpha hL ha0 ha1
    have hsi := sinkWeights_sum_and_ipr hL alpha
    refine ⟨?_, hsi.1, hsi.2⟩
    intro j
    unfold sinkWeights
    by_cases hj : j.val = 0
    · simp [hj, ha0]
    · simp only [hj, ↓reduceIte]
      exact rat_div_nonneg (rat_sub_nonneg ha1) (rat_natCast_pos (by omega))
  · intro L alpha hL ha34 _ha1
    have hsi := sinkWeights_sum_and_ipr hL alpha
    have hLm1_pos : (0 : Rat) < ((L - 1 : Nat) : Rat) := rat_natCast_pos (by omega)
    have hipr_gt : (9 / 16 : Rat) < ipr (sinkWeights L alpha) := by
      rw [hsi.2]
      by_cases heq : alpha = 3 / 4
      · subst heq
        have htail : (0 : Rat) < (1 - 3 / 4 : Rat) * (1 - 3 / 4) / ((L - 1 : Nat) : Rat) :=
          rat_div_pos (by grind) hLm1_pos
        have h916 : (3 / 4 : Rat) * (3 / 4) = 9 / 16 := by grind
        rw [h916]
        grind
      · have hgt : (3 / 4 : Rat) < alpha := Rat.lt_of_le_of_ne ha34 (Ne.symm heq)
        have ha_pos : (0 : Rat) < alpha := by grind
        have hmul1 : (3 / 4 : Rat) * (3 / 4) < (3 / 4) * alpha :=
          rat_mul_lt_mul_of_pos_left hgt (by grind)
        have hmul2 : (3 / 4 : Rat) * alpha < alpha * alpha :=
          rat_mul_lt_mul_of_pos_right hgt ha_pos
        have hsq : (9 / 16 : Rat) < alpha * alpha := by grind
        have htail : (0 : Rat) ≤ (1 - alpha) * (1 - alpha) / ((L - 1 : Nat) : Rat) :=
          rat_div_nonneg (rat_sq_nonneg (1 - alpha)) hLm1_pos
        grind
    have hipr_pos : (0 : Rat) < ipr (sinkWeights L alpha) := by grind
    have hneff_lt : neff (sinkWeights L alpha) < 16 / 9 := by
      unfold neff
      rw [rat_div_lt_iff hipr_pos]
      have hmul := rat_mul_lt_mul_of_pos_left hipr_gt (show (0 : Rat) < 16 / 9 by grind)
      grind
    exact ⟨hipr_gt, hneff_lt, by grind⟩
  · intro L alpha e hL he0
    obtain ⟨m, rfl⟩ : ∃ m : Nat, L = m + 1 := ⟨L - 1, by omega⟩
    have hm : 0 < m := by omega
    have hu := uniformWeights_ipr_neff hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [finSum_split_zero]
      have h0 : sinkWeights (m + 1) alpha ⟨0, Nat.zero_lt_succ m⟩ * e ⟨0, Nat.zero_lt_succ m⟩ = 0 := by
        rw [he0]; grind
      rw [h0]
      have hrest : finSum (fun k : Fin m =>
          sinkWeights (m + 1) alpha ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ *
          e ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) =
          (1 - alpha) * finSum (fun k : Fin m =>
            uniformWeights m k * e ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) := by
        rw [← finSum_mul_left]
        apply finSum_congr
        intro k
        simp only [sinkWeights, uniformWeights, Nat.add_sub_cancel]
        have hne : k.val + 1 ≠ 0 := by omega
        simp only [hne, ↓reduceIte]
        grind
      rw [hrest, Rat.zero_add]
      rfl
    · simpa using hu.1
    · simpa using hu.2.1
    · simpa using hu.2.2

/-! ### Theorem 5 Helpers: Sylvester WHT Orthogonality & Rank-1 Split Output Inversion -/

theorem finSum_cast {m n : Nat} (h : m = n) (f : Fin m → Rat) :
    finSum f = finSum (fun i : Fin n => f ⟨i.val, h ▸ i.isLt⟩) := by
  subst h
  rfl

theorem whtMat_isScaledOrthogonal (m : Nat) : isScaledOrthogonal (whtMat m) := by
  induction m with
  | zero =>
    intro a b
    have ha : a.val = 0 := by omega
    have hb : b.val = 0 := by omega
    have hab : a = b := Fin.ext (by omega)
    subst hab
    simp [finSum, finSumAux, whtMat]
    grind
  | succ k ih =>
    intro a b
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hsplit : finSum (fun i : Fin (2 ^ (k + 1)) => whtMat (k + 1) i a * whtMat (k + 1) i b) =
        finSum (fun i : Fin (2 ^ k) =>
          whtMat (k + 1) ⟨i.val, by omega⟩ a * whtMat (k + 1) ⟨i.val, by omega⟩ b) +
        finSum (fun i : Fin (2 ^ k) =>
          whtMat (k + 1) ⟨2 ^ k + i.val, by omega⟩ a * whtMat (k + 1) ⟨2 ^ k + i.val, by omega⟩ b) := by
      rw [finSum_cast hpow, finSum_append]
    rw [hsplit]
    let a0 : Fin (2 ^ k) := ⟨a.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
    let b0 : Fin (2 ^ k) := ⟨b.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
    have htop : finSum (fun i : Fin (2 ^ k) =>
        whtMat (k + 1) ⟨i.val, by omega⟩ a * whtMat (k + 1) ⟨i.val, by omega⟩ b) =
        finSum (fun i : Fin (2 ^ k) => whtMat k i a0 * whtMat k i b0) := by
      apply finSum_congr
      intro i
      simp only [whtMat, i.isLt, true_or, ↓reduceIte, Nat.mod_eq_of_lt]
      grind
    have hbot_term : ∀ i : Fin (2 ^ k),
        whtMat (k + 1) ⟨2 ^ k + i.val, by omega⟩ a * whtMat (k + 1) ⟨2 ^ k + i.val, by omega⟩ b =
        ((if a.val < 2 ^ k then (1 : Rat) else -1) * (if b.val < 2 ^ k then (1 : Rat) else -1)) *
        (whtMat k i a0 * whtMat k i b0) := by
      intro i
      have hge : ¬ (2 ^ k + i.val < 2 ^ k) := by omega
      have hmod : (2 ^ k + i.val) % 2 ^ k = i.val := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt i.isLt]
      have hfin : (⟨(2 ^ k + i.val) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩ : Fin (2 ^ k)) = i :=
        Fin.ext hmod
      simp only [whtMat, hge, false_or, hfin]
      by_cases ha : a.val < 2 ^ k <;> by_cases hb : b.val < 2 ^ k <;> simp [ha, hb] <;> grind
    rw [htop, finSum_congr hbot_term, finSum_mul_left, ih a0 b0]
    by_cases ha : a.val < 2 ^ k <;> by_cases hb : b.val < 2 ^ k
    · have hab_iff : a = b ↔ a0 = b0 := by
        constructor
        · intro h; subst h; rfl
        · intro h
          have hv : a.val % 2 ^ k = b.val % 2 ^ k := congrArg Fin.val h
          rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
          exact Fin.ext hv
      by_cases h : a = b
      · have h0 : a0 = b0 := hab_iff.mp h
        simp only [hb, h, h0, ↓reduceIte]
        rw [hpow, Rat.natCast_add]
        grind
      · have h0 : a0 ≠ b0 := fun hh => h (hab_iff.mpr hh)
        simp only [ha, hb, h, h0, ↓reduceIte]
        grind
    · have hne : a ≠ b := by
        intro h; subst h; exact hb ha
      simp only [ha, hb, hne, ↓reduceIte]
      grind
    · have hne : a ≠ b := by
        intro h; subst h; exact ha hb
      simp only [ha, hb, hne, ↓reduceIte]
      grind
    · have hab_iff : a = b ↔ a0 = b0 := by
        constructor
        · intro h; subst h; rfl
        · intro h
          have hv : a.val % 2 ^ k = b.val % 2 ^ k := congrArg Fin.val h
          have ha_mod : a.val % 2 ^ k = a.val - 2 ^ k := by
            have ha_sub : 2 ^ k + (a.val - 2 ^ k) = a.val := by omega
            have h1 : (2 ^ k + (a.val - 2 ^ k)) % 2 ^ k = a.val - 2 ^ k := by
              rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            rwa [ha_sub] at h1
          have hb_mod : b.val % 2 ^ k = b.val - 2 ^ k := by
            have hb_sub : 2 ^ k + (b.val - 2 ^ k) = b.val := by omega
            have h1 : (2 ^ k + (b.val - 2 ^ k)) % 2 ^ k = b.val - 2 ^ k := by
              rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            rwa [hb_sub] at h1
          rw [ha_mod, hb_mod] at hv
          exact Fin.ext (by omega)
      by_cases h : a = b
      · have h0 : a0 = b0 := hab_iff.mp h
        simp only [hb, h, h0, ↓reduceIte]
        rw [hpow, Rat.natCast_add]
        grind
      · have h0 : a0 ≠ b0 := fun hh => h (hab_iff.mpr hh)
        simp only [ha, hb, h, h0, ↓reduceIte]
        grind

theorem attnOut_comm_matVecMul {L d : Nat} (p : Fin L → Rat) (r : Fin L → Fin d → Rat)
    (H : Fin d → Fin d → Rat) (i : Fin d) :
    attnOut p (fun j => matVecMul H (r j)) i = matVecMul H (attnOut p r) i := by
  unfold attnOut matVecMul
  have h1 : finSum (fun j => p j * finSum (fun c => H i c * r j c)) =
      finSum (fun j => finSum (fun c => p j * (H i c * r j c))) := by
    apply finSum_congr; intro j; rw [finSum_mul_left]
  rw [h1, finSum_comm]
  apply finSum_congr
  intro c
  rw [← finSum_mul_left]
  apply finSum_congr
  intro j
  grind

theorem scaledOrthogonal_left_inv {d : Nat} (hd : 0 < d) (H : Fin d → Fin d → Rat)
    (hH : isScaledOrthogonal H) (v : Fin d → Rat) (c : Fin d) :
    (1 / (d : Rat)) * matVecMul (matTranspose H) (matVecMul H v) c = v c := by
  unfold matVecMul matTranspose
  have h1 : finSum (fun i => H i c * finSum (fun b => H i b * v b)) =
      finSum (fun i => finSum (fun b => H i c * (H i b * v b))) := by
    apply finSum_congr; intro i; rw [finSum_mul_left]
  rw [h1, finSum_comm]
  have h2 : finSum (fun b => finSum (fun i => H i c * (H i b * v b))) =
      finSum (fun b => if b = c then (d : Rat) * v c else 0) := by
    apply finSum_congr
    intro b
    have h3 : finSum (fun i => H i c * (H i b * v b)) =
        finSum (fun i => H i c * H i b) * v b := by
      rw [← finSum_mul_right]
      apply finSum_congr; intro i; grind
    rw [h3, hH c b]
    by_cases hbc : b = c
    · subst hbc; simp
    · have hcb : c ≠ b := fun h => hbc h.symm
      simp [hbc, hcb]
  rw [h2, finSum_single]
  have hdne : (d : Rat) ≠ 0 := rat_natCast_ne_zero hd
  grind

theorem rank1_split_wht_orthogonality_and_output_inversion :
    (∀ m : Nat, isScaledOrthogonal (whtMat m)) ∧
    (∀ (L d : Nat) (p : Fin L → Rat) (r : Fin L → Fin d → Rat) (H : Fin d → Fin d → Rat) (i : Fin d),
      attnOut p (fun j => matVecMul H (r j)) i = matVecMul H (attnOut p r) i) ∧
    (∀ (L d : Nat) (p : Fin L → Rat) (r : Fin L → Fin d → Rat) (H : Fin d → Fin d → Rat) (c : Fin d),
      0 < d → isScaledOrthogonal H →
      (1 / (d : Rat)) * matVecMul (matTranspose H) (attnOut p (fun j => matVecMul H (r j))) c =
        attnOut p r c) ∧
    (∀ (L d : Nat) (p : Fin L → Rat) (mu : Fin d → Rat) (r : Fin L → Fin d → Rat)
      (H : Fin d → Fin d → Rat) (c : Fin d),
      0 < d → finSum p = 1 → isScaledOrthogonal H →
      attnOut p (fun j k => mu k + r j k) c =
        mu c + (1 / (d : Rat)) * matVecMul (matTranspose H) (attnOut p (fun j => matVecMul H (r j))) c) ∧
    (∀ (mu r rho K : Rat), (0 : Rat) < rho → (0 : Rat) ≤ K →
      (ratAbs r ≤ rho → ratAbs ((mu + r) - mu) ≤ rho) ∧
      (mu = K * rho → r = rho → ratAbs (mu + r) = (K + 1) * rho ∧ ratAbs r = rho)) := by
  refine ⟨whtMat_isScaledOrthogonal, ?_, ?_, ?_, ?_⟩
  · intro L d p r H i
    exact attnOut_comm_matVecMul p r H i
  · intro L d p r H c hd hH
    have hcomm : attnOut p (fun j => matVecMul H (r j)) = matVecMul H (attnOut p r) := by
      funext i
      exact attnOut_comm_matVecMul p r H i
    rw [hcomm]
    exact scaledOrthogonal_left_inv hd H hH (attnOut p r) c
  · intro L d p mu r H c hd hsum hH
    have hsplit : attnOut p (fun j k => mu k + r j k) c = mu c + attnOut p r c := by
      unfold attnOut
      have h1 : finSum (fun j => p j * (mu c + r j c)) =
          finSum (fun j => p j * mu c + p j * r j c) := by
        apply finSum_congr; intro j; grind
      rw [h1, finSum_add, finSum_mul_right, hsum]
      grind
    have hcomm : attnOut p (fun j => matVecMul H (r j)) = matVecMul H (attnOut p r) := by
      funext i
      exact attnOut_comm_matVecMul p r H i
    rw [hsplit, hcomm, scaledOrthogonal_left_inv hd H hH (attnOut p r) c]
  · intro mu r rho K hrho hK
    refine ⟨?_, ?_⟩
    · intro hr
      have eq : (mu + r) - mu = r := by grind
      rw [eq]; exact hr
    · intro hmu hr
      rw [hmu, hr]
      have h1 : (0 : Rat) ≤ K * rho + rho := by
        have hk1 : (0 : Rat) ≤ K + 1 := by grind
        have hmul := Rat.mul_nonneg hk1 (Rat.le_of_lt hrho)
        grind
      have h2 : (0 : Rat) ≤ rho := Rat.le_of_lt hrho
      unfold ratAbs
      simp only [h1, h2, ↓reduceIte]
      grind

end VcacheIprXorvdc
