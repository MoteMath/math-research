/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FlashAttnBwdSignflip.RatOrder

/-!
# Theorems 1 & 2: Softmax-Jacobian Zero-Sum Conservation, Cancellation-Free Identity,
# and Peaked-Softmax `50.00%` Spurious Sign-Flip Phase Transition

Pure `Init` (zero Mathlib, zero `native_decide`) proofs.
-/

namespace FlashAttnBwdSignflip

/-! ### Theorem 1 Helpers -/

theorem softmaxGradStd_sum_eq {n : Nat} (p dP : Fin n → Rat) :
    finSum (fun j => softmaxGradStd p dP j) = softmaxD p dP * (1 - finSum p) := by
  unfold softmaxGradStd softmaxD dotProd
  have h1 : finSum (fun j => p j * (dP j - finSum (fun k => p k * dP k))) =
      finSum (fun j => p j * dP j - p j * finSum (fun k => p k * dP k)) := by
    apply finSum_congr
    intro j; grind
  rw [h1, finSum_sub, finSum_mul_right]
  grind

theorem softmaxGradCF_eq_expanded {n : Nat} (p dP : Fin n → Rat) (i : Fin n) :
    softmaxGradCF p dP i = p i * (finSum p * dP i - softmaxD p dP) := by
  unfold softmaxGradCF softmaxD dotProd
  have hsub : finSumExcept i (fun j => p j * (dP i - dP j)) =
      finSum (fun j => p j * (dP i - dP j)) := by
    have hsplit := finSum_split_at i (fun j => p j * (dP i - dP j))
    have hself : p i * (dP i - dP i) = 0 := by grind
    rw [hself, Rat.zero_add] at hsplit
    exact hsplit.symm
  rw [hsub]
  have hlin : finSum (fun j => p j * (dP i - dP j)) =
      finSum (fun j => p j * dP i - p j * dP j) := by
    apply finSum_congr
    intro j; grind
  rw [hlin, finSum_sub, finSum_mul_right]

/-- **Theorem 1** (`softmax_jacobian_zero_sum_and_cancellation_free_identity`):
    Universal exact algebraic theorem over `Rat` for any `p, dP : Fin n → Rat`:
    1. Exact zero-sum conservation `∑_j p_j (dP_j - D) = 0` on the simplex `∑_j p_j = 1`.
    2. Exact algebraic equivalence `softmaxGradStd p dP i = softmaxGradCF p dP i` for every index `i`
       (and specifically the top token `i = 0`).
    3. Unconditional shift-invariance of `softmaxGradCF` for ANY weights `pHat` (even off-simplex),
       contrasted with the exact off-simplex shift leakage `pHat i * (1 - ∑ pHat) * c` of `softmaxGradStd`. -/
theorem softmax_jacobian_zero_sum_and_cancellation_free_identity :
    (∀ (n : Nat) (p dP : Fin n → Rat), finSum p = 1 →
      finSum (fun j => softmaxGradStd p dP j) = 0) ∧
    (∀ (n : Nat) (p dP : Fin n → Rat) (i : Fin n), finSum p = 1 →
      softmaxGradStd p dP i = softmaxGradCF p dP i) ∧
    (∀ (n : Nat) (hn : 0 < n) (p dP : Fin n → Rat), finSum p = 1 →
      softmaxGradStd p dP ⟨0, hn⟩ = softmaxGradCF p dP ⟨0, hn⟩) ∧
    (∀ (n : Nat) (pHat dP : Fin n → Rat) (c : Rat) (i : Fin n),
      softmaxGradCF pHat (fun j => dP j + c) i = softmaxGradCF pHat dP i) ∧
    (∀ (n : Nat) (pHat dP : Fin n → Rat) (c : Rat) (i : Fin n),
      softmaxGradStd pHat (fun j => dP j + c) i =
        softmaxGradStd pHat dP i + pHat i * (1 - finSum pHat) * c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n p dP hsum
    rw [softmaxGradStd_sum_eq, hsum]
    grind
  · intro n p dP i hsum
    rw [softmaxGradCF_eq_expanded, hsum]
    unfold softmaxGradStd
    grind
  · intro n hn p dP hsum
    rw [softmaxGradCF_eq_expanded, hsum]
    unfold softmaxGradStd
    grind
  · intro n pHat dP c i
    unfold softmaxGradCF finSumExcept
    congr 1
    apply finSum_congr
    intro j
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, ite_false]
      grind
  · intro n pHat dP c i
    unfold softmaxGradStd softmaxD dotProd
    have hD : finSum (fun j => pHat j * (dP j + c)) =
        finSum (fun j => pHat j * dP j) + finSum pHat * c := by
      have hlin : finSum (fun j => pHat j * (dP j + c)) =
          finSum (fun j => pHat j * dP j + pHat j * c) := by
        apply finSum_congr
        intro j; grind
      rw [hlin, finSum_add, finSum_mul_right]
    rw [hD]
    grind

/-! ### Theorem 2 Helpers -/

theorem rneSnapsToOne_iff (m : Nat) (ε : Rat) :
    rneSnapsToOne m (1 - ε) ↔ ((0 : Rat) ≤ ε ∧ ε ≤ epsSnap m) := by
  unfold rneSnapsToOne epsSnap
  have h2 : (2 : Rat) * invPow2Rat (m + 2) = invPow2Rat (m + 1) := invPow2Rat_succ (m + 1)
  have hpos : (0 : Rat) < invPow2Rat (m + 2) := invPow2Rat_pos (m + 2)
  constructor
  · rintro ⟨⟨_, hle1⟩, hmid⟩
    refine ⟨?_, ?_⟩
    · apply rat_le_of_sub_nonneg
      have := rat_sub_nonneg hle1
      grind
    · apply rat_le_of_mul_pos_right (c := (2 : Rat)) (by decide)
      have h1 : (2 : Rat) * ε ≤ invPow2Rat (m + 1) := by
        apply rat_le_of_sub_nonneg
        have := rat_sub_nonneg hmid
        grind
      rw [Rat.mul_comm ε 2, Rat.mul_comm (invPow2Rat (m + 2)) 2, h2]
      exact h1
  · rintro ⟨h0, hle⟩
    have h2ε : (2 : Rat) * ε ≤ invPow2Rat (m + 1) := by
      rw [← h2]
      exact rat_mul_le_mul_of_nonneg_left hle (by decide)
    have hεle : ε ≤ invPow2Rat (m + 1) := by
      have h1 : ε ≤ (2 : Rat) * ε := by
        apply rat_le_of_sub_nonneg
        have : (2 : Rat) * ε - ε = ε := by grind
        rw [this]; exact h0
      exact Rat.le_trans h1 h2ε
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply rat_le_of_sub_nonneg
      have := rat_sub_nonneg hεle
      grind
    · apply rat_le_of_sub_nonneg
      have : (1 : Rat) - (1 - ε) = ε := by grind
      rw [this]; exact h0
    · apply rat_le_of_sub_nonneg
      have := rat_sub_nonneg h2ε
      grind

theorem epsSnap_values :
    epsSnap 1 = 1 / 8 ∧
    epsSnap 2 = 1 / 16 ∧
    epsSnap 3 = 1 / 32 ∧
    epsSnap 7 = 1 / 512 ∧
    epsSnap 10 = 1 / 4096 := by
  unfold epsSnap invPow2Rat pow2Rat
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h : (2 ^ (1 + 2) : Nat) = 8 := rfl; rw [h]; rfl
  · have h : (2 ^ (2 + 2) : Nat) = 16 := rfl; rw [h]; rfl
  · have h : (2 ^ (3 + 2) : Nat) = 32 := rfl; rw [h]; rfl
  · have h : (2 ^ (7 + 2) : Nat) = 512 := rfl; rw [h]; rfl
  · have h : (2 ^ (10 + 2) : Nat) = 4096 := rfl; rw [h]; rfl

theorem offsetGrad_eval_std_cf {n : Nat} (hn : 0 < n) (pHat : Fin n → Rat)
    (hp0 : pHat ⟨0, hn⟩ = 1) (c δ : Rat) :
    let i0 : Fin n := ⟨0, hn⟩
    let εHat := finSumExcept i0 pHat
    finSum pHat = 1 + εHat ∧
    softmaxGradStd pHat (offsetGrad hn c δ) i0 = εHat * (δ - c) ∧
    softmaxGradCF pHat (offsetGrad hn c δ) i0 = εHat * δ := by
  intro i0 εHat
  have hsum : finSum pHat = 1 + εHat := by
    rw [finSum_split_at i0 pHat, hp0]
  have hcf : softmaxGradCF pHat (offsetGrad hn c δ) i0 = εHat * δ := by
    unfold softmaxGradCF finSumExcept offsetGrad
    rw [hp0, Rat.one_mul]
    have hcongr :
        finSum (fun j : Fin n =>
          if j = i0 then (0 : Rat)
          else pHat j * ((if i0 = i0 then c else c - δ) - (if j = i0 then c else c - δ))) =
        finSum (fun j : Fin n => (if j = i0 then (0 : Rat) else pHat j) * δ) := by
      apply finSum_congr
      intro j
      by_cases hji : j = i0
      · simp [hji]
      · simp only [hji, ite_false, ite_true]
        grind
    rw [hcongr, finSum_mul_right]
    rfl
  have hstd : softmaxGradStd pHat (offsetGrad hn c δ) i0 = εHat * (δ - c) := by
    have hD : softmaxD pHat (offsetGrad hn c δ) = c + εHat * (c - δ) := by
      unfold softmaxD dotProd
      rw [finSum_split_at i0, hp0]
      unfold offsetGrad
      simp only [Rat.one_mul]
      have hite : (if i0 = i0 then c else c - δ) = c := by simp
      rw [hite]
      congr 1
      unfold finSumExcept
      have hcongr :
          finSum (fun j : Fin n =>
            if j = i0 then (0 : Rat) else pHat j * (if j = i0 then c else c - δ)) =
          finSum (fun j : Fin n => (if j = i0 then (0 : Rat) else pHat j) * (c - δ)) := by
        apply finSum_congr
        intro j
        by_cases hji : j = i0
        · simp [hji]
        · simp [hji]
      rw [hcongr, finSum_mul_right]
      rfl
    unfold softmaxGradStd
    rw [hp0, hD]
    unfold offsetGrad
    have hite : (if i0 = i0 then c else c - δ) = c := by simp
    rw [hite]
    grind
  exact ⟨hsum, hstd, hcf⟩

/-- **Theorem 2** (`peaked_softmax_half_spurious_signflip_threshold`):
    Universal exact IEEE-754 RNE theorem for `m`-bit mantissa formats
    (`U-E3M1`, `FP8-E5M2`, `FP8-E4M3`, `BF16`, `FP16`):
    1. `1 - ε` snaps to `1` under `m`-bit RNE iff `0 ≤ ε ≤ 2^{-(m+2)}`
       (`1/8`, `1/16`, `1/32`, `1/512`, `1/4096`).
    2. Whenever `pHat_0 = 1` and quantized tail mass `εHat = ∑_{j ≠ 0} pHat_j > 0`,
       `∑ pHat_j = 1 + εHat > 1`. For ANY constant-offset upstream gradient
       `dP_0 = c, dP_{j ≠ 0} = c - δ` (`δ ≠ 0`):
       - Standard `softmaxGradStd` equals `εHat * (δ - c)` and **STRICTLY FLIPS SIGN**
         relative to the true gradient `(1 - ε) ε δ` whenever `c` has the same sign as `δ`
         and `|c| > |δ|`.
       - Exact `50.00%` sign-flip symmetry: for EVERY `|c| > |δ|`, **EXACTLY ONE** of `+c`
         and `-c` flips the sign of `softmaxGradStd`.
       - Cancellation-free `softmaxGradCF` equals `εHat * δ`, is **100% invariant to `c`**,
         and **NEVER flips sign**.
    3. Universal `m`-bit 2-token concrete witness at `ε = 2^{-(m+2)}, dP = (1, 1/2)` proving
       `dS_0^{true} > 0`, `dS_0^{naive} = -2^{-(m+3)} < 0`, `dS_0^{cf} = +2^{-(m+3)} > 0`. -/
theorem peaked_softmax_half_spurious_signflip_threshold :
    (∀ (m : Nat) (ε : Rat), rneSnapsToOne m (1 - ε) ↔ ((0 : Rat) ≤ ε ∧ ε ≤ epsSnap m)) ∧
    (epsSnap 1 = 1 / 8 ∧ epsSnap 2 = 1 / 16 ∧ epsSnap 3 = 1 / 32 ∧
     epsSnap 7 = 1 / 512 ∧ epsSnap 10 = 1 / 4096) ∧
    (∀ (n : Nat) (hn : 0 < n) (pHat : Fin n → Rat) (ε c δ : Rat),
      0 < ε → ε < 1 → pHat ⟨0, hn⟩ = 1 →
      0 < finSumExcept ⟨0, hn⟩ pHat → δ ≠ 0 →
      let i0 : Fin n := ⟨0, hn⟩
      let εHat := finSumExcept i0 pHat
      let dS_true := (1 - ε) * ε * δ
      (finSum pHat = 1 + εHat ∧ 1 < finSum pHat) ∧
      (softmaxGradStd pHat (offsetGrad hn c δ) i0 = εHat * (δ - c)) ∧
      (softmaxGradCF pHat (offsetGrad hn c δ) i0 = εHat * δ) ∧
      (0 < softmaxGradCF pHat (offsetGrad hn c δ) i0 * dS_true) ∧
      (((0 < δ ∧ δ < c) ∨ (c < δ ∧ δ < 0)) →
        softmaxGradStd pHat (offsetGrad hn c δ) i0 * dS_true < 0) ∧
      (ratAbs δ < ratAbs c →
        (softmaxGradStd pHat (offsetGrad hn c δ) i0 * dS_true < 0 ∧
         0 < softmaxGradStd pHat (offsetGrad hn (-c) δ) i0 * dS_true) ∨
        (0 < softmaxGradStd pHat (offsetGrad hn c δ) i0 * dS_true ∧
         softmaxGradStd pHat (offsetGrad hn (-c) δ) i0 * dS_true < 0))) ∧
    (∀ m : Nat, 1 ≤ m →
      let ε := epsSnap m
      let pHat2 : Fin 2 → Rat := fun j => if j.val = 0 then 1 else ε
      let dP2 : Fin 2 → Rat := fun j => if j.val = 0 then 1 else 1 / 2
      rneSnapsToOne m (1 - ε) ∧
      0 < (1 - ε) * ε * (1 / 2 : Rat) ∧
      softmaxGradStd pHat2 dP2 ⟨0, by decide⟩ = -invPow2Rat (m + 3) ∧
      softmaxGradStd pHat2 dP2 ⟨0, by decide⟩ < 0 ∧
      softmaxGradCF pHat2 dP2 ⟨0, by decide⟩ = invPow2Rat (m + 3) ∧
      0 < softmaxGradCF pHat2 dP2 ⟨0, by decide⟩) := by
  refine ⟨rneSnapsToOne_iff, epsSnap_values, ?_, ?_⟩
  · intro n hn pHat ε c δ hε0 hε1 hp0 hεHat hδne
    dsimp only
    have heval := offsetGrad_eval_std_cf hn pHat hp0 c δ
    dsimp only at heval
    rcases heval with ⟨hsum, hstd, hcf⟩
    have hp0pos : (0 : Rat) < 1 - ε := rat_sub_pos hε1
    have hcoeff : (0 : Rat) < (1 - ε) * ε := rat_mul_pos hp0pos hε0
    refine ⟨⟨hsum, ?_⟩, hstd, hcf, ?_, ?_, ?_⟩
    · rw [hsum]
      apply rat_lt_of_sub_pos
      have : (1 : Rat) + finSumExcept ⟨0, hn⟩ pHat - 1 = finSumExcept ⟨0, hn⟩ pHat := by grind
      rw [this]; exact hεHat
    · rw [hcf]
      have hsq : (0 : Rat) < δ * δ := rat_sq_pos_of_ne_zero hδne
      have heq : finSumExcept ⟨0, hn⟩ pHat * δ * ((1 - ε) * ε * δ) =
          (finSumExcept ⟨0, hn⟩ pHat * ((1 - ε) * ε)) * (δ * δ) := by grind
      rw [heq]
      exact rat_mul_pos (rat_mul_pos hεHat hcoeff) hsq
    · intro hsame
      rw [hstd]
      have heq : finSumExcept ⟨0, hn⟩ pHat * (δ - c) * ((1 - ε) * ε * δ) =
          (finSumExcept ⟨0, hn⟩ pHat * ((1 - ε) * ε)) * ((δ - c) * δ) := by grind
      rw [heq]
      have hfactor : (δ - c) * δ < 0 := by
        cases hsame with
        | inl h =>
          have hneg : δ - c < 0 := by
            have := rat_sub_pos h.2
            have := rat_neg_of_pos this
            have eq2 : -(c - δ) = δ - c := by grind
            rw [← eq2]; exact this
          exact rat_mul_neg_of_neg_of_pos hneg h.1
        | inr h =>
          have hpos : (0 : Rat) < δ - c := rat_sub_pos h.1
          exact rat_mul_neg_of_pos_of_neg hpos h.2
      exact rat_mul_neg_of_pos_of_neg (rat_mul_pos hεHat hcoeff) hfactor
    · intro habs
      have hevalNeg := offsetGrad_eval_std_cf hn pHat hp0 (-c) δ
      dsimp only at hevalNeg
      have hstdNeg : softmaxGradStd pHat (offsetGrad hn (-c) δ) ⟨0, hn⟩ =
          finSumExcept ⟨0, hn⟩ pHat * (δ - (-c)) := hevalNeg.2.1
      rw [hstd, hstdNeg]
      have hprodPos : (0 : Rat) < finSumExcept ⟨0, hn⟩ pHat * ((1 - ε) * ε) :=
        rat_mul_pos hεHat hcoeff
      have h1eq : finSumExcept ⟨0, hn⟩ pHat * (δ - c) * ((1 - ε) * ε * δ) =
          (finSumExcept ⟨0, hn⟩ pHat * ((1 - ε) * ε)) * ((δ - c) * δ) := by grind
      have h2eq : finSumExcept ⟨0, hn⟩ pHat * (δ - (-c)) * ((1 - ε) * ε * δ) =
          (finSumExcept ⟨0, hn⟩ pHat * ((1 - ε) * ε)) * ((δ + c) * δ) := by grind
      rw [h1eq, h2eq]
      -- Case split on signs of δ and c
      cases Rat.le_total (a := (0 : Rat)) (b := δ) with
      | inl hδge =>
        have hδpos : (0 : Rat) < δ := Rat.lt_of_le_of_ne hδge (Ne.symm hδne)
        rw [ratAbs_of_nonneg hδge] at habs
        cases Rat.le_total (a := (0 : Rat)) (b := c) with
        | inl hcge =>
          rw [ratAbs_of_nonneg hcge] at habs
          left
          have hsub : δ - c < 0 := by
            have := rat_neg_of_pos (rat_sub_pos habs)
            have eq2 : -(c - δ) = δ - c := by grind
            rw [← eq2]; exact this
          have hadd : (0 : Rat) < δ + c := rat_add_pos_of_pos_of_nonneg hδpos hcge
          exact ⟨rat_mul_neg_of_pos_of_neg hprodPos (rat_mul_neg_of_neg_of_pos hsub hδpos),
                 rat_mul_pos hprodPos (rat_mul_pos hadd hδpos)⟩
        | inr hcle =>
          rw [ratAbs_of_nonpos hcle] at habs
          right
          have hsub : (0 : Rat) < δ - c := by
            have : (0 : Rat) ≤ -c := rat_neg_nonneg_of_nonpos hcle
            have := rat_add_pos_of_pos_of_nonneg hδpos this
            have eq2 : δ + -c = δ - c := by grind
            rw [← eq2]; exact this
          have hadd : δ + c < 0 := by
            have := rat_neg_of_pos (rat_sub_pos habs)
            have eq2 : -((-c) - δ) = δ + c := by grind
            rw [← eq2]; exact this
          exact ⟨rat_mul_pos hprodPos (rat_mul_pos hsub hδpos),
                 rat_mul_neg_of_pos_of_neg hprodPos (rat_mul_neg_of_neg_of_pos hadd hδpos)⟩
      | inr hδle =>
        have hδneg : δ < 0 := Rat.lt_of_le_of_ne hδle hδne
        rw [ratAbs_of_nonpos hδle] at habs
        cases Rat.le_total (a := (0 : Rat)) (b := c) with
        | inl hcge =>
          rw [ratAbs_of_nonneg hcge] at habs
          right
          have hsub : δ - c < 0 := by
            have h1 : -c ≤ 0 := by
              have := rat_sub_nonneg hcge
              grind
            have := rat_add_pos_of_pos_of_nonneg (rat_neg_pos_of_neg hδneg) hcge
            have h2 := rat_neg_of_pos this
            have eq2 : -(-δ + c) = δ - c := by grind
            rw [← eq2]; exact h2
          have hadd : (0 : Rat) < δ + c := by
            have := rat_sub_pos habs
            have eq2 : c - (-δ) = δ + c := by grind
            rw [← eq2]; exact this
          exact ⟨rat_mul_pos hprodPos (rat_mul_pos_of_neg_of_neg hsub hδneg),
                 rat_mul_neg_of_pos_of_neg hprodPos (rat_mul_neg_of_pos_of_neg hadd hδneg)⟩
        | inr hcle =>
          rw [ratAbs_of_nonpos hcle] at habs
          left
          have hsub : (0 : Rat) < δ - c := by
            have := rat_sub_pos habs
            have eq2 : (-c) - (-δ) = δ - c := by grind
            rw [← eq2]; exact this
          have hadd : δ + c < 0 := by
            have := rat_add_pos_of_pos_of_nonneg (rat_neg_pos_of_neg hδneg)
              (rat_neg_nonneg_of_nonpos hcle)
            have h2 := rat_neg_of_pos this
            have eq2 : -(-δ + -c) = δ + c := by grind
            rw [← eq2]; exact h2
          exact ⟨rat_mul_neg_of_pos_of_neg hprodPos (rat_mul_neg_of_pos_of_neg hsub hδneg),
                 rat_mul_pos hprodPos (rat_mul_pos_of_neg_of_neg hadd hδneg)⟩
  · intro m hm
    dsimp only
    have hεpos : (0 : Rat) < epsSnap m := invPow2Rat_pos (m + 2)
    have hεlt1 : epsSnap m < 1 := by
      unfold epsSnap invPow2Rat pow2Rat
      apply rat_div_lt_of_mul_lt (rat_natCast_pos (Nat.pow_pos (by decide)))
      rw [Rat.one_mul]
      have hpow : 1 < 2 ^ (m + 2) := by
        have h1 : 2 ^ 3 ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      exact rat_natCast_lt hpow
    have hhalf : epsSnap m * (1 / 2 : Rat) = invPow2Rat (m + 3) := by
      unfold epsSnap
      have h2 := invPow2Rat_succ (m + 2)
      have hdiv : invPow2Rat (m + 2) * (1 / 2 : Rat) = invPow2Rat (m + 3) := by
        rw [← h2]; grind
      exact hdiv
    have hstd2 : softmaxGradStd (fun j : Fin 2 => if j.val = 0 then (1 : Rat) else epsSnap m)
        (fun j : Fin 2 => if j.val = 0 then (1 : Rat) else 1 / 2) ⟨0, by decide⟩ =
        -invPow2Rat (m + 3) := by
      unfold softmaxGradStd softmaxD dotProd
      rw [finSum_two]
      simp only [ite_true]
      have hne : (1 : Nat) ≠ 0 := by decide
      simp only [hne, ite_false]
      rw [← hhalf]
      grind
    have hcf2 : softmaxGradCF (fun j : Fin 2 => if j.val = 0 then (1 : Rat) else epsSnap m)
        (fun j : Fin 2 => if j.val = 0 then (1 : Rat) else 1 / 2) ⟨0, by decide⟩ =
        invPow2Rat (m + 3) := by
      unfold softmaxGradCF finSumExcept
      rw [finSum_two]
      simp only [ite_true]
      have hne0 : (⟨1, by decide⟩ : Fin 2) ≠ ⟨0, by decide⟩ := by decide
      have hne : (1 : Nat) ≠ 0 := by decide
      simp only [hne0, hne, ite_false]
      rw [← hhalf]
      grind
    refine ⟨?_, ?_, hstd2, ?_, hcf2, ?_⟩
    · exact (rneSnapsToOne_iff m (epsSnap m)).mpr ⟨Rat.le_of_lt hεpos, Rat.le_refl⟩
    · exact rat_mul_pos (rat_mul_pos (rat_sub_pos hεlt1) hεpos)
        (rat_div_pos (by decide) (by decide))
    · rw [hstd2]
      exact rat_neg_of_pos (invPow2Rat_pos (m + 3))
    · rw [hcf2]
      exact invPow2Rat_pos (m + 3)

end FlashAttnBwdSignflip
