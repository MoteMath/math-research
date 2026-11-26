/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FlashAttnBwdSignflip.RatOrder

/-!
# Theorems 3 & 4: Direct `P · dP` Midpoint DC-Leakage Law &
# FlashAttention `D_i = dO · fl(O)` Orthogonal Divergence Amplification

Pure `Init` (zero Mathlib, zero `native_decide`) proofs.
-/

namespace FlashAttnBwdSignflip

/-! ### Theorem 3 Helpers -/

theorem directMidpointLeakage_pos (m : Nat) : (0 : Rat) < directMidpointLeakage m := by
  unfold directMidpointLeakage
  exact rat_div_pos (by decide) (rat_add_pos (pow2Rat_pos (m + 1)) (by decide))

theorem directMidpointLeakage_values :
    directMidpointLeakage 1 = 1 / 5 ∧
    directMidpointLeakage 2 = 1 / 9 ∧
    directMidpointLeakage 3 = 1 / 17 ∧
    directMidpointLeakage 7 = 1 / 257 ∧
    directMidpointLeakage 10 = 1 / 2049 := by
  unfold directMidpointLeakage pow2Rat
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h : ((2 ^ (1 + 1) : Nat) : Rat) + 1 = 5 := by
      have : (2 ^ (1 + 1) : Nat) = 4 := rfl; rw [this]; grind
    rw [h]
  · have h : ((2 ^ (2 + 1) : Nat) : Rat) + 1 = 9 := by
      have : (2 ^ (2 + 1) : Nat) = 8 := rfl; rw [this]; grind
    rw [h]
  · have h : ((2 ^ (3 + 1) : Nat) : Rat) + 1 = 17 := by
      have : (2 ^ (3 + 1) : Nat) = 16 := rfl; rw [this]; grind
    rw [h]
  · have h : ((2 ^ (7 + 1) : Nat) : Rat) + 1 = 257 := by
      have : (2 ^ (7 + 1) : Nat) = 256 := rfl; rw [this]; grind
    rw [h]
  · have h : ((2 ^ (10 + 1) : Nat) : Rat) + 1 = 2049 := by
      have : (2 ^ (10 + 1) : Nat) = 2048 := rfl; rw [this]; grind
    rw [h]

theorem softmaxGradWithD_sum_eq {n : Nat} (p dP : Fin n → Rat) (dHat : Rat)
    (hsum : finSum p = 1) :
    finSum (fun j => softmaxGradWithD p dP dHat j) = softmaxD p dP - dHat := by
  unfold softmaxGradWithD softmaxD dotProd
  have hlin : finSum (fun j => p j * (dP j - dHat)) =
      finSum (fun j => p j * dP j - p j * dHat) := by
    apply finSum_congr
    intro j; grind
  rw [hlin, finSum_sub, finSum_mul_right, hsum, Rat.one_mul]

theorem invPow2_div_one_add_invPow2 (m : Nat) :
    invPow2Rat (m + 1) / (1 + invPow2Rat (m + 1)) = directMidpointLeakage m := by
  unfold directMidpointLeakage invPow2Rat
  have hp : pow2Rat (m + 1) ≠ 0 := pow2Rat_ne_zero (m + 1)
  have hpos : (0 : Rat) < pow2Rat (m + 1) := pow2Rat_pos (m + 1)
  have hd1 : (1 : Rat) + 1 / pow2Rat (m + 1) ≠ 0 :=
    Rat.ne_of_gt (rat_add_pos (by decide) (rat_div_pos (by decide) hpos))
  have hd2 : pow2Rat (m + 1) + 1 ≠ 0 :=
    Rat.ne_of_gt (rat_add_pos hpos (by decide))
  apply (rat_div_eq_iff hd1).mpr
  apply (rat_div_eq_iff hp).mpr
  have hmul : (1 / (pow2Rat (m + 1) + 1)) * (1 + 1 / pow2Rat (m + 1)) * pow2Rat (m + 1) =
      (1 / (pow2Rat (m + 1) + 1)) * (pow2Rat (m + 1) + (1 / pow2Rat (m + 1)) * pow2Rat (m + 1)) := by
    grind
  rw [hmul, rat_div_mul_cancel hp, rat_div_mul_cancel hd2]

/-- **Theorem 3** (`direct_p_dp_midpoint_dc_leakage_exact`):
    Universal exact rational theorem proving the direct `D = fl(P · dP)` midpoint zero-sum
    DC-leakage law `Z_direct^* = 1 / (2^{m+1} + 1)` (`1/5` MXFP4, `1/9` FP8-E5M2,
    `1/17` FP8-E4M3, `1/257` BF16, `1/2049` FP16) and `Z_jac^* = 1` (100% of true Jacobian L1 norm),
    together with the universal relative-error upper bound `Z_direct ≤ 2^{-(m+1)}`. -/
theorem direct_p_dp_midpoint_dc_leakage_exact :
    (directMidpointLeakage 1 = 1 / 5 ∧
     directMidpointLeakage 2 = 1 / 9 ∧
     directMidpointLeakage 3 = 1 / 17 ∧
     directMidpointLeakage 7 = 1 / 257 ∧
     directMidpointLeakage 10 = 1 / 2049) ∧
    (∀ (m : Nat) (s : Rat), 0 < s →
      let p : Fin 2 → Rat := fun _ => 1 / 2
      let dP : Fin 2 → Rat := fun j => if j.val = 0 then s * (1 + invPow2Rat m) else s
      let dTrue := softmaxD p dP
      finSum p = 1 ∧
      dTrue = s * (1 + invPow2Rat (m + 1)) ∧
      rneRoundsToLowerEven m s dTrue ∧
      finSum (fun j => softmaxGradWithD p dP s j) = s * invPow2Rat (m + 1) ∧
      hadamardL1 p dP = s * (1 + invPow2Rat (m + 1)) ∧
      ratAbs (finSum (fun j => softmaxGradWithD p dP s j)) / hadamardL1 p dP =
        directMidpointLeakage m ∧
      finSum (fun j => ratAbs (softmaxGradStd p dP j)) = s * invPow2Rat (m + 1) ∧
      ratAbs (finSum (fun j => softmaxGradWithD p dP s j)) /
        finSum (fun j => ratAbs (softmaxGradStd p dP j)) = 1) ∧
    (∀ (n m : Nat) (p dP : Fin n → Rat) (dHat : Rat),
      finSum p = 1 →
      ratAbs (dHat - softmaxD p dP) ≤ invPow2Rat (m + 1) * ratAbs (softmaxD p dP) →
      ratAbs (finSum (fun j => softmaxGradWithD p dP dHat j)) ≤
        invPow2Rat (m + 1) * hadamardL1 p dP) := by
  refine ⟨directMidpointLeakage_values, ?_, ?_⟩
  · intro m s hs
    dsimp only
    have hpSum : finSum (fun _ : Fin 2 => (1 / 2 : Rat)) = 1 := by
      rw [finSum_two]; grind
    have h2m : (2 : Rat) * invPow2Rat (m + 1) = invPow2Rat m := invPow2Rat_succ m
    have h2m2 : (2 : Rat) * invPow2Rat (m + 2) = invPow2Rat (m + 1) := invPow2Rat_succ (m + 1)
    have huPos : (0 : Rat) < invPow2Rat (m + 1) := invPow2Rat_pos (m + 1)
    have hu2Pos : (0 : Rat) < invPow2Rat (m + 2) := invPow2Rat_pos (m + 2)
    have hdTrue :
        softmaxD (fun _ : Fin 2 => (1 / 2 : Rat))
          (fun j : Fin 2 => if j.val = 0 then s * (1 + invPow2Rat m) else s) =
        s * (1 + invPow2Rat (m + 1)) := by
      unfold softmaxD dotProd
      rw [finSum_two]
      have hne : (1 : Nat) ≠ 0 := by decide
      simp only [ite_true, hne, ite_false]
      rw [← h2m]
      grind
    have hrne : rneRoundsToLowerEven m s (s * (1 + invPow2Rat (m + 1))) := by
      unfold rneRoundsToLowerEven
      refine ⟨?_, ?_⟩
      · apply rat_le_of_sub_nonneg
        have hsub : s * (1 + invPow2Rat (m + 1)) - s = s * invPow2Rat (m + 1) := by grind
        rw [hsub]
        exact Rat.mul_nonneg (Rat.le_of_lt hs) (Rat.le_of_lt huPos)
      · have heq : s * (1 + invPow2Rat (m + 1)) - s =
            s * (1 + invPow2Rat m) - s * (1 + invPow2Rat (m + 1)) := by
          rw [← h2m]; grind
        rw [heq]
        exact Rat.le_refl
    have hsumHat :
        finSum (fun j : Fin 2 =>
          softmaxGradWithD (fun _ : Fin 2 => (1 / 2 : Rat))
            (fun j : Fin 2 => if j.val = 0 then s * (1 + invPow2Rat m) else s) s j) =
        s * invPow2Rat (m + 1) := by
      rw [softmaxGradWithD_sum_eq _ _ s hpSum, hdTrue]
      grind
    have hL1 :
        hadamardL1 (fun _ : Fin 2 => (1 / 2 : Rat))
          (fun j : Fin 2 => if j.val = 0 then s * (1 + invPow2Rat m) else s) =
        s * (1 + invPow2Rat (m + 1)) := by
      unfold hadamardL1
      rw [finSum_two]
      have hne : (1 : Nat) ≠ 0 := by decide
      simp only [ite_true, hne, ite_false]
      have h0nn : (0 : Rat) ≤ (1 / 2 : Rat) * (s * (1 + invPow2Rat m)) :=
        Rat.mul_nonneg (rat_div_nonneg (by decide) (by decide))
          (Rat.mul_nonneg (Rat.le_of_lt hs)
            (rat_add_nonneg (by decide) (Rat.le_of_lt (invPow2Rat_pos m))))
      have h1nn : (0 : Rat) ≤ (1 / 2 : Rat) * s :=
        Rat.mul_nonneg (rat_div_nonneg (by decide) (by decide)) (Rat.le_of_lt hs)
      rw [ratAbs_of_nonneg h0nn, ratAbs_of_nonneg h1nn, ← h2m]
      grind
    have hsumHatPos : (0 : Rat) < s * invPow2Rat (m + 1) := rat_mul_pos hs huPos
    have hL1Pos : (0 : Rat) < s * (1 + invPow2Rat (m + 1)) :=
      rat_mul_pos hs (rat_add_pos (by decide) huPos)
    have hZ :
        ratAbs (s * invPow2Rat (m + 1)) / (s * (1 + invPow2Rat (m + 1))) =
        directMidpointLeakage m := by
      rw [ratAbs_of_nonneg (Rat.le_of_lt hsumHatPos)]
      rw [← invPow2_div_one_add_invPow2 m]
      have hsne : s ≠ 0 := Rat.ne_of_gt hs
      have hd1ne : (1 : Rat) + invPow2Rat (m + 1) ≠ 0 :=
        Rat.ne_of_gt (rat_add_pos (by decide) huPos)
      have hd2ne : s * (1 + invPow2Rat (m + 1)) ≠ 0 := Rat.ne_of_gt hL1Pos
      apply (rat_div_eq_iff hd2ne).mpr
      have hmul : (invPow2Rat (m + 1) / (1 + invPow2Rat (m + 1))) * (s * (1 + invPow2Rat (m + 1))) =
          s * ((invPow2Rat (m + 1) / (1 + invPow2Rat (m + 1))) * (1 + invPow2Rat (m + 1))) := by
        grind
      rw [hmul, rat_div_mul_cancel hd1ne]
    have hJacL1 :
        finSum (fun j : Fin 2 =>
          ratAbs (softmaxGradStd (fun _ : Fin 2 => (1 / 2 : Rat))
            (fun j : Fin 2 => if j.val = 0 then s * (1 + invPow2Rat m) else s) j)) =
        s * invPow2Rat (m + 1) := by
      rw [finSum_two]
      unfold softmaxGradStd
      rw [hdTrue]
      have hne : (1 : Nat) ≠ 0 := by decide
      simp only [ite_true, hne, ite_false]
      have h0eq : (1 / 2 : Rat) * (s * (1 + invPow2Rat m) - s * (1 + invPow2Rat (m + 1))) =
          s * invPow2Rat (m + 2) := by
        rw [← h2m, ← h2m2]; grind
      have h1eq : (1 / 2 : Rat) * (s - s * (1 + invPow2Rat (m + 1))) =
          -(s * invPow2Rat (m + 2)) := by
        rw [← h2m2]; grind
      rw [h0eq, h1eq, ratAbs_neg,
          ratAbs_of_nonneg (Rat.le_of_lt (rat_mul_pos hs hu2Pos)), ← h2m2]
      grind
    have hZjac :
        ratAbs (s * invPow2Rat (m + 1)) / (s * invPow2Rat (m + 1)) = 1 := by
      rw [ratAbs_of_nonneg (Rat.le_of_lt hsumHatPos)]
      apply (rat_div_eq_iff (Rat.ne_of_gt hsumHatPos)).mpr
      grind
    refine ⟨hpSum, hdTrue, ?_, hsumHat, hL1, ?_, hJacL1, ?_⟩
    · rw [hdTrue]; exact hrne
    · rw [hsumHat, hL1]; exact hZ
    · rw [hsumHat, hJacL1]; exact hZjac
  · intro n m p dP dHat hsum hrel
    rw [softmaxGradWithD_sum_eq p dP dHat hsum]
    have hneg : ratAbs (softmaxD p dP - dHat) = ratAbs (dHat - softmaxD p dP) := by
      have heq : softmaxD p dP - dHat = -(dHat - softmaxD p dP) := by grind
      rw [heq, ratAbs_neg]
    rw [hneg]
    have htri : ratAbs (softmaxD p dP) ≤ hadamardL1 p dP := by
      unfold softmaxD dotProd hadamardL1
      exact ratAbs_finSum_le (fun j => p j * dP j)
    exact Rat.le_trans hrel
      (rat_mul_le_mul_of_nonneg_left htri (Rat.le_of_lt (invPow2Rat_pos (m + 1))))

/-! ### Theorem 4 Helpers -/

theorem dotProd_sub_right {d : Nat} (a b c : Fin d → Rat) :
    dotProd a (fun k => b k - c k) = dotProd a b - dotProd a c := by
  unfold dotProd
  have hlin : finSum (fun k => a k * (b k - c k)) =
      finSum (fun k => a k * b k - a k * c k) := by
    apply finSum_congr
    intro k; grind
  rw [hlin, finSum_sub]

/-- **Theorem 4** (`flashattn_do_o_orthogonal_divergence_amplification`):
    1. Exact algebraic law for FlashAttention `D_i^{FA} = dO · fl(O)` under forward error
       `δO = oHat - O`: whenever `dO · O = P · dP` and `∑_j p_j = 1`,
       - Exact zero-sum leakage equals `-⟨dO, δO⟩`.
       - Under `|δO_k| ≤ u_fwd |O_k|`, the leakage obeys both the exact L1 Hadamard
         amplification bound `Z_FA ≤ u_fwd · κ_orth` (`κ_orth = ||dO ⊙ O||_1 / ||P ⊙ dP||_1`)
         and the exact L2 Cauchy-Schwarz squared bound
         `(dO · δO)^2 ≤ u_fwd^2 · ||dO||_2^2 · ||O||_2^2`.
    2. Explicit parametric rational family (`d_head = 2, n = 2`) with exact RNE midpoint
       rounding `fl(O_0) = 1`, exact forward output `O = P V`, and exact orthogonal
       cancellation `dO · O = P · dP = 0` achieving `Z_FA(m, ε_v) = Z_direct^*(m) / ε_v`,
       proving arbitrarily large blowup, strictly `> 1000×` worse than direct `P · dP`
       at `ε_v = 1/1001`, and exact `symbolic_proofs.json` witnesses at `ε_v = 1/256`
       (`256/257` BF16, `256/17` FP8-E4M3, `256/9` FP8-E5M2, `256/5` MXFP4). -/
theorem flashattn_do_o_orthogonal_divergence_amplification :
    (∀ (n d : Nat) (p dP : Fin n → Rat) (dO O oHat : Fin d → Rat) (uFwd : Rat),
      finSum p = 1 →
      dotProd dO O = softmaxD p dP →
      0 ≤ uFwd →
      (∀ k : Fin d, ratAbs (oHat k - O k) ≤ uFwd * ratAbs (O k)) →
      let δO : Fin d → Rat := fun k => oHat k - O k
      let dFA := dotProd dO oHat
      finSum (fun j => softmaxGradWithD p dP dFA j) = -dotProd dO δO ∧
      ratAbs (finSum (fun j => softmaxGradWithD p dP dFA j)) ≤ uFwd * hadamardL1 dO O ∧
      (0 < hadamardL1 p dP →
        ratAbs (finSum (fun j => softmaxGradWithD p dP dFA j)) / hadamardL1 p dP ≤
          uFwd * (hadamardL1 dO O / hadamardL1 p dP)) ∧
      dotProd dO δO * dotProd dO δO ≤ (uFwd * uFwd) * l2NormSq dO * l2NormSq O) ∧
    (∀ (m : Nat) (ε_v : Rat), 0 < ε_v →
      let u := invPow2Rat (m + 1)
      let p : Fin 2 → Rat := fun _ => 1 / 2
      let O : Fin 2 → Rat := fun k => if k.val = 0 then 1 + u else 1
      let oHat : Fin 2 → Rat := fun _ => 1
      let dO : Fin 2 → Rat := fun k => if k.val = 0 then 1 else -(1 + u)
      let V0 : Fin 2 → Rat := fun k => if k.val = 0 then 1 + u else 1 + ε_v
      let V1 : Fin 2 → Rat := fun k => if k.val = 0 then 1 + u else 1 - ε_v
      let dP : Fin 2 → Rat := fun j => if j.val = 0 then dotProd dO V0 else dotProd dO V1
      rneRoundsToLowerEven m 1 (O ⟨0, by decide⟩) ∧
      (∀ k : Fin 2, (1 / 2 : Rat) * V0 k + (1 / 2 : Rat) * V1 k = O k) ∧
      dotProd dO O = 0 ∧
      softmaxD p dP = 0 ∧
      dotProd dO oHat = -u ∧
      ratAbs (finSum (fun j => softmaxGradWithD p dP (dotProd dO oHat) j)) / hadamardL1 p dP =
        directMidpointLeakage m / ε_v) ∧
    (∀ (m : Nat) (M : Rat), 0 < M →
      directMidpointLeakage m / (directMidpointLeakage m / M) = M) ∧
    (∀ m : Nat,
      directMidpointLeakage m / (1 / 1001 : Rat) = 1001 * directMidpointLeakage m ∧
      1000 * directMidpointLeakage m < directMidpointLeakage m / (1 / 1001 : Rat)) ∧
    (directMidpointLeakage 7 / (1 / 256 : Rat) = 256 / 257 ∧
     directMidpointLeakage 3 / (1 / 256 : Rat) = 256 / 17 ∧
     directMidpointLeakage 2 / (1 / 256 : Rat) = 256 / 9 ∧
     directMidpointLeakage 1 / (1 / 256 : Rat) = 256 / 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n d p dP dO O oHat uFwd hsum hcons hu hδ
    dsimp only
    have hleak : finSum (fun j => softmaxGradWithD p dP (dotProd dO oHat) j) =
        -dotProd dO (fun k => oHat k - O k) := by
      rw [softmaxGradWithD_sum_eq p dP (dotProd dO oHat) hsum, ← hcons, dotProd_sub_right]
      grind
    have hL1bound : ratAbs (finSum (fun j => softmaxGradWithD p dP (dotProd dO oHat) j)) ≤
        uFwd * hadamardL1 dO O := by
      rw [hleak, ratAbs_neg]
      unfold dotProd hadamardL1
      have h1 := ratAbs_finSum_le (fun k => dO k * (oHat k - O k))
      have h2 : finSum (fun k => ratAbs (dO k * (oHat k - O k))) ≤
          finSum (fun k => uFwd * ratAbs (dO k * O k)) := by
        apply finSum_le_finSum
        intro k
        rw [ratAbs_mul, ratAbs_mul]
        have hmul := rat_mul_le_mul_of_nonneg_left (hδ k) (ratAbs_nonneg (dO k))
        have heq : ratAbs (dO k) * (uFwd * ratAbs (O k)) =
            uFwd * (ratAbs (dO k) * ratAbs (O k)) := by grind
        rw [← heq]
        exact hmul
      rw [finSum_mul_left] at h2
      exact Rat.le_trans h1 h2
    have hL2bound :
        dotProd dO (fun k => oHat k - O k) * dotProd dO (fun k => oHat k - O k) ≤
        (uFwd * uFwd) * l2NormSq dO * l2NormSq O := by
      have hcs := cauchy_schwarz_finSum dO (fun k => oHat k - O k)
      have hδSq : l2NormSq (fun k => oHat k - O k) ≤ (uFwd * uFwd) * l2NormSq O := by
        unfold l2NormSq
        rw [← finSum_mul_left]
        apply finSum_le_finSum
        intro k
        have hle := hδ k
        have ha : (0 : Rat) ≤ ratAbs (oHat k - O k) := ratAbs_nonneg _
        have hb : (0 : Rat) ≤ uFwd * ratAbs (O k) := Rat.mul_nonneg hu (ratAbs_nonneg _)
        have hsq : ratAbs (oHat k - O k) * ratAbs (oHat k - O k) ≤
            (uFwd * ratAbs (O k)) * (uFwd * ratAbs (O k)) :=
          Rat.le_trans (rat_mul_le_mul_of_nonneg_left hle ha)
            (rat_mul_le_mul_of_nonneg_right hle hb)
        rw [ratAbs_sq] at hsq
        have hrhs : (uFwd * ratAbs (O k)) * (uFwd * ratAbs (O k)) =
            (uFwd * uFwd) * (O k * O k) := by
          have : (uFwd * ratAbs (O k)) * (uFwd * ratAbs (O k)) =
              (uFwd * uFwd) * (ratAbs (O k) * ratAbs (O k)) := by grind
          rw [this, ratAbs_sq]
        rw [hrhs] at hsq
        exact hsq
      have hl2nn : (0 : Rat) ≤ l2NormSq dO := finSum_nonneg (fun k => rat_sq_nonneg _)
      have hmul := rat_mul_le_mul_of_nonneg_left hδSq hl2nn
      have hrearr : l2NormSq dO * ((uFwd * uFwd) * l2NormSq O) =
          (uFwd * uFwd) * l2NormSq dO * l2NormSq O := by grind
      rw [hrearr] at hmul
      exact Rat.le_trans hcs hmul
    refine ⟨hleak, hL1bound, ?_, hL2bound⟩
    · intro hL1pos
      apply rat_div_le_of_mul_le hL1pos
      have hrearr : uFwd * (hadamardL1 dO O / hadamardL1 p dP) * hadamardL1 p dP =
          uFwd * ((hadamardL1 dO O / hadamardL1 p dP) * hadamardL1 p dP) := by grind
      rw [hrearr, rat_div_mul_cancel (Rat.ne_of_gt hL1pos)]
      exact hL1bound
  · intro m ε_v hε
    dsimp only
    have h2m : (2 : Rat) * invPow2Rat (m + 1) = invPow2Rat m := invPow2Rat_succ m
    have huPos : (0 : Rat) < invPow2Rat (m + 1) := invPow2Rat_pos (m + 1)
    have hne : (1 : Nat) ≠ 0 := by decide
    have hrne : rneRoundsToLowerEven m 1 (1 + invPow2Rat (m + 1)) := by
      unfold rneRoundsToLowerEven
      refine ⟨?_, ?_⟩
      · apply rat_le_of_sub_nonneg
        have : (1 : Rat) + invPow2Rat (m + 1) - 1 = invPow2Rat (m + 1) := by grind
        rw [this]; exact Rat.le_of_lt huPos
      · have heq : (1 : Rat) + invPow2Rat (m + 1) - 1 =
            1 * (1 + invPow2Rat m) - (1 + invPow2Rat (m + 1)) := by
          rw [← h2m]; grind
        rw [heq]; exact Rat.le_refl
    have hPV : ∀ k : Fin 2,
        (1 / 2 : Rat) * (if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 + ε_v) +
        (1 / 2 : Rat) * (if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 - ε_v) =
        (if k.val = 0 then 1 + invPow2Rat (m + 1) else 1) := by
      intro k
      by_cases hk : k.val = 0
      · simp only [hk, ite_true]; grind
      · simp only [hk, ite_false]; grind
    have hdO_O : dotProd
        (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
        (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1) = 0 := by
      unfold dotProd
      rw [finSum_two]
      simp only [ite_true, hne, ite_false]
      grind
    have hdP0 : dotProd
        (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
        (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 + ε_v) =
        -((1 + invPow2Rat (m + 1)) * ε_v) := by
      unfold dotProd
      rw [finSum_two]
      simp only [ite_true, hne, ite_false]
      grind
    have hdP1 : dotProd
        (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
        (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 - ε_v) =
        (1 + invPow2Rat (m + 1)) * ε_v := by
      unfold dotProd
      rw [finSum_two]
      simp only [ite_true, hne, ite_false]
      grind
    have hpSum : finSum (fun _ : Fin 2 => (1 / 2 : Rat)) = 1 := by
      rw [finSum_two]; grind
    have hdTrue : softmaxD (fun _ : Fin 2 => (1 / 2 : Rat))
        (fun j : Fin 2 =>
          if j.val = 0 then
            dotProd (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
              (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 + ε_v)
          else
            dotProd (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
              (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 - ε_v)) = 0 := by
      change finSum (fun j : Fin 2 =>
        (1 / 2 : Rat) *
          (if j.val = 0 then
            dotProd (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
              (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 + ε_v)
          else
            dotProd (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
              (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 - ε_v))) = 0
      rw [finSum_two]
      simp only [ite_true, hne, ite_false]
      rw [hdP0, hdP1]
      grind
    have hdFA : dotProd
        (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
        (fun _ : Fin 2 => (1 : Rat)) = -invPow2Rat (m + 1) := by
      unfold dotProd
      rw [finSum_two]
      simp only [ite_true, hne, ite_false]
      grind
    have hL1 : hadamardL1 (fun _ : Fin 2 => (1 / 2 : Rat))
        (fun j : Fin 2 =>
          if j.val = 0 then
            dotProd (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
              (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 + ε_v)
          else
            dotProd (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
              (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 - ε_v)) =
        (1 + invPow2Rat (m + 1)) * ε_v := by
      unfold hadamardL1
      rw [finSum_two]
      simp only [ite_true, hne, ite_false]
      rw [hdP0, hdP1]
      have hpos : (0 : Rat) ≤ (1 / 2 : Rat) * ((1 + invPow2Rat (m + 1)) * ε_v) :=
        Rat.mul_nonneg (rat_div_nonneg (by decide) (by decide))
          (Rat.mul_nonneg (rat_add_nonneg (by decide) (Rat.le_of_lt huPos)) (Rat.le_of_lt hε))
      have hnegEq : (1 / 2 : Rat) * -((1 + invPow2Rat (m + 1)) * ε_v) =
          -((1 / 2 : Rat) * ((1 + invPow2Rat (m + 1)) * ε_v)) := by grind
      rw [hnegEq, ratAbs_neg, ratAbs_of_nonneg hpos]
      grind
    have hZFA :
        ratAbs (finSum (fun j : Fin 2 =>
          softmaxGradWithD (fun _ : Fin 2 => (1 / 2 : Rat))
            (fun j : Fin 2 =>
              if j.val = 0 then
                dotProd (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
                  (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 + ε_v)
              else
                dotProd (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
                  (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 - ε_v))
            (dotProd
              (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
              (fun _ : Fin 2 => (1 : Rat))) j)) /
        hadamardL1 (fun _ : Fin 2 => (1 / 2 : Rat))
          (fun j : Fin 2 =>
            if j.val = 0 then
              dotProd (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
                (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 + ε_v)
            else
              dotProd (fun k : Fin 2 => if k.val = 0 then (1 : Rat) else -(1 + invPow2Rat (m + 1)))
                (fun k : Fin 2 => if k.val = 0 then 1 + invPow2Rat (m + 1) else 1 - ε_v)) =
        directMidpointLeakage m / ε_v := by
      rw [softmaxGradWithD_sum_eq _ _ _ hpSum, hdTrue, hdFA, hL1]
      have h0sub : (0 : Rat) - -invPow2Rat (m + 1) = invPow2Rat (m + 1) := by grind
      rw [h0sub, ratAbs_of_nonneg (Rat.le_of_lt huPos), ← invPow2_div_one_add_invPow2 m]
      have hd1ne : (1 : Rat) + invPow2Rat (m + 1) ≠ 0 :=
        Rat.ne_of_gt (rat_add_pos (by decide) huPos)
      have hεne : ε_v ≠ 0 := Rat.ne_of_gt hε
      have hprodNe : (1 + invPow2Rat (m + 1)) * ε_v ≠ 0 :=
        Rat.ne_of_gt (rat_mul_pos (rat_add_pos (by decide) huPos) hε)
      apply (rat_div_eq_iff hprodNe).mpr
      have hrearr :
          invPow2Rat (m + 1) / (1 + invPow2Rat (m + 1)) / ε_v * ((1 + invPow2Rat (m + 1)) * ε_v) =
          ((invPow2Rat (m + 1) / (1 + invPow2Rat (m + 1)) / ε_v) * ε_v) * (1 + invPow2Rat (m + 1)) := by
        grind
      rw [hrearr, rat_div_mul_cancel hεne, rat_div_mul_cancel hd1ne]
    exact ⟨by simp only [ite_true]; exact hrne, hPV, hdO_O, hdTrue, hdFA, hZFA⟩
  · intro m M hM
    have hZpos : (0 : Rat) < directMidpointLeakage m := directMidpointLeakage_pos m
    have hZne : directMidpointLeakage m ≠ 0 := Rat.ne_of_gt hZpos
    have hMne : M ≠ 0 := Rat.ne_of_gt hM
    have hDne : directMidpointLeakage m / M ≠ 0 := Rat.ne_of_gt (rat_div_pos hZpos hM)
    apply (rat_div_eq_iff hDne).mpr
    rw [rat_mul_div_cancel hMne]
  · intro m
    have hdiv : directMidpointLeakage m / (1 / 1001 : Rat) = 1001 * directMidpointLeakage m := by
      have hne : (1 / 1001 : Rat) ≠ 0 := Rat.ne_of_gt (rat_div_pos (by decide) (by decide))
      apply (rat_div_eq_iff hne).mpr
      have h1001 : (1001 : Rat) ≠ 0 := by decide
      have hrearr : 1001 * directMidpointLeakage m * (1 / 1001 : Rat) =
          directMidpointLeakage m * ((1 / 1001 : Rat) * 1001) := by grind
      rw [hrearr, rat_div_mul_cancel h1001, Rat.mul_one]
    refine ⟨hdiv, ?_⟩
    rw [hdiv]
    exact rat_mul_lt_mul_of_pos_right (by decide) (directMidpointLeakage_pos m)
  · rcases directMidpointLeakage_values with ⟨h1, h2, h3, h7, _⟩
    have h256 : ∀ a : Rat, (1 / a) / (1 / 256 : Rat) = 256 / a := by
      intro a
      have hne : (1 / 256 : Rat) ≠ 0 := Rat.ne_of_gt (rat_div_pos (by decide) (by decide))
      apply (rat_div_eq_iff hne).mpr
      have h256ne : (256 : Rat) ≠ 0 := by decide
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      have hrearr : 256 * a⁻¹ * (1 * (256 : Rat)⁻¹) = 1 * a⁻¹ * (256 * (256 : Rat)⁻¹) := by grind
      rw [hrearr, Rat.mul_inv_cancel (256 : Rat) h256ne, Rat.mul_one]
    rw [h7, h3, h2, h1]
    exact ⟨h256 257, h256 17, h256 9, h256 5⟩

end FlashAttnBwdSignflip
