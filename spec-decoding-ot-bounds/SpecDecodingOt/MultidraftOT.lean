/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpecDecodingOt.RatHelpers

/-!
# Theorems 1 & 2: Exact Multi-Draft Speculative Decoding OT Gaps & Cyclic Madow Refutation

Pure-`Init` Lean 4 proofs over `Rat` (zero Mathlib):
1. `multidraft_corr_vs_iid_exact_gaps`:
   Universal additive gap `((K - 1) / K)^K` and multiplicative gap `K^K / (K^K - (K - 1)^K)`
   for ALL `K ≥ 1`, ALL `V : Nat`, ALL probability distributions `p, q : Fin V → Rat`, and
   ALL subsets `S : Fin V → Bool`, plus exact attainment witness for every `K ≥ 1`.
2. `cyclic_madow_optimality_refutation_exact`:
   Exact rational counterexamples at `K = 2, V = 4` showing that both default-order Cyclic Madow
   (`1/2 < 3/4 < 1`) and oracle descending-`p/q`-sorted Cyclic Madow (`17/20 < 91/100 < 1`)
   strictly fail to reach the correlated OT ceiling and can even underperform i.i.d. OT.
-/

namespace SpecDecodingOt

/-! ## Geometric Sum Helper for Concavity Secant Bound -/

private def geomSum (u : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => geomSum u n + ratPow u n

private theorem one_sub_ratPow_eq (u : Rat) (n : Nat) :
    1 - ratPow u n = (1 - u) * geomSum u n := by
  induction n with
  | zero =>
    simp only [ratPow, geomSum]
    grind
  | succ k ih =>
    simp only [ratPow, geomSum]
    have hmul : (1 - u) * (geomSum u k + ratPow u k) =
        (1 - u) * geomSum u k + (1 - u) * ratPow u k := by grind
    rw [hmul, ← ih]
    grind

private theorem geomSum_mono {u v : Rat} (hu : 0 ≤ u) (huv : u ≤ v) (n : Nat) :
    geomSum u n ≤ geomSum v n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [geomSum]
    exact rat_add_le_add ih (ratPow_mono hu huv k)

private theorem alphaCorr_le_one {K V : Nat} (p q : Fin V → Rat) (hp : isProbDist p) :
    alphaCorr K p q ≤ 1 := by
  unfold alphaCorr
  have hle : sumRat (fun i => min (p i) ((K : Rat) * q i)) ≤ sumRat p := by
    apply sumRat_le_sumRat
    intro i
    exact rat_min_le_left _ _
  rw [hp.2] at hle
  exact hle

private theorem alphaCorr_le_split {K V : Nat} (p q : Fin V → Rat) (S : Fin V → Bool) :
    alphaCorr K p q ≤
      sumRat (fun i => if S i then 0 else p i) +
      (K : Rat) * sumRat (fun i => if S i then q i else 0) := by
  unfold alphaCorr
  rw [← sumRat_mul_left]
  rw [← sumRat_add]
  apply sumRat_le_sumRat
  intro i
  cases hS : S i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hz : (K : Rat) * 0 = 0 := by grind
    rw [hz]
    have hadd : p i + 0 = p i := by grind
    rw [hadd]
    exact rat_min_le_left _ _
  | true =>
    simp only [↓reduceIte]
    have hadd : 0 + (K : Rat) * q i = (K : Rat) * q i := by grind
    rw [hadd]
    exact rat_min_le_right _ _

private theorem sumRat_subset_bounds {V : Nat} (f : Fin V → Rat) (hf : isProbDist f)
    (S : Fin V → Bool) :
    0 ≤ sumRat (fun i => if S i then f i else 0) ∧
    sumRat (fun i => if S i then f i else 0) ≤ 1 ∧
    0 ≤ sumRat (fun i => if S i then 0 else f i) := by
  have h1 : 0 ≤ sumRat (fun i => if S i then f i else 0) := by
    apply sumRat_nonneg
    intro i
    cases S i
    · exact Rat.le_refl
    · exact hf.1 i
  have h2 : 0 ≤ sumRat (fun i => if S i then 0 else f i) := by
    apply sumRat_nonneg
    intro i
    cases S i
    · exact hf.1 i
    · exact Rat.le_refl
  have hsplit := sumRat_split_bool f S
  rw [hf.2] at hsplit
  have h3 : sumRat (fun i => if S i then f i else 0) ≤ 1 := by
    apply rat_le_of_sub_nonneg
    have hEq : 1 - sumRat (fun i => if S i then f i else 0) =
        sumRat (fun i => if S i then 0 else f i) := by grind
    rw [hEq]
    exact h2
  exact ⟨h1, h3, h2⟩

private theorem one_sub_inv_eq (K : Nat) (hK : 1 ≤ K) :
    1 - (1 : Rat) / (K : Rat) = ((K : Rat) - 1) / (K : Rat) := by
  have hKpos : (0 : Rat) < (K : Rat) := rat_natCast_pos (by omega)
  have hKne : (K : Rat) ≠ 0 := rat_ne_zero_of_pos hKpos
  rw [Rat.div_def, Rat.div_def]
  have h1 : (K : Rat) * (K : Rat)⁻¹ = 1 := Rat.mul_inv_cancel (K : Rat) hKne
  grind

private theorem natCast_pred_eq (K : Nat) (hK : 1 ≤ K) :
    (((K - 1 : Nat) : Rat)) = (K : Rat) - 1 := by
  have hadd : K = (K - 1) + 1 := by omega
  have hcast : (K : Rat) = (((K - 1 : Nat) : Rat)) + 1 := by
    conv => lhs; rw [hadd]
    rw [Rat.natCast_add]; rfl
  grind

private theorem ratPow_pred_div_K (K : Nat) (hK : 1 ≤ K) :
    ratPow (((K : Rat) - 1) / (K : Rat)) K =
      (((K - 1) ^ K : Nat) : Rat) / ((K ^ K : Nat) : Rat) := by
  have hKpos : (0 : Rat) < (K : Rat) := rat_natCast_pos (by omega)
  have hKne : (K : Rat) ≠ 0 := rat_ne_zero_of_pos hKpos
  rw [ratPow_div hKne K, ← natCast_pred_eq K hK, ratPow_natCast, ratPow_natCast]

/-! ## Theorem 1: Universal Additive and Multiplicative Gaps + Tight Witness -/

theorem multidraft_additive_gap_universal (K : Nat) (hK : 1 ≤ K) {V : Nat}
    (p q : Fin V → Rat) (hp : isProbDist p) (hq : isProbDist q) (S : Fin V → Bool) :
    alphaCorr K p q - strassenObj K p q S ≤ ratPow (((K : Rat) - 1) / (K : Rat)) K := by
  have hKpos : (0 : Rat) < (K : Rat) := rat_natCast_pos (by omega)
  have hKne : (K : Rat) ≠ 0 := rat_ne_zero_of_pos hKpos
  have ⟨hx0, hx1, _⟩ := sumRat_subset_bounds q hq S
  have ⟨_, _, hc0⟩ := sumRat_subset_bounds p hp S
  let x := sumRat (fun i => if S i then q i else 0)
  let c := sumRat (fun i => if S i then 0 else p i)
  have hinv_le1 : (1 : Rat) / (K : Rat) ≤ 1 := by
    rw [rat_div_le_iff hKpos]
    have h1 : (1 : Rat) * (K : Rat) = (K : Rat) := by grind
    rw [h1]
    exact rat_natCast_le_natCast hK
  have h1K : 1 - (1 : Rat) / (K : Rat) = ((K : Rat) - 1) / (K : Rat) := one_sub_inv_eq K hK
  cases @Rat.le_total x ((1 : Rat) / (K : Rat)) with
  | inl hx_le =>
    have hsplit : alphaCorr K p q ≤ c + (K : Rat) * x := alphaCorr_le_split p q S
    have hmono := bernoulli_linear_plus_pow_mono hx0 hx_le hinv_le1 K
    have hKmul : (K : Rat) * ((1 : Rat) / (K : Rat)) = 1 := by
      rw [Rat.div_def]
      have : (K : Rat) * (1 * (K : Rat)⁻¹) = (K : Rat) * (K : Rat)⁻¹ := by grind
      rw [this, Rat.mul_inv_cancel (K : Rat) hKne]
    rw [hKmul, h1K] at hmono
    unfold strassenObj
    change alphaCorr K p q - (c + (1 - ratPow (1 - x) K)) ≤ ratPow (((K : Rat) - 1) / (K : Rat)) K
    apply rat_le_of_sub_nonneg
    have h1 : ratPow (((K : Rat) - 1) / (K : Rat)) K -
        (alphaCorr K p q - (c + (1 - ratPow (1 - x) K))) =
        ((c + (K : Rat) * x) - alphaCorr K p q) +
        ((1 + ratPow (((K : Rat) - 1) / (K : Rat)) K) - ((K : Rat) * x + ratPow (1 - x) K)) := by
      grind
    rw [h1]
    have hz : (0 : Rat) + 0 = 0 := by grind
    rw [← hz]
    exact rat_add_le_add (rat_sub_nonneg_of_le hsplit) (rat_sub_nonneg_of_le hmono)
  | inr hx_ge =>
    have ha1 : alphaCorr K p q ≤ 1 := alphaCorr_le_one p q hp
    have h1x_nonneg : 0 ≤ 1 - x := rat_sub_nonneg_of_le hx1
    have h1x_le : 1 - x ≤ 1 - (1 : Rat) / (K : Rat) := by
      apply rat_le_of_sub_nonneg
      have hEq : (1 - (1 : Rat) / (K : Rat)) - (1 - x) = x - (1 : Rat) / (K : Rat) := by grind
      rw [hEq]
      exact rat_sub_nonneg_of_le hx_ge
    have hpow : ratPow (1 - x) K ≤ ratPow (((K : Rat) - 1) / (K : Rat)) K := by
      rw [← h1K]
      exact ratPow_mono h1x_nonneg h1x_le K
    unfold strassenObj
    change alphaCorr K p q - (c + (1 - ratPow (1 - x) K)) ≤ ratPow (((K : Rat) - 1) / (K : Rat)) K
    apply rat_le_of_sub_nonneg
    have h1 : ratPow (((K : Rat) - 1) / (K : Rat)) K -
        (alphaCorr K p q - (c + (1 - ratPow (1 - x) K))) =
        (1 - alphaCorr K p q) + c +
        (ratPow (((K : Rat) - 1) / (K : Rat)) K - ratPow (1 - x) K) := by
      grind
    rw [h1]
    have hz : (0 : Rat) + 0 + 0 = 0 := by grind
    rw [← hz]
    exact rat_add_le_add (rat_add_le_add (rat_sub_nonneg_of_le ha1) hc0) (rat_sub_nonneg_of_le hpow)

theorem multidraft_multiplicative_gap_universal (K : Nat) (hK : 1 ≤ K) {V : Nat}
    (p q : Fin V → Rat) (hp : isProbDist p) (hq : isProbDist q) (S : Fin V → Bool) :
    (((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) * alphaCorr K p q ≤
      ((K ^ K : Nat) : Rat) * strassenObj K p q S := by
  have hKpos : (0 : Rat) < (K : Rat) := rat_natCast_pos (by omega)
  have hKne : (K : Rat) ≠ 0 := rat_ne_zero_of_pos hKpos
  have hKKpos : (0 : Rat) < ((K ^ K : Nat) : Rat) := by
    rw [← ratPow_natCast]
    exact ratPow_pos hKpos K
  have h1K : 1 - (1 : Rat) / (K : Rat) = ((K : Rat) - 1) / (K : Rat) := one_sub_inv_eq K hK
  let r : Rat := 1 - ratPow (((K : Rat) - 1) / (K : Rat)) K
  have hr_eq : r = (((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) / ((K ^ K : Nat) : Rat) := by
    change 1 - ratPow (((K : Rat) - 1) / (K : Rat)) K = _
    rw [ratPow_pred_div_K K hK, Rat.div_def, Rat.div_def]
    have hmul : ((K ^ K : Nat) : Rat) * ((K ^ K : Nat) : Rat)⁻¹ = 1 :=
      Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hKKpos)
    grind
  suffices hred : r * alphaCorr K p q ≤ strassenObj K p q S by
    have hmul := Rat.mul_le_mul_of_nonneg_left hred (Rat.le_of_lt hKKpos)
    have hL : ((K ^ K : Nat) : Rat) * (r * alphaCorr K p q) =
        (((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) * alphaCorr K p q := by
      rw [hr_eq, Rat.div_def]
      have h1 : ((K ^ K : Nat) : Rat) * ((K ^ K : Nat) : Rat)⁻¹ = 1 :=
        Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hKKpos)
      have h2 : ((K ^ K : Nat) : Rat) *
          ((((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) *
            ((K ^ K : Nat) : Rat)⁻¹ * alphaCorr K p q) =
          (((K ^ K : Nat) : Rat) * ((K ^ K : Nat) : Rat)⁻¹) *
          ((((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) * alphaCorr K p q) := by grind
      rw [h2, h1, Rat.one_mul]
    rw [hL] at hmul
    exact hmul
  have ⟨hx0, hx1, _⟩ := sumRat_subset_bounds q hq S
  have ⟨_, _, hc0⟩ := sumRat_subset_bounds p hp S
  let x := sumRat (fun i => if S i then q i else 0)
  let c := sumRat (fun i => if S i then 0 else p i)
  have hkm1_nonneg : (0 : Rat) ≤ ((K : Rat) - 1) / (K : Rat) := by
    rw [← natCast_pred_eq K hK]
    exact rat_div_nonneg (rat_natCast_nonneg (K - 1)) hKpos
  have hkm1_le1 : ((K : Rat) - 1) / (K : Rat) ≤ 1 := by
    rw [rat_div_le_iff hKpos]
    apply rat_le_of_sub_nonneg
    have : 1 * (K : Rat) - ((K : Rat) - 1) = 1 := by grind
    rw [this]; decide
  have hr_nonneg : 0 ≤ r :=
    rat_sub_nonneg_of_le (ratPow_le_one hkm1_nonneg hkm1_le1 K)
  have hr_le1 : r ≤ 1 := by
    apply rat_le_of_sub_nonneg
    have : 1 - r = ratPow (((K : Rat) - 1) / (K : Rat)) K := by grind
    rw [this]
    exact ratPow_nonneg hkm1_nonneg K
  cases @Rat.le_total x ((1 : Rat) / (K : Rat)) with
  | inl hx_le =>
    have hsplit : alphaCorr K p q ≤ c + (K : Rat) * x := alphaCorr_le_split p q S
    have h1 : r * alphaCorr K p q ≤ r * (c + (K : Rat) * x) :=
      Rat.mul_le_mul_of_nonneg_left hsplit hr_nonneg
    have hrc : r * c ≤ c := by
      have hm := Rat.mul_le_mul_of_nonneg_right hr_le1 hc0
      have h1c : 1 * c = c := by grind
      rw [h1c] at hm
      exact hm
    have hv_le_u : ((K : Rat) - 1) / (K : Rat) ≤ 1 - x := by
      rw [← h1K]
      apply rat_le_of_sub_nonneg
      have : (1 - x) - (1 - (1 : Rat) / (K : Rat)) = (1 : Rat) / (K : Rat) - x := by grind
      rw [this]
      exact rat_sub_nonneg_of_le hx_le
    have hgeom : geomSum (((K : Rat) - 1) / (K : Rat)) K ≤ geomSum (1 - x) K :=
      geomSum_mono hkm1_nonneg hv_le_u K
    have hr_geom : (K : Rat) * r = geomSum (((K : Rat) - 1) / (K : Rat)) K := by
      have hid := one_sub_ratPow_eq (((K : Rat) - 1) / (K : Rat)) K
      have h1minus : 1 - ((K : Rat) - 1) / (K : Rat) = (1 : Rat) / (K : Rat) := by
        rw [← h1K]; grind
      rw [h1minus] at hid
      have hKr : (K : Rat) * r = (K : Rat) * ((1 : Rat) / (K : Rat) * geomSum (((K : Rat) - 1) / (K : Rat)) K) := by
        change (K : Rat) * (1 - ratPow (((K : Rat) - 1) / (K : Rat)) K) = _
        rw [hid]
      rw [hKr, Rat.div_def]
      have hKinv : (K : Rat) * (K : Rat)⁻¹ = 1 := Rat.mul_inv_cancel (K : Rat) hKne
      have hassoc : (K : Rat) * (1 * (K : Rat)⁻¹ * geomSum (((K : Rat) - 1) / (K : Rat)) K) =
          ((K : Rat) * (K : Rat)⁻¹) * geomSum (((K : Rat) - 1) / (K : Rat)) K := by grind
      rw [hassoc, hKinv, Rat.one_mul]
    have hsec : r * ((K : Rat) * x) ≤ 1 - ratPow (1 - x) K := by
      have hmul := Rat.mul_le_mul_of_nonneg_left hgeom hx0
      have hL : x * geomSum (((K : Rat) - 1) / (K : Rat)) K = r * ((K : Rat) * x) := by
        rw [← hr_geom]; grind
      have hR : x * geomSum (1 - x) K = 1 - ratPow (1 - x) K := by
        have hid := one_sub_ratPow_eq (1 - x) K
        have h1x : 1 - (1 - x) = x := by grind
        rw [h1x] at hid
        exact hid.symm
      rw [hL, hR] at hmul
      exact hmul
    unfold strassenObj
    change r * alphaCorr K p q ≤ c + (1 - ratPow (1 - x) K)
    have h2 : r * (c + (K : Rat) * x) = r * c + r * ((K : Rat) * x) := by grind
    rw [h2] at h1
    exact Rat.le_trans h1 (rat_add_le_add hrc hsec)
  | inr hx_ge =>
    have ha1 : alphaCorr K p q ≤ 1 := alphaCorr_le_one p q hp
    have h1 : r * alphaCorr K p q ≤ r := by
      have hm := Rat.mul_le_mul_of_nonneg_left ha1 hr_nonneg
      have hr1 : r * 1 = r := by grind
      rw [hr1] at hm
      exact hm
    have h1x_nonneg : 0 ≤ 1 - x := rat_sub_nonneg_of_le hx1
    have h1x_le : 1 - x ≤ ((K : Rat) - 1) / (K : Rat) := by
      rw [← h1K]
      apply rat_le_of_sub_nonneg
      have : (1 - (1 : Rat) / (K : Rat)) - (1 - x) = x - (1 : Rat) / (K : Rat) := by grind
      rw [this]
      exact rat_sub_nonneg_of_le hx_ge
    have hpow : ratPow (1 - x) K ≤ ratPow (((K : Rat) - 1) / (K : Rat)) K :=
      ratPow_mono h1x_nonneg h1x_le K
    have hr_le_hit : r ≤ 1 - ratPow (1 - x) K := by
      apply rat_le_of_sub_nonneg
      have hEq : (1 - ratPow (1 - x) K) - r =
          ratPow (((K : Rat) - 1) / (K : Rat)) K - ratPow (1 - x) K := by grind
      rw [hEq]
      exact rat_sub_nonneg_of_le hpow
    unfold strassenObj
    change r * alphaCorr K p q ≤ c + (1 - ratPow (1 - x) K)
    have hadd := rat_add_le_add hc0 hr_le_hit
    have h0r : 0 + r = r := by grind
    rw [h0r] at hadd
    exact Rat.le_trans h1 hadd

private def extWitnessP : Fin 2 → Rat := fun i => if i.val = 0 then 1 else 0
private def extWitnessQ (K : Nat) : Fin 2 → Rat :=
  fun i => if i.val = 0 then (1 : Rat) / (K : Rat) else ((K : Rat) - 1) / (K : Rat)

private theorem extWitness_alphaCorr (K : Nat) (hK : 1 ≤ K) :
    alphaCorr K extWitnessP (extWitnessQ K) = 1 := by
  have hKpos : (0 : Rat) < (K : Rat) := rat_natCast_pos (by omega)
  have hKne : (K : Rat) ≠ 0 := rat_ne_zero_of_pos hKpos
  have hKinv : (K : Rat) * ((1 : Rat) / (K : Rat)) = 1 := by
    rw [Rat.div_def]
    have : (K : Rat) * (1 * (K : Rat)⁻¹) = (K : Rat) * (K : Rat)⁻¹ := by grind
    rw [this, Rat.mul_inv_cancel (K : Rat) hKne]
  have h0le : (0 : Rat) ≤ (K : Rat) * (((K : Rat) - 1) / (K : Rat)) := by
    rw [← natCast_pred_eq K hK]
    exact rat_mul_nonneg (Rat.le_of_lt hKpos) (rat_div_nonneg (rat_natCast_nonneg (K - 1)) hKpos)
  change (0 + min (extWitnessP ⟨0, by decide⟩) ((K : Rat) * extWitnessQ K ⟨0, by decide⟩)) +
      min (extWitnessP ⟨1, by decide⟩) ((K : Rat) * extWitnessQ K ⟨1, by decide⟩) = 1
  simp only [extWitnessP, extWitnessQ, ↓reduceIte, Nat.one_ne_zero]
  rw [hKinv, rat_min_eq_left Rat.le_refl, rat_min_eq_left h0le]
  grind

private theorem extWitness_alphaIID (K : Nat) (hK : 1 ≤ K) :
    alphaIID K extWitnessP (extWitnessQ K) = 1 - ratPow (((K : Rat) - 1) / (K : Rat)) K := by
  have hKpos : (0 : Rat) < (K : Rat) := rat_natCast_pos (by omega)
  have h1K := one_sub_inv_eq K hK
  have hkm1_nonneg : (0 : Rat) ≤ ((K : Rat) - 1) / (K : Rat) := by
    rw [← natCast_pred_eq K hK]
    exact rat_div_nonneg (rat_natCast_nonneg (K - 1)) hKpos
  have hpow_nonneg : 0 ≤ ratPow (((K : Rat) - 1) / (K : Rat)) K :=
    ratPow_nonneg hkm1_nonneg K
  have hpow0 : ratPow 0 K = 0 := ratPow_zero_of_pos hK
  have hpow1 : ratPow 1 K = 1 := ratPow_one K
  have hobj0 : strassenObj K extWitnessP (extWitnessQ K) (maskToSet 0) = 1 := by
    change (0 + 1 + 0) + (1 - ratPow (1 - (0 + 0 + 0)) K) = 1
    have h10 : (1 : Rat) - (0 + 0 + 0) = 1 := by grind
    rw [h10, hpow1]; grind
  have hobj1 : strassenObj K extWitnessP (extWitnessQ K) (maskToSet 1) =
      1 - ratPow (((K : Rat) - 1) / (K : Rat)) K := by
    change (0 + 0 + 0) + (1 - ratPow (1 - (0 + (1 : Rat) / (K : Rat) + 0)) K) = _
    have h1x : (1 : Rat) - (0 + (1 : Rat) / (K : Rat) + 0) = ((K : Rat) - 1) / (K : Rat) := by
      rw [← h1K]; grind
    rw [h1x]; grind
  have hobj2 : strassenObj K extWitnessP (extWitnessQ K) (maskToSet 2) =
      1 + (1 - ratPow ((1 : Rat) / (K : Rat)) K) := by
    change (0 + 1 + 0) + (1 - ratPow (1 - (0 + 0 + ((K : Rat) - 1) / (K : Rat))) K) = _
    have h1x : (1 : Rat) - (0 + 0 + ((K : Rat) - 1) / (K : Rat)) = (1 : Rat) / (K : Rat) := by
      rw [← h1K]; grind
    have h010 : (0 : Rat) + 1 + 0 = 1 := by grind
    rw [h1x, h010]
  have hobj3 : strassenObj K extWitnessP (extWitnessQ K) (maskToSet 3) = 1 := by
    change (0 + 0 + 0) + (1 - ratPow (1 - (0 + (1 : Rat) / (K : Rat) + ((K : Rat) - 1) / (K : Rat))) K) = 1
    have h11 : (1 : Rat) - (0 + (1 : Rat) / (K : Rat) + ((K : Rat) - 1) / (K : Rat)) = 0 := by
      rw [← h1K]; grind
    rw [h11, hpow0]; grind
  unfold alphaIID minOverMasks
  change min (min (min (min 1 (strassenObj K extWitnessP (extWitnessQ K) (maskToSet 0)))
    (strassenObj K extWitnessP (extWitnessQ K) (maskToSet 1)))
    (strassenObj K extWitnessP (extWitnessQ K) (maskToSet 2)))
    (strassenObj K extWitnessP (extWitnessQ K) (maskToSet 3)) = _
  rw [hobj0, hobj1, hobj2, hobj3]
  have hr_le1 : 1 - ratPow (((K : Rat) - 1) / (K : Rat)) K ≤ 1 := by
    apply rat_le_of_sub_nonneg
    have : 1 - (1 - ratPow (((K : Rat) - 1) / (K : Rat)) K) =
        ratPow (((K : Rat) - 1) / (K : Rat)) K := by grind
    rw [this]; exact hpow_nonneg
  have hinv_le1 : (1 : Rat) / (K : Rat) ≤ 1 := by
    rw [rat_div_le_iff hKpos]
    have : 1 * (K : Rat) = (K : Rat) := by grind
    rw [this]; exact rat_natCast_le_natCast hK
  have hobj2_ge1 : 1 ≤ 1 + (1 - ratPow ((1 : Rat) / (K : Rat)) K) := by
    apply rat_le_of_sub_nonneg
    have : 1 + (1 - ratPow ((1 : Rat) / (K : Rat)) K) - 1 =
        1 - ratPow ((1 : Rat) / (K : Rat)) K := by grind
    rw [this]
    exact rat_sub_nonneg_of_le (ratPow_le_one (rat_div_nonneg (by decide) hKpos) hinv_le1 K)
  rw [rat_min_eq_left Rat.le_refl, rat_min_eq_right hr_le1,
      rat_min_eq_left (Rat.le_trans hr_le1 hobj2_ge1), rat_min_eq_left hr_le1]

theorem multidraft_witness_exact (K : Nat) (hK : 1 ≤ K) :
    ∃ p q : Fin 2 → Rat,
      isProbDist p ∧ isProbDist q ∧
      alphaCorr K p q = 1 ∧
      alphaIID K p q = 1 - ratPow (((K : Rat) - 1) / (K : Rat)) K ∧
      alphaCorr K p q - alphaIID K p q = ratPow (((K : Rat) - 1) / (K : Rat)) K ∧
      (((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) * alphaCorr K p q =
        ((K ^ K : Nat) : Rat) * alphaIID K p q := by
  have hKpos : (0 : Rat) < (K : Rat) := rat_natCast_pos (by omega)
  have hKKpos : (0 : Rat) < ((K ^ K : Nat) : Rat) := by
    rw [← ratPow_natCast]; exact ratPow_pos hKpos K
  have hac := extWitness_alphaCorr K hK
  have hai := extWitness_alphaIID K hK
  refine ⟨extWitnessP, extWitnessQ K, ?_, ?_, hac, hai, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      unfold extWitnessP
      by_cases h0 : i.val = 0
      · simp [h0]; decide
      · simp [h0]
    · change (0 + (1 : Rat)) + 0 = 1; grind
  · refine ⟨?_, ?_⟩
    · intro i
      unfold extWitnessQ
      by_cases h0 : i.val = 0
      · simp only [h0, ↓reduceIte]
        exact rat_div_nonneg (by decide) hKpos
      · simp only [h0, ↓reduceIte]
        rw [← natCast_pred_eq K hK]
        exact rat_div_nonneg (rat_natCast_nonneg (K - 1)) hKpos
    · change (0 + (1 : Rat) / (K : Rat)) + ((K : Rat) - 1) / (K : Rat) = 1
      have h1K := one_sub_inv_eq K hK
      grind
  · rw [hac, hai]; grind
  · rw [hac, hai, ratPow_pred_div_K K hK, Rat.div_def]
    have hmul : ((K ^ K : Nat) : Rat) * ((K ^ K : Nat) : Rat)⁻¹ = 1 :=
      Rat.mul_inv_cancel _ (rat_ne_zero_of_pos hKKpos)
    grind

theorem multidraft_corr_vs_iid_exact_gaps (K : Nat) (hK : 1 ≤ K) :
    (∀ (V : Nat) (p q : Fin V → Rat), isProbDist p → isProbDist q →
      ∀ (S : Fin V → Bool),
        alphaCorr K p q - strassenObj K p q S ≤ ratPow (((K : Rat) - 1) / (K : Rat)) K ∧
        (((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) * alphaCorr K p q ≤
          ((K ^ K : Nat) : Rat) * strassenObj K p q S) ∧
    (∃ p q : Fin 2 → Rat,
      isProbDist p ∧ isProbDist q ∧
      alphaCorr K p q = 1 ∧
      alphaIID K p q = 1 - ratPow (((K : Rat) - 1) / (K : Rat)) K ∧
      alphaCorr K p q - alphaIID K p q = ratPow (((K : Rat) - 1) / (K : Rat)) K ∧
      (((K ^ K : Nat) : Rat) - (((K - 1) ^ K : Nat) : Rat)) * alphaCorr K p q =
        ((K ^ K : Nat) : Rat) * alphaIID K p q) := by
  refine ⟨fun V p q hp hq S =>
    ⟨multidraft_additive_gap_universal K hK p q hp hq S,
     multidraft_multiplicative_gap_universal K hK p q hp hq S⟩, ?_⟩
  exact multidraft_witness_exact K hK

/-! ## Theorem 2: Constructive Refutation of Default & Oracle-Sorted Cyclic Madow -/

private theorem minOverMasksAux_le {V : Nat} (f : (Fin V → Bool) → Rat) (m k : Nat) (hk : k < m) :
    minOverMasksAux f m ≤ f (maskToSet k) := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [minOverMasksAux]
    by_cases hkm : k = m
    · subst hkm; exact rat_min_le_right _ _
    · exact Rat.le_trans (rat_min_le_left _ _) (ih (by omega))

private theorem le_minOverMasksAux {V : Nat} (f : (Fin V → Bool) → Rat) (c : Rat) (hc1 : c ≤ 1)
    (m : Nat) (h : ∀ k, k < m → c ≤ f (maskToSet k)) :
    c ≤ minOverMasksAux f m := by
  induction m with
  | zero => exact hc1
  | succ m ih =>
    simp only [minOverMasksAux]
    exact rat_le_min (ih (fun k hk => h k (Nat.lt_succ_of_lt hk))) (h m (Nat.lt_succ_self m))

private theorem madowCE1_isProb : isProbDist madowCE1P ∧ isProbDist madowCE1Q := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro ⟨i, hi⟩
    match i with
    | 0 => change (0 : Rat) ≤ (1 : Rat) / 2; grind
    | 1 => change (0 : Rat) ≤ 0; exact Rat.le_refl
    | 2 => change (0 : Rat) ≤ (1 : Rat) / 2; grind
    | 3 => change (0 : Rat) ≤ 0; exact Rat.le_refl
  · change (((0 + (1 : Rat) / 2) + 0) + (1 : Rat) / 2) + 0 = 1; grind
  · intro _; change (0 : Rat) ≤ (1 : Rat) / 4; grind
  · change (((0 + (1 : Rat) / 4) + (1 : Rat) / 4) + (1 : Rat) / 4) + (1 : Rat) / 4 = 1; grind

private theorem madowCE2_isProb : isProbDist madowCE2P ∧ isProbDist madowCE2Q := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro ⟨i, hi⟩
    match i with
    | 0 => change (0 : Rat) ≤ (3 : Rat) / 10; grind
    | 1 => change (0 : Rat) ≤ (9 : Rat) / 20; grind
    | 2 => change (0 : Rat) ≤ (1 : Rat) / 4; grind
    | 3 => change (0 : Rat) ≤ 0; exact Rat.le_refl
  · change (((0 + (3 : Rat) / 10) + (9 : Rat) / 20) + (1 : Rat) / 4) + 0 = 1; grind
  · intro ⟨i, hi⟩
    match i with
    | 0 => change (0 : Rat) ≤ (1 : Rat) / 5; grind
    | 1 => change (0 : Rat) ≤ (3 : Rat) / 10; grind
    | 2 => change (0 : Rat) ≤ (1 : Rat) / 5; grind
    | 3 => change (0 : Rat) ≤ (3 : Rat) / 10; grind
  · change (((0 + (1 : Rat) / 5) + (3 : Rat) / 10) + (1 : Rat) / 5) + (3 : Rat) / 10 = 1; grind

private theorem madowCE2_monotone :
    ∀ i j : Fin 4, i.val ≤ j.val → madowCE2P j / madowCE2Q j ≤ madowCE2P i / madowCE2Q i := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  match i, j with
  | 0, 0 => exact Rat.le_refl
  | 0, 1 => change ((9 : Rat) / 20) / ((3 : Rat) / 10) ≤ ((3 : Rat) / 10) / ((1 : Rat) / 5); grind
  | 0, 2 => change ((1 : Rat) / 4) / ((1 : Rat) / 5) ≤ ((3 : Rat) / 10) / ((1 : Rat) / 5); grind
  | 0, 3 => change (0 : Rat) / ((3 : Rat) / 10) ≤ ((3 : Rat) / 10) / ((1 : Rat) / 5); grind
  | 1, 1 => exact Rat.le_refl
  | 1, 2 => change ((1 : Rat) / 4) / ((1 : Rat) / 5) ≤ ((9 : Rat) / 20) / ((3 : Rat) / 10); grind
  | 1, 3 => change (0 : Rat) / ((3 : Rat) / 10) ≤ ((9 : Rat) / 20) / ((3 : Rat) / 10); grind
  | 2, 2 => exact Rat.le_refl
  | 2, 3 => change (0 : Rat) / ((3 : Rat) / 10) ≤ ((1 : Rat) / 4) / ((1 : Rat) / 5); grind
  | 3, 3 => exact Rat.le_refl

private theorem madowCE1_alphaCorr : alphaCorr 2 madowCE1P madowCE1Q = 1 := by
  change ((((0 + min ((1 : Rat) / 2) ((2 : Nat) * ((1 : Rat) / 4))) +
    min 0 ((2 : Nat) * ((1 : Rat) / 4))) +
    min ((1 : Rat) / 2) ((2 : Nat) * ((1 : Rat) / 4))) +
    min 0 ((2 : Nat) * ((1 : Rat) / 4))) = 1
  simp only [min]; grind

private theorem madowCE2_alphaCorr : alphaCorr 2 madowCE2P madowCE2Q = 1 := by
  change ((((0 + min ((3 : Rat) / 10) ((2 : Nat) * ((1 : Rat) / 5))) +
    min ((9 : Rat) / 20) ((2 : Nat) * ((3 : Rat) / 10))) +
    min ((1 : Rat) / 4) ((2 : Nat) * ((1 : Rat) / 5))) +
    min 0 ((2 : Nat) * ((3 : Rat) / 10))) = 1
  simp only [min]; grind

private theorem madowCE1_alphaIID : alphaIID 2 madowCE1P madowCE1Q = (3 : Rat) / 4 := by
  apply Rat.le_antisymm
  · have hle : alphaIID 2 madowCE1P madowCE1Q ≤ strassenObj 2 madowCE1P madowCE1Q (maskToSet 5) :=
      minOverMasksAux_le _ 16 5 (by decide)
    have hv : strassenObj 2 madowCE1P madowCE1Q (maskToSet 5) = (3 : Rat) / 4 := by
      have h0 : maskToSet (V := 4) 5 ⟨0, by decide⟩ = true := rfl
      have h1 : maskToSet (V := 4) 5 ⟨1, by decide⟩ = false := rfl
      have h2 : maskToSet (V := 4) 5 ⟨2, by decide⟩ = true := rfl
      have h3 : maskToSet (V := 4) 5 ⟨3, by decide⟩ = false := rfl
      change ((((0 + if maskToSet (V := 4) 5 ⟨0, by decide⟩ then 0 else (1 : Rat) / 2) +
          if maskToSet (V := 4) 5 ⟨1, by decide⟩ then 0 else 0) +
          if maskToSet (V := 4) 5 ⟨2, by decide⟩ then 0 else (1 : Rat) / 2) +
          if maskToSet (V := 4) 5 ⟨3, by decide⟩ then 0 else 0) +
        (1 - ratPow (1 - ((((0 + if maskToSet (V := 4) 5 ⟨0, by decide⟩ then (1 : Rat) / 4 else 0) +
          if maskToSet (V := 4) 5 ⟨1, by decide⟩ then (1 : Rat) / 4 else 0) +
          if maskToSet (V := 4) 5 ⟨2, by decide⟩ then (1 : Rat) / 4 else 0) +
          if maskToSet (V := 4) 5 ⟨3, by decide⟩ then (1 : Rat) / 4 else 0)) 2) = (3 : Rat) / 4
      rw [h0, h1, h2, h3]
      simp only [Bool.false_eq_true, ↓reduceIte, ratPow]
      grind
    rw [hv] at hle; exact hle
  · apply le_minOverMasksAux _ ((3 : Rat) / 4) (by grind) 16
    intro k _
    let S := maskToSet (V := 4) k
    change (3 : Rat) / 4 ≤
      ((((0 + if S ⟨0, by decide⟩ then 0 else (1 : Rat) / 2) +
          if S ⟨1, by decide⟩ then 0 else 0) +
          if S ⟨2, by decide⟩ then 0 else (1 : Rat) / 2) +
          if S ⟨3, by decide⟩ then 0 else 0) +
        (1 - ratPow (1 - ((((0 + if S ⟨0, by decide⟩ then (1 : Rat) / 4 else 0) +
          if S ⟨1, by decide⟩ then (1 : Rat) / 4 else 0) +
          if S ⟨2, by decide⟩ then (1 : Rat) / 4 else 0) +
          if S ⟨3, by decide⟩ then (1 : Rat) / 4 else 0)) 2)
    cases S ⟨0, by decide⟩ <;> cases S ⟨1, by decide⟩ <;>
      cases S ⟨2, by decide⟩ <;> cases S ⟨3, by decide⟩ <;>
      (simp only [Bool.false_eq_true, ↓reduceIte, ratPow]; grind)

private theorem madowCE2_alphaIID : alphaIID 2 madowCE2P madowCE2Q = (91 : Rat) / 100 := by
  apply Rat.le_antisymm
  · have hle : alphaIID 2 madowCE2P madowCE2Q ≤ strassenObj 2 madowCE2P madowCE2Q (maskToSet 7) :=
      minOverMasksAux_le _ 16 7 (by decide)
    have hv : strassenObj 2 madowCE2P madowCE2Q (maskToSet 7) = (91 : Rat) / 100 := by
      have h0 : maskToSet (V := 4) 7 ⟨0, by decide⟩ = true := rfl
      have h1 : maskToSet (V := 4) 7 ⟨1, by decide⟩ = true := rfl
      have h2 : maskToSet (V := 4) 7 ⟨2, by decide⟩ = true := rfl
      have h3 : maskToSet (V := 4) 7 ⟨3, by decide⟩ = false := rfl
      change ((((0 + if maskToSet (V := 4) 7 ⟨0, by decide⟩ then 0 else (3 : Rat) / 10) +
          if maskToSet (V := 4) 7 ⟨1, by decide⟩ then 0 else (9 : Rat) / 20) +
          if maskToSet (V := 4) 7 ⟨2, by decide⟩ then 0 else (1 : Rat) / 4) +
          if maskToSet (V := 4) 7 ⟨3, by decide⟩ then 0 else 0) +
        (1 - ratPow (1 - ((((0 + if maskToSet (V := 4) 7 ⟨0, by decide⟩ then (1 : Rat) / 5 else 0) +
          if maskToSet (V := 4) 7 ⟨1, by decide⟩ then (3 : Rat) / 10 else 0) +
          if maskToSet (V := 4) 7 ⟨2, by decide⟩ then (1 : Rat) / 5 else 0) +
          if maskToSet (V := 4) 7 ⟨3, by decide⟩ then (3 : Rat) / 10 else 0)) 2) = (91 : Rat) / 100
      rw [h0, h1, h2, h3]
      simp only [Bool.false_eq_true, ↓reduceIte, ratPow]
      grind
    rw [hv] at hle; exact hle
  · apply le_minOverMasksAux _ ((91 : Rat) / 100) (by grind) 16
    intro k _
    let S := maskToSet (V := 4) k
    change (91 : Rat) / 100 ≤
      ((((0 + if S ⟨0, by decide⟩ then 0 else (3 : Rat) / 10) +
          if S ⟨1, by decide⟩ then 0 else (9 : Rat) / 20) +
          if S ⟨2, by decide⟩ then 0 else (1 : Rat) / 4) +
          if S ⟨3, by decide⟩ then 0 else 0) +
        (1 - ratPow (1 - ((((0 + if S ⟨0, by decide⟩ then (1 : Rat) / 5 else 0) +
          if S ⟨1, by decide⟩ then (3 : Rat) / 10 else 0) +
          if S ⟨2, by decide⟩ then (1 : Rat) / 5 else 0) +
          if S ⟨3, by decide⟩ then (3 : Rat) / 10 else 0)) 2)
    cases S ⟨0, by decide⟩ <;> cases S ⟨1, by decide⟩ <;>
      cases S ⟨2, by decide⟩ <;> cases S ⟨3, by decide⟩ <;>
      (simp only [Bool.false_eq_true, ↓reduceIte, ratPow]; grind)

private theorem madowCE1_intervals (S : Fin 4 → Bool) :
    madowIntervals2Aux madowCE1Q S 4 (Nat.le_refl 4) =
      (if S ⟨3, by decide⟩ then [((1 : Rat) / 2, (1 : Rat))] else []) ++
      (if S ⟨2, by decide⟩ then [((0 : Rat), (1 : Rat) / 2)] else []) ++
      (if S ⟨1, by decide⟩ then [((1 : Rat) / 2, (1 : Rat))] else []) ++
      (if S ⟨0, by decide⟩ then [((0 : Rat), (1 : Rat) / 2)] else []) := by
  have hc0 : cdfRat madowCE1Q ⟨0, by decide⟩ = 0 := by
    simp only [cdfRat, sumRat, madowCE1Q]; grind
  have hc1 : cdfRat madowCE1Q ⟨1, by decide⟩ = (1 : Rat) / 4 := by
    simp only [cdfRat, sumRat, madowCE1Q]; grind
  have hc2 : cdfRat madowCE1Q ⟨2, by decide⟩ = (1 : Rat) / 2 := by
    simp only [cdfRat, sumRat, madowCE1Q]; grind
  have hc3 : cdfRat madowCE1Q ⟨3, by decide⟩ = (3 : Rat) / 4 := by
    simp only [cdfRat, sumRat, madowCE1Q]; grind
  unfold madowIntervals2Aux madowIntervals2Aux madowIntervals2Aux madowIntervals2Aux madowIntervals2Aux
  simp only [madowCE1Q, hc0, hc1, hc2, hc3, fracPart2]
  have h1 : ¬ ((2 : Rat) * ((1 : Rat) / 4) ≤ 0) := by grind
  have h2 : ¬ ((1 : Rat) ≤ (2 : Rat) * ((1 : Rat) / 4)) := by grind
  have hf0 : ¬ ((1 : Rat) ≤ (2 : Rat) * 0) := by grind
  have hf1 : ¬ ((1 : Rat) ≤ (2 : Rat) * ((1 : Rat) / 4)) := by grind
  have hf2 : (1 : Rat) ≤ (2 : Rat) * ((1 : Rat) / 2) := by grind
  have hf3 : (1 : Rat) ≤ (2 : Rat) * ((3 : Rat) / 4) := by grind
  simp only [h1, h2, hf0, hf2, hf3, ↓reduceIte]
  have he0 : (2 : Rat) * 0 + (2 : Rat) * ((1 : Rat) / 4) ≤ 1 := by grind
  have he1 : (2 : Rat) * ((1 : Rat) / 4) + (2 : Rat) * ((1 : Rat) / 4) ≤ 1 := by grind
  have he2 : ((2 : Rat) * ((1 : Rat) / 2) - 1) + (2 : Rat) * ((1 : Rat) / 4) ≤ 1 := by grind
  have he3 : ((2 : Rat) * ((3 : Rat) / 4) - 1) + (2 : Rat) * ((1 : Rat) / 4) ≤ 1 := by grind
  simp only [he0, he1, he2, he3, ↓reduceIte]
  have ha0 : (2 : Rat) * 0 = 0 := by grind
  have hb0 : (2 : Rat) * 0 + (2 : Rat) * ((1 : Rat) / 4) = (1 : Rat) / 2 := by grind
  have ha1 : (2 : Rat) * ((1 : Rat) / 4) = (1 : Rat) / 2 := by grind
  have hb1 : (2 : Rat) * ((1 : Rat) / 4) + (2 : Rat) * ((1 : Rat) / 4) = 1 := by grind
  have ha2 : (2 : Rat) * ((1 : Rat) / 2) - 1 = 0 := by grind
  have hb2 : ((2 : Rat) * ((1 : Rat) / 2) - 1) + (2 : Rat) * ((1 : Rat) / 4) = (1 : Rat) / 2 := by grind
  have ha3 : (2 : Rat) * ((3 : Rat) / 4) - 1 = (1 : Rat) / 2 := by grind
  have hb3 : ((2 : Rat) * ((3 : Rat) / 4) - 1) + (2 : Rat) * ((1 : Rat) / 4) = 1 := by grind
  rw [hb3, hb2, hb1, hb0, ha3, ha2, ha1, ha0]
  cases S ⟨0, by decide⟩ <;> cases S ⟨1, by decide⟩ <;> cases S ⟨2, by decide⟩ <;> cases S ⟨3, by decide⟩ <;> rfl

private theorem madowCE2_intervals (S : Fin 4 → Bool) :
    madowIntervals2Aux madowCE2Q S 4 (Nat.le_refl 4) =
      (if S ⟨3, by decide⟩ then [((2 : Rat) / 5, (1 : Rat))] else []) ++
      (if S ⟨2, by decide⟩ then [((0 : Rat), (2 : Rat) / 5)] else []) ++
      (if S ⟨1, by decide⟩ then [((2 : Rat) / 5, (1 : Rat))] else []) ++
      (if S ⟨0, by decide⟩ then [((0 : Rat), (2 : Rat) / 5)] else []) := by
  have hc0 : cdfRat madowCE2Q ⟨0, by decide⟩ = 0 := by
    simp only [cdfRat, sumRat, madowCE2Q]; grind
  have hc1 : cdfRat madowCE2Q ⟨1, by decide⟩ = (1 : Rat) / 5 := by
    simp only [cdfRat, sumRat, madowCE2Q]; grind
  have hc2 : cdfRat madowCE2Q ⟨2, by decide⟩ = (1 : Rat) / 2 := by
    simp only [cdfRat, sumRat, madowCE2Q]; grind
  have hc3 : cdfRat madowCE2Q ⟨3, by decide⟩ = (7 : Rat) / 10 := by
    simp only [cdfRat, sumRat, madowCE2Q]; grind
  unfold madowIntervals2Aux madowIntervals2Aux madowIntervals2Aux madowIntervals2Aux madowIntervals2Aux
  simp only [madowCE2Q, hc0, hc1, hc2, hc3, fracPart2]
  have h1a : ¬ ((2 : Rat) * ((1 : Rat) / 5) ≤ 0) := by grind
  have h1b : ¬ ((1 : Rat) ≤ (2 : Rat) * ((1 : Rat) / 5)) := by grind
  have h2a : ¬ ((2 : Rat) * ((3 : Rat) / 10) ≤ 0) := by grind
  have h2b : ¬ ((1 : Rat) ≤ (2 : Rat) * ((3 : Rat) / 10)) := by grind
  have hf0 : ¬ ((1 : Rat) ≤ (2 : Rat) * 0) := by grind
  have hf1 : ¬ ((1 : Rat) ≤ (2 : Rat) * ((1 : Rat) / 5)) := by grind
  have hf2 : (1 : Rat) ≤ (2 : Rat) * ((1 : Rat) / 2) := by grind
  have hf3 : (1 : Rat) ≤ (2 : Rat) * ((7 : Rat) / 10) := by grind
  simp only [h1a, h1b, h2a, h2b, hf0, hf2, hf3, ↓reduceIte]
  have he0 : (2 : Rat) * 0 + (2 : Rat) * ((1 : Rat) / 5) ≤ 1 := by grind
  have he1 : (2 : Rat) * ((1 : Rat) / 5) + (2 : Rat) * ((3 : Rat) / 10) ≤ 1 := by grind
  have he2 : ((2 : Rat) * ((1 : Rat) / 2) - 1) + (2 : Rat) * ((1 : Rat) / 5) ≤ 1 := by grind
  have he3 : ((2 : Rat) * ((7 : Rat) / 10) - 1) + (2 : Rat) * ((3 : Rat) / 10) ≤ 1 := by grind
  simp only [he0, he1, he2, he3, ↓reduceIte]
  have ha0 : (2 : Rat) * 0 = 0 := by grind
  have hb0 : (2 : Rat) * 0 + (2 : Rat) * ((1 : Rat) / 5) = (2 : Rat) / 5 := by grind
  have ha1 : (2 : Rat) * ((1 : Rat) / 5) = (2 : Rat) / 5 := by grind
  have hb1 : (2 : Rat) * ((1 : Rat) / 5) + (2 : Rat) * ((3 : Rat) / 10) = 1 := by grind
  have ha2 : (2 : Rat) * ((1 : Rat) / 2) - 1 = 0 := by grind
  have hb2 : ((2 : Rat) * ((1 : Rat) / 2) - 1) + (2 : Rat) * ((1 : Rat) / 5) = (2 : Rat) / 5 := by grind
  have ha3 : (2 : Rat) * ((7 : Rat) / 10) - 1 = (2 : Rat) / 5 := by grind
  have hb3 : ((2 : Rat) * ((7 : Rat) / 10) - 1) + (2 : Rat) * ((3 : Rat) / 10) = 1 := by grind
  rw [hb3, hb2, hb1, hb0, ha3, ha2, ha1, ha0]
  cases S ⟨0, by decide⟩ <;> cases S ⟨1, by decide⟩ <;> cases S ⟨2, by decide⟩ <;> cases S ⟨3, by decide⟩ <;> rfl

private theorem unionMeasure_two_half (a b c d : Bool) :
    unionMeasure
      ((if d then [((1 : Rat) / 2, (1 : Rat))] else []) ++
       (if c then [((0 : Rat), (1 : Rat) / 2)] else []) ++
       (if b then [((1 : Rat) / 2, (1 : Rat))] else []) ++
       (if a then [((0 : Rat), (1 : Rat) / 2)] else [])) =
      (if a || c then (1 : Rat) / 2 else 0) + (if b || d then (1 : Rat) / 2 else 0) := by
  have h00 : (0 : Rat) ≤ 0 := Rat.le_refl
  have h0h : (0 : Rat) ≤ (1 : Rat) / 2 := by grind
  have hh0 : ¬ ((1 : Rat) / 2 ≤ (0 : Rat)) := by grind
  have hhh : (1 : Rat) / 2 ≤ (1 : Rat) / 2 := Rat.le_refl
  have hh1 : (1 : Rat) / 2 ≤ (1 : Rat) := by grind
  have h1h : ¬ ((1 : Rat) ≤ (1 : Rat) / 2) := by grind
  have h11 : (1 : Rat) ≤ (1 : Rat) := Rat.le_refl
  have hsub1 : (1 : Rat) - 0 = 1 := by grind
  have hsub2 : (1 : Rat) - (1 : Rat) / 2 = (1 : Rat) / 2 := by grind
  have hsub3 : (1 : Rat) / 2 - 0 = (1 : Rat) / 2 := by grind
  cases a <;> cases b <;> cases c <;> cases d <;>
    (simp only [unionMeasure, sortIntervals, insertInterval, measureSortedIntervals, List.append_nil,
      List.nil_append, List.cons_append, Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_true,
      min, max, h00, h0h, hh0, hhh, hh1, h1h, h11, hsub1, hsub2, hsub3]; grind)

private theorem unionMeasure_two_fifths (a b c d : Bool) :
    unionMeasure
      ((if d then [((2 : Rat) / 5, (1 : Rat))] else []) ++
       (if c then [((0 : Rat), (2 : Rat) / 5)] else []) ++
       (if b then [((2 : Rat) / 5, (1 : Rat))] else []) ++
       (if a then [((0 : Rat), (2 : Rat) / 5)] else [])) =
      (if a || c then (2 : Rat) / 5 else 0) + (if b || d then (3 : Rat) / 5 else 0) := by
  have h00 : (0 : Rat) ≤ 0 := Rat.le_refl
  have h0f : (0 : Rat) ≤ (2 : Rat) / 5 := by grind
  have hf0 : ¬ ((2 : Rat) / 5 ≤ (0 : Rat)) := by grind
  have hff : (2 : Rat) / 5 ≤ (2 : Rat) / 5 := Rat.le_refl
  have hf1 : (2 : Rat) / 5 ≤ (1 : Rat) := by grind
  have h1f : ¬ ((1 : Rat) ≤ (2 : Rat) / 5) := by grind
  have h11 : (1 : Rat) ≤ (1 : Rat) := Rat.le_refl
  have hsub1 : (1 : Rat) - 0 = 1 := by grind
  have hsub2 : (1 : Rat) - (2 : Rat) / 5 = (3 : Rat) / 5 := by grind
  have hsub3 : (2 : Rat) / 5 - 0 = (2 : Rat) / 5 := by grind
  have h135 : ¬ ((1 : Rat) ≤ (3 : Rat) / 5) := by grind
  cases a <;> cases b <;> cases c <;> cases d <;>
    (simp only [unionMeasure, sortIntervals, insertInterval, measureSortedIntervals, List.append_nil,
      List.nil_append, List.cons_append, Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_true,
      min, max, h00, h0f, hf0, hff, hf1, h1f, h11, hsub1, hsub2, hsub3, h135]; grind)

private theorem madowCE1_obj_eq (S : Fin 4 → Bool) :
    madowObj2 madowCE1P madowCE1Q S =
      (if S ⟨0, by decide⟩ then 0 else (1 : Rat) / 2) +
      (if S ⟨2, by decide⟩ then 0 else (1 : Rat) / 2) +
      (if S ⟨0, by decide⟩ || S ⟨2, by decide⟩ then (1 : Rat) / 2 else 0) +
      (if S ⟨1, by decide⟩ || S ⟨3, by decide⟩ then (1 : Rat) / 2 else 0) := by
  unfold madowObj2 madowHit2
  rw [madowCE1_intervals, unionMeasure_two_half]
  change ((((0 + if S ⟨0, by decide⟩ then 0 else (1 : Rat) / 2) +
      if S ⟨1, by decide⟩ then 0 else 0) +
      if S ⟨2, by decide⟩ then 0 else (1 : Rat) / 2) +
      if S ⟨3, by decide⟩ then 0 else 0) + _ = _
  cases S ⟨0, by decide⟩ <;> cases S ⟨1, by decide⟩ <;> cases S ⟨2, by decide⟩ <;> cases S ⟨3, by decide⟩ <;>
    (simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_true]; grind)

private theorem madowCE2_obj_eq (S : Fin 4 → Bool) :
    madowObj2 madowCE2P madowCE2Q S =
      (if S ⟨0, by decide⟩ then 0 else (3 : Rat) / 10) +
      (if S ⟨1, by decide⟩ then 0 else (9 : Rat) / 20) +
      (if S ⟨2, by decide⟩ then 0 else (1 : Rat) / 4) +
      (if S ⟨0, by decide⟩ || S ⟨2, by decide⟩ then (2 : Rat) / 5 else 0) +
      (if S ⟨1, by decide⟩ || S ⟨3, by decide⟩ then (3 : Rat) / 5 else 0) := by
  unfold madowObj2 madowHit2
  rw [madowCE2_intervals, unionMeasure_two_fifths]
  change ((((0 + if S ⟨0, by decide⟩ then 0 else (3 : Rat) / 10) +
      if S ⟨1, by decide⟩ then 0 else (9 : Rat) / 20) +
      if S ⟨2, by decide⟩ then 0 else (1 : Rat) / 4) +
      if S ⟨3, by decide⟩ then 0 else 0) + _ = _
  cases S ⟨0, by decide⟩ <;> cases S ⟨1, by decide⟩ <;> cases S ⟨2, by decide⟩ <;> cases S ⟨3, by decide⟩ <;>
    (simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_true]; grind)

private theorem madowCE1_alphaMadow2 : alphaMadow2 madowCE1P madowCE1Q = (1 : Rat) / 2 := by
  apply Rat.le_antisymm
  · have hle : alphaMadow2 madowCE1P madowCE1Q ≤ madowObj2 madowCE1P madowCE1Q (maskToSet 5) :=
      minOverMasksAux_le _ 16 5 (by decide)
    rw [madowCE1_obj_eq] at hle
    have h0 : maskToSet (V := 4) 5 ⟨0, by decide⟩ = true := rfl
    have h1 : maskToSet (V := 4) 5 ⟨1, by decide⟩ = false := rfl
    have h2 : maskToSet (V := 4) 5 ⟨2, by decide⟩ = true := rfl
    have h3 : maskToSet (V := 4) 5 ⟨3, by decide⟩ = false := rfl
    rw [h0, h1, h2, h3] at hle
    have hv : (if true then (0 : Rat) else (1 : Rat) / 2) +
        (if true then 0 else (1 : Rat) / 2) +
        (if true || true then (1 : Rat) / 2 else 0) +
        (if false || false then (1 : Rat) / 2 else 0) = (1 : Rat) / 2 := by
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_true]; grind
    rw [hv] at hle; exact hle
  · apply le_minOverMasksAux _ ((1 : Rat) / 2) (by grind) 16
    intro k _
    rw [madowCE1_obj_eq]
    let S := maskToSet (V := 4) k
    change (1 : Rat) / 2 ≤
      (if S ⟨0, by decide⟩ then 0 else (1 : Rat) / 2) +
      (if S ⟨2, by decide⟩ then 0 else (1 : Rat) / 2) +
      (if S ⟨0, by decide⟩ || S ⟨2, by decide⟩ then (1 : Rat) / 2 else 0) +
      (if S ⟨1, by decide⟩ || S ⟨3, by decide⟩ then (1 : Rat) / 2 else 0)
    cases S ⟨0, by decide⟩ <;> cases S ⟨1, by decide⟩ <;>
      cases S ⟨2, by decide⟩ <;> cases S ⟨3, by decide⟩ <;>
      (simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_true]; grind)

private theorem madowCE2_alphaMadow2 : alphaMadow2 madowCE2P madowCE2Q = (17 : Rat) / 20 := by
  apply Rat.le_antisymm
  · have hle : alphaMadow2 madowCE2P madowCE2Q ≤ madowObj2 madowCE2P madowCE2Q (maskToSet 5) :=
      minOverMasksAux_le _ 16 5 (by decide)
    rw [madowCE2_obj_eq] at hle
    have h0 : maskToSet (V := 4) 5 ⟨0, by decide⟩ = true := rfl
    have h1 : maskToSet (V := 4) 5 ⟨1, by decide⟩ = false := rfl
    have h2 : maskToSet (V := 4) 5 ⟨2, by decide⟩ = true := rfl
    have h3 : maskToSet (V := 4) 5 ⟨3, by decide⟩ = false := rfl
    rw [h0, h1, h2, h3] at hle
    have hv : (if true then (0 : Rat) else (3 : Rat) / 10) +
        (if false then 0 else (9 : Rat) / 20) +
        (if true then 0 else (1 : Rat) / 4) +
        (if true || true then (2 : Rat) / 5 else 0) +
        (if false || false then (3 : Rat) / 5 else 0) = (17 : Rat) / 20 := by
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_true]; grind
    rw [hv] at hle; exact hle
  · apply le_minOverMasksAux _ ((17 : Rat) / 20) (by grind) 16
    intro k _
    rw [madowCE2_obj_eq]
    let S := maskToSet (V := 4) k
    change (17 : Rat) / 20 ≤
      (if S ⟨0, by decide⟩ then 0 else (3 : Rat) / 10) +
      (if S ⟨1, by decide⟩ then 0 else (9 : Rat) / 20) +
      (if S ⟨2, by decide⟩ then 0 else (1 : Rat) / 4) +
      (if S ⟨0, by decide⟩ || S ⟨2, by decide⟩ then (2 : Rat) / 5 else 0) +
      (if S ⟨1, by decide⟩ || S ⟨3, by decide⟩ then (3 : Rat) / 5 else 0)
    cases S ⟨0, by decide⟩ <;> cases S ⟨1, by decide⟩ <;>
      cases S ⟨2, by decide⟩ <;> cases S ⟨3, by decide⟩ <;>
      (simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_true]; grind)

theorem cyclic_madow_optimality_refutation_exact :
    (isProbDist madowCE1P ∧ isProbDist madowCE1Q ∧
      alphaMadow2 madowCE1P madowCE1Q = (1 : Rat) / 2 ∧
      alphaIID 2 madowCE1P madowCE1Q = (3 : Rat) / 4 ∧
      alphaCorr 2 madowCE1P madowCE1Q = 1 ∧
      alphaMadow2 madowCE1P madowCE1Q < alphaIID 2 madowCE1P madowCE1Q ∧
      alphaIID 2 madowCE1P madowCE1Q < alphaCorr 2 madowCE1P madowCE1Q) ∧
    (isProbDist madowCE2P ∧ isProbDist madowCE2Q ∧
      (∀ i j : Fin 4, i.val ≤ j.val → madowCE2P j / madowCE2Q j ≤ madowCE2P i / madowCE2Q i) ∧
      alphaMadow2 madowCE2P madowCE2Q = (17 : Rat) / 20 ∧
      alphaIID 2 madowCE2P madowCE2Q = (91 : Rat) / 100 ∧
      alphaCorr 2 madowCE2P madowCE2Q = 1 ∧
      alphaMadow2 madowCE2P madowCE2Q < alphaIID 2 madowCE2P madowCE2Q ∧
      alphaIID 2 madowCE2P madowCE2Q < alphaCorr 2 madowCE2P madowCE2Q) := by
  have ⟨hp1, hq1⟩ := madowCE1_isProb
  have ⟨hp2, hq2⟩ := madowCE2_isProb
  have hm1 := madowCE1_alphaMadow2
  have hi1 := madowCE1_alphaIID
  have hc1 := madowCE1_alphaCorr
  have hm2 := madowCE2_alphaMadow2
  have hi2 := madowCE2_alphaIID
  have hc2 := madowCE2_alphaCorr
  refine ⟨⟨hp1, hq1, hm1, hi1, hc1, ?_, ?_⟩, ⟨hp2, hq2, madowCE2_monotone, hm2, hi2, hc2, ?_, ?_⟩⟩
  · rw [hm1, hi1]; grind
  · rw [hi1, hc1]; grind
  · rw [hm2, hi2]; grind
  · rw [hi2, hc2]; grind

end SpecDecodingOt
