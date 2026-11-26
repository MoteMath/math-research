/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RopeQ32Coprime.Defs
import RopeQ32Coprime.RatOrder

/-!
# Pillar 2B & Dyadic Cayley Group: Relative-Position Error Decomposition and Exact `SO(2, Q)` Composition

Proves Theorems 5 and 6 of `RopeQ32CoprimeChallenge`:
- Theorem 5 (`relative_position_factorization_error_decomposition`): Exact algebraic separation of
  phase-truncation non-commutativity from rotation-matrix quantization error, plus the
  context-length-independent `Q32` dominance bound over frozen `BF16`/`FP16` RoPE at `L = 128K`.
- Theorem 6 (`dyadic_cayley_relative_composition_exact`): Exact `SO(2, Q)` group composition,
  orthogonality, transpose-inverse, norm preservation, and relative-position factorization of
  rational Cayley rotations `R_Cayley(t)`.
-/

namespace RopeQ32Coprime

/-! ### Exact `2 × 2` Rotation Algebra & Score Identities -/

theorem rotScore_eq_relScore (q k : Rat × Rat) (Rm Rn : Rot2) :
    rotScore q k Rm Rn = relScore q k (Rm.transpose.mul Rn) := by
  unfold rotScore relScore dot2 Rot2.apply Rot2.transpose Rot2.mul
  grind

theorem rot2_error_identity (RphM RphN Rm Rn : Rot2) :
    let Em := Rm.sub RphM
    let En := Rn.sub RphN
    Rm.transpose.mul Rn =
      (RphM.transpose.mul RphN).add
        ((Em.transpose.mul RphN).add ((RphM.transpose.mul En).add (Em.transpose.mul En))) := by
  unfold Rot2.sub Rot2.add Rot2.transpose Rot2.mul
  cases RphM; cases RphN; cases Rm; cases Rn
  simp only [Rot2.mk.injEq]
  constructor <;> grind

theorem relScore_add (q k : Rat × Rat) (A B : Rot2) :
    relScore q k (A.add B) = relScore q k A + relScore q k B := by
  unfold relScore dot2 Rot2.apply Rot2.add
  grind

theorem rotScore_error_decomp (q k : Rat × Rat) (RphM RphN Rm Rn Rrel : Rot2) :
    let Em := Rm.sub RphM
    let En := Rn.sub RphN
    rotScore q k Rm Rn - relScore q k Rrel =
      (rotScore q k RphM RphN - relScore q k Rrel) +
      (relScore q k (Em.transpose.mul RphN) +
       relScore q k (RphM.transpose.mul En) +
       relScore q k (Em.transpose.mul En)) := by
  rw [rotScore_eq_relScore q k Rm Rn, rotScore_eq_relScore q k RphM RphN]
  rw [rot2_error_identity RphM RphN Rm Rn]
  rw [relScore_add, relScore_add, relScore_add]
  grind

theorem relScore_abs_bound (q k : Rat × Rat) (A : Rot2) (B : Rat)
    (hc : ratAbs A.c ≤ B) (hs : ratAbs A.s ≤ B) :
    ratAbs (relScore q k A) ≤ B * l1Norm2 q * l1Norm2 k := by
  unfold relScore dot2 Rot2.apply l1Norm2
  have hB : (0 : Rat) ≤ B := Rat.le_trans (ratAbs_nonneg A.c) hc
  have h1 : ratAbs (q.1 * (A.c * k.1 - A.s * k.2) + q.2 * (A.s * k.1 + A.c * k.2)) ≤
      ratAbs (q.1 * (A.c * k.1 - A.s * k.2)) + ratAbs (q.2 * (A.s * k.1 + A.c * k.2)) :=
    ratAbs_add_le _ _
  have h2 : ratAbs (A.c * k.1 - A.s * k.2) ≤ B * (ratAbs k.1 + ratAbs k.2) := by
    have hsub := ratAbs_sub_le (A.c * k.1) (A.s * k.2)
    rw [ratAbs_mul, ratAbs_mul] at hsub
    have hc' := rat_mul_le_mul_of_nonneg_right hc (ratAbs_nonneg k.1)
    have hs' := rat_mul_le_mul_of_nonneg_right hs (ratAbs_nonneg k.2)
    have hsum := rat_add_le_add hc' hs'
    have hdist : B * ratAbs k.1 + B * ratAbs k.2 = B * (ratAbs k.1 + ratAbs k.2) := by grind
    rw [hdist] at hsum
    exact Rat.le_trans hsub hsum
  have h3 : ratAbs (A.s * k.1 + A.c * k.2) ≤ B * (ratAbs k.1 + ratAbs k.2) := by
    have hadd := ratAbs_add_le (A.s * k.1) (A.c * k.2)
    rw [ratAbs_mul, ratAbs_mul] at hadd
    have hs' := rat_mul_le_mul_of_nonneg_right hs (ratAbs_nonneg k.1)
    have hc' := rat_mul_le_mul_of_nonneg_right hc (ratAbs_nonneg k.2)
    have hsum := rat_add_le_add hs' hc'
    have hdist : B * ratAbs k.1 + B * ratAbs k.2 = B * (ratAbs k.1 + ratAbs k.2) := by grind
    rw [hdist] at hsum
    exact Rat.le_trans hadd hsum
  rw [ratAbs_mul, ratAbs_mul] at h1
  have hq1 := rat_mul_le_mul_of_nonneg_left h2 (ratAbs_nonneg q.1)
  have hq2 := rat_mul_le_mul_of_nonneg_left h3 (ratAbs_nonneg q.2)
  have htot := Rat.le_trans h1 (rat_add_le_add hq1 hq2)
  have heq : ratAbs q.1 * (B * (ratAbs k.1 + ratAbs k.2)) +
      ratAbs q.2 * (B * (ratAbs k.1 + ratAbs k.2)) =
      B * (ratAbs q.1 + ratAbs q.2) * (ratAbs k.1 + ratAbs k.2) := by grind
  rw [heq] at htot
  exact htot

theorem rot2_mul_entry_bound (A B : Rot2) (a b : Rat)
    (hAc : ratAbs A.c ≤ a) (hAs : ratAbs A.s ≤ a)
    (hBc : ratAbs B.c ≤ b) (hBs : ratAbs B.s ≤ b) :
    ratAbs (A.mul B).c ≤ 2 * a * b ∧ ratAbs (A.mul B).s ≤ 2 * a * b := by
  have ha : (0 : Rat) ≤ a := Rat.le_trans (ratAbs_nonneg A.c) hAc
  have hb : (0 : Rat) ≤ b := Rat.le_trans (ratAbs_nonneg B.c) hBc
  unfold Rot2.mul
  constructor
  · have h1 := ratAbs_sub_le (A.c * B.c) (A.s * B.s)
    rw [ratAbs_mul, ratAbs_mul] at h1
    have hcc : ratAbs A.c * ratAbs B.c ≤ a * b :=
      Rat.le_trans (rat_mul_le_mul_of_nonneg_right hAc (ratAbs_nonneg B.c))
        (rat_mul_le_mul_of_nonneg_left hBc ha)
    have hss : ratAbs A.s * ratAbs B.s ≤ a * b :=
      Rat.le_trans (rat_mul_le_mul_of_nonneg_right hAs (ratAbs_nonneg B.s))
        (rat_mul_le_mul_of_nonneg_left hBs ha)
    have hsum := rat_add_le_add hcc hss
    have heq : a * b + a * b = 2 * a * b := by grind
    rw [heq] at hsum
    exact Rat.le_trans h1 hsum
  · have h1 := ratAbs_add_le (A.s * B.c) (A.c * B.s)
    rw [ratAbs_mul, ratAbs_mul] at h1
    have hsc : ratAbs A.s * ratAbs B.c ≤ a * b :=
      Rat.le_trans (rat_mul_le_mul_of_nonneg_right hAs (ratAbs_nonneg B.c))
        (rat_mul_le_mul_of_nonneg_left hBc ha)
    have hcs : ratAbs A.c * ratAbs B.s ≤ a * b :=
      Rat.le_trans (rat_mul_le_mul_of_nonneg_right hAc (ratAbs_nonneg B.s))
        (rat_mul_le_mul_of_nonneg_left hBs ha)
    have hsum := rat_add_le_add hsc hcs
    have heq : a * b + a * b = 2 * a * b := by grind
    rw [heq] at hsum
    exact Rat.le_trans h1 hsum

theorem exact_phase_quantized_rot_bound (q k : Rat × Rat) (RphM RphN Rm Rn Rrel : Rot2) (ε : Rat)
    (hrel : RphM.transpose.mul RphN = Rrel)
    (hMc : ratAbs RphM.c ≤ 1) (hMs : ratAbs RphM.s ≤ 1)
    (hNc : ratAbs RphN.c ≤ 1) (hNs : ratAbs RphN.s ≤ 1)
    (hEmc : ratAbs (Rm.sub RphM).c ≤ ε) (hEms : ratAbs (Rm.sub RphM).s ≤ ε)
    (hEnc : ratAbs (Rn.sub RphN).c ≤ ε) (hEns : ratAbs (Rn.sub RphN).s ≤ ε) :
    ratAbs (rotScore q k Rm Rn - relScore q k Rrel) ≤
      (4 * ε + 2 * ε * ε) * l1Norm2 q * l1Norm2 k := by
  have hdecomp := rotScore_error_decomp q k RphM RphN Rm Rn Rrel
  dsimp only at hdecomp
  have hph0 : rotScore q k RphM RphN - relScore q k Rrel = 0 := by
    rw [rotScore_eq_relScore, hrel]
    grind
  rw [hph0, Rat.zero_add] at hdecomp
  rw [hdecomp]
  let Em := Rm.sub RphM
  let En := Rn.sub RphN
  have hEmT_c : ratAbs Em.transpose.c ≤ ε := hEmc
  have hEmT_s : ratAbs Em.transpose.s ≤ ε := by
    unfold Rot2.transpose; rw [ratAbs_neg]; exact hEms
  have hMT_c : ratAbs RphM.transpose.c ≤ 1 := hMc
  have hMT_s : ratAbs RphM.transpose.s ≤ 1 := by
    unfold Rot2.transpose; rw [ratAbs_neg]; exact hMs
  have hB1 := rot2_mul_entry_bound Em.transpose RphN ε 1 hEmT_c hEmT_s hNc hNs
  have hB2 := rot2_mul_entry_bound RphM.transpose En 1 ε hMT_c hMT_s hEnc hEns
  have hB3 := rot2_mul_entry_bound Em.transpose En ε ε hEmT_c hEmT_s hEnc hEns
  have hs1 := relScore_abs_bound q k (Em.transpose.mul RphN) (2 * ε * 1) hB1.1 hB1.2
  have hs2 := relScore_abs_bound q k (RphM.transpose.mul En) (2 * 1 * ε) hB2.1 hB2.2
  have hs3 := relScore_abs_bound q k (Em.transpose.mul En) (2 * ε * ε) hB3.1 hB3.2
  have htri1 := ratAbs_add_le
    (relScore q k (Em.transpose.mul RphN) + relScore q k (RphM.transpose.mul En))
    (relScore q k (Em.transpose.mul En))
  have htri2 := ratAbs_add_le
    (relScore q k (Em.transpose.mul RphN))
    (relScore q k (RphM.transpose.mul En))
  have htot := Rat.le_trans htri1 (rat_add_le_add (Rat.le_trans htri2 (rat_add_le_add hs1 hs2)) hs3)
  have heq : 2 * ε * 1 * l1Norm2 q * l1Norm2 k + 2 * 1 * ε * l1Norm2 q * l1Norm2 k +
      2 * ε * ε * l1Norm2 q * l1Norm2 k =
      (4 * ε + 2 * ε * ε) * l1Norm2 q * l1Norm2 k := by grind
  rw [heq] at htot
  exact htot

/-! ### Headline Theorem 5: `relative_position_factorization_error_decomposition` -/

theorem relative_position_factorization_error_decomposition :
    (∀ (q k : Rat × Rat) (Rm Rn : Rot2),
      rotScore q k Rm Rn = relScore q k (Rm.transpose.mul Rn)) ∧
    (∀ (q k : Rat × Rat) (RphM RphN Rm Rn Rrel : Rot2),
      let Em := Rm.sub RphM
      let En := Rn.sub RphN
      rotScore q k Rm Rn - relScore q k Rrel =
        (rotScore q k RphM RphN - relScore q k Rrel) +
        (relScore q k (Em.transpose.mul RphN) +
         relScore q k (RphM.transpose.mul En) +
         relScore q k (Em.transpose.mul En))) ∧
    (∀ (h : Nat) (q k : Fin h → Rat × Rat) (RphM RphN Rm Rn Rrel : Fin h → Rot2),
      finSum (fun i => rotScore (q i) (k i) (Rm i) (Rn i) - relScore (q i) (k i) (Rrel i)) =
        finSum (fun i => rotScore (q i) (k i) (RphM i) (RphN i) - relScore (q i) (k i) (Rrel i)) +
        finSum (fun i =>
          relScore (q i) (k i) ((Rm i).sub (RphM i) |>.transpose.mul (RphN i)) +
          relScore (q i) (k i) ((RphM i).transpose.mul ((Rn i).sub (RphN i))) +
          relScore (q i) (k i) ((Rm i).sub (RphM i) |>.transpose.mul ((Rn i).sub (RphN i))))) ∧
    (∀ (q k : Rat × Rat) (RphM RphN Rm Rn Rrel : Rot2) (ε : Rat),
      RphM.transpose.mul RphN = Rrel →
      ratAbs RphM.c ≤ 1 → ratAbs RphM.s ≤ 1 →
      ratAbs RphN.c ≤ 1 → ratAbs RphN.s ≤ 1 →
      ratAbs (Rm.sub RphM).c ≤ ε → ratAbs (Rm.sub RphM).s ≤ ε →
      ratAbs (Rn.sub RphN).c ≤ ε → ratAbs (Rn.sub RphN).s ≤ ε →
      ratAbs (rotScore q k Rm Rn - relScore q k Rrel) ≤
        (4 * ε + 2 * ε * ε) * l1Norm2 q * l1Norm2 k) ∧
    (∀ (Rfreeze : Rot2), Rfreeze.c * Rfreeze.c + Rfreeze.s * Rfreeze.s = 1 →
      ratAbs (rotScore (1, 0) (1, 0) Rfreeze Rfreeze - relScore (1, 0) (1, 0) ⟨0, 1⟩) = 1 ∧
      ratAbs (rotScore (1, 0) (1, 0) Rfreeze Rfreeze - relScore (1, 0) (1, 0) ⟨-1, 0⟩) = 2 ∧
      (4 * (1 / 32 : Rat) + 2 * (1 / 32) * (1 / 32) = 65 / 512) ∧
      (65 / 512 : Rat) < 1 ∧
      (4 * (1 / 8 : Rat) + 2 * (1 / 8) * (1 / 8) = 17 / 32) ∧
      (17 / 32 : Rat) < 1) := by
  refine ⟨rotScore_eq_relScore, rotScore_error_decomp, ?_, exact_phase_quantized_rot_bound, ?_⟩
  · intro h q k RphM RphN Rm Rn Rrel
    rw [← finSum_add]
    apply finSum_congr
    intro i
    exact rotScore_error_decomp (q i) (k i) (RphM i) (RphN i) (Rm i) (Rn i) (Rrel i)
  · intro Rfreeze hunit
    have hself : rotScore (1, 0) (1, 0) Rfreeze Rfreeze = 1 := by
      unfold rotScore dot2 Rot2.apply
      grind
    have hq90 : relScore (1, 0) (1, 0) ⟨0, 1⟩ = 0 := by
      unfold relScore dot2 Rot2.apply; grind
    have hq180 : relScore (1, 0) (1, 0) ⟨-1, 0⟩ = -1 := by
      unfold relScore dot2 Rot2.apply; grind
    rw [hself, hq90, hq180]
    have h1 : ratAbs ((1 : Rat) - 0) = 1 := by
      have : (1 : Rat) - 0 = 1 := by grind
      rw [this, ratAbs_of_nonneg (by decide)]
    have h2 : ratAbs ((1 : Rat) - (-1)) = 2 := by
      have : (1 : Rat) - (-1) = 2 := by grind
      rw [this, ratAbs_of_nonneg (by decide)]
    have hlt1 : (65 / 512 : Rat) < 1 := by
      apply rat_lt_of_sub_pos
      have heq : (1 : Rat) - 65 / 512 = 447 / 512 := by grind
      rw [heq]
      have hmul : (0 : Rat) * 512 < (447 / 512 : Rat) * 512 := by
        rw [Rat.zero_mul, rat_div_mul_cancel (by decide)]; decide
      cases Rat.le_total (a := (0 : Rat)) (b := (447 / 512 : Rat)) with
      | inl hge =>
        have hne : (447 / 512 : Rat) ≠ 0 := by intro h0; rw [h0, Rat.zero_mul] at hmul; exact Rat.not_le.mpr hmul Rat.le_refl
        exact Rat.lt_of_le_of_ne hge (Ne.symm hne)
      | inr hle =>
        exact False.elim (Rat.not_le.mpr hmul (rat_mul_le_mul_of_nonneg_right hle (by decide)))
    have hlt2 : (17 / 32 : Rat) < 1 := by
      apply rat_lt_of_sub_pos
      have heq : (1 : Rat) - 17 / 32 = 15 / 32 := by grind
      rw [heq]
      have hmul : (0 : Rat) * 32 < (15 / 32 : Rat) * 32 := by
        rw [Rat.zero_mul, rat_div_mul_cancel (by decide)]; decide
      cases Rat.le_total (a := (0 : Rat)) (b := (15 / 32 : Rat)) with
      | inl hge =>
        have hne : (15 / 32 : Rat) ≠ 0 := by intro h0; rw [h0, Rat.zero_mul] at hmul; exact Rat.not_le.mpr hmul Rat.le_refl
        exact Rat.lt_of_le_of_ne hge (Ne.symm hne)
      | inr hle =>
        exact False.elim (Rat.not_le.mpr hmul (rat_mul_le_mul_of_nonneg_right hle (by decide)))
    exact ⟨h1, h2, by grind, hlt1, by grind, hlt2⟩

/-! ### Headline Theorem 6: `dyadic_cayley_relative_composition_exact` -/

theorem cayley_unit_circle (t : Rat) :
    cayleyCos t * cayleyCos t + cayleySin t * cayleySin t = 1 := by
  unfold cayleyCos cayleySin
  have hd : 1 + t * t ≠ 0 := rat_one_add_sq_ne_zero t
  have hd2 : (1 + t * t) * (1 + t * t) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hd h
    | inr h => exact hd h
  have hmul : (((1 - t * t) / (1 + t * t)) * ((1 - t * t) / (1 + t * t)) +
      ((2 * t) / (1 + t * t)) * ((2 * t) / (1 + t * t))) * ((1 + t * t) * (1 + t * t)) =
      (1 + t * t) * (1 + t * t) := by
    have h1 : ((1 - t * t) / (1 + t * t)) * ((1 - t * t) / (1 + t * t)) *
        ((1 + t * t) * (1 + t * t)) = (1 - t * t) * (1 - t * t) := by
      have ha : ((1 - t * t) / (1 + t * t)) * ((1 - t * t) / (1 + t * t)) *
          ((1 + t * t) * (1 + t * t)) =
          (((1 - t * t) / (1 + t * t)) * (1 + t * t)) *
          (((1 - t * t) / (1 + t * t)) * (1 + t * t)) := by grind
      rw [ha, rat_div_mul_cancel hd]
    have h2 : ((2 * t) / (1 + t * t)) * ((2 * t) / (1 + t * t)) *
        ((1 + t * t) * (1 + t * t)) = (2 * t) * (2 * t) := by
      have ha : ((2 * t) / (1 + t * t)) * ((2 * t) / (1 + t * t)) *
          ((1 + t * t) * (1 + t * t)) =
          (((2 * t) / (1 + t * t)) * (1 + t * t)) *
          (((2 * t) / (1 + t * t)) * (1 + t * t)) := by grind
      rw [ha, rat_div_mul_cancel hd]
    have hdist : (((1 - t * t) / (1 + t * t)) * ((1 - t * t) / (1 + t * t)) +
        ((2 * t) / (1 + t * t)) * ((2 * t) / (1 + t * t))) * ((1 + t * t) * (1 + t * t)) =
        ((1 - t * t) / (1 + t * t)) * ((1 - t * t) / (1 + t * t)) * ((1 + t * t) * (1 + t * t)) +
        ((2 * t) / (1 + t * t)) * ((2 * t) / (1 + t * t)) * ((1 + t * t) * (1 + t * t)) := by grind
    rw [hdist, h1, h2]
    grind
  have hsub : ((((1 - t * t) / (1 + t * t)) * ((1 - t * t) / (1 + t * t)) +
      ((2 * t) / (1 + t * t)) * ((2 * t) / (1 + t * t))) - 1) * ((1 + t * t) * (1 + t * t)) = 0 := by
    grind
  cases Rat.mul_eq_zero.mp hsub with
  | inl h => grind
  | inr h => exact absurd h hd2

theorem cayleyRot_transpose (t : Rat) : (cayleyRot t).transpose = cayleyRot (-t) := by
  unfold cayleyRot Rot2.transpose cayleyCos cayleySin
  simp only [Rot2.mk.injEq]
  constructor
  · have h1 : (-t) * (-t) = t * t := by grind
    rw [h1]
  · have h1 : (-t) * (-t) = t * t := by grind
    have h2 : 2 * (-t) = -(2 * t) := by grind
    rw [h1, h2]
    rw [Rat.div_def, Rat.div_def]
    grind

theorem cayleyRot_orthog_left (t : Rat) :
    (cayleyRot t).transpose.mul (cayleyRot t) = Rot2.id := by
  unfold cayleyRot Rot2.transpose Rot2.mul Rot2.id
  simp only [Rot2.mk.injEq]
  constructor
  · have h := cayley_unit_circle t
    grind
  · grind

theorem cayleyRot_orthog_right (t : Rat) :
    (cayleyRot t).mul (cayleyRot t).transpose = Rot2.id := by
  unfold cayleyRot Rot2.transpose Rot2.mul Rot2.id
  simp only [Rot2.mk.injEq]
  constructor
  · have h := cayley_unit_circle t
    grind
  · grind

theorem cayleyRot_mul (t1 t2 : Rat) (h : t1 * t2 ≠ 1) :
    (cayleyRot t1).mul (cayleyRot t2) = cayleyRot ((t1 + t2) / (1 - t1 * t2)) := by
  have hd1 : 1 + t1 * t1 ≠ 0 := rat_one_add_sq_ne_zero t1
  have hd2 : 1 + t2 * t2 ≠ 0 := rat_one_add_sq_ne_zero t2
  have hd12 : 1 - t1 * t2 ≠ 0 := by
    intro h0; exact h (by grind)
  let u := (t1 + t2) / (1 - t1 * t2)
  have hdu : 1 + u * u ≠ 0 := rat_one_add_sq_ne_zero u
  have hu_mul : u * (1 - t1 * t2) = t1 + t2 := rat_div_mul_cancel hd12
  have hden_prod : (1 + t1 * t1) * (1 + t2 * t2) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl ha => exact hd1 ha
    | inr hb => exact hd2 hb
  have h12_sq : (1 - t1 * t2) * (1 - t1 * t2) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl ha => exact hd12 ha
    | inr hb => exact hd12 hb
  -- Cross-multiply both components by (1 + t1^2)(1 + t2^2)(1 + u^2)(1 - t1*t2)^2
  have hu_den_eq : (1 + u * u) * ((1 - t1 * t2) * (1 - t1 * t2)) =
      (1 + t1 * t1) * (1 + t2 * t2) := by
    have hsq : (u * u) * ((1 - t1 * t2) * (1 - t1 * t2)) = (t1 + t2) * (t1 + t2) := by
      have ha : (u * u) * ((1 - t1 * t2) * (1 - t1 * t2)) =
          (u * (1 - t1 * t2)) * (u * (1 - t1 * t2)) := by grind
      rw [ha, hu_mul]
    have hdist : (1 + u * u) * ((1 - t1 * t2) * (1 - t1 * t2)) =
        (1 - t1 * t2) * (1 - t1 * t2) + (u * u) * ((1 - t1 * t2) * (1 - t1 * t2)) := by grind
    rw [hdist, hsq]
    grind
  have hu_num_c : (1 - u * u) * ((1 - t1 * t2) * (1 - t1 * t2)) =
      (1 - t1 * t1) * (1 - t2 * t2) - (2 * t1) * (2 * t2) := by
    have hsq : (u * u) * ((1 - t1 * t2) * (1 - t1 * t2)) = (t1 + t2) * (t1 + t2) := by
      have ha : (u * u) * ((1 - t1 * t2) * (1 - t1 * t2)) =
          (u * (1 - t1 * t2)) * (u * (1 - t1 * t2)) := by grind
      rw [ha, hu_mul]
    have hdist : (1 - u * u) * ((1 - t1 * t2) * (1 - t1 * t2)) =
        (1 - t1 * t2) * (1 - t1 * t2) - (u * u) * ((1 - t1 * t2) * (1 - t1 * t2)) := by grind
    rw [hdist, hsq]
    grind
  have hu_num_s : (2 * u) * ((1 - t1 * t2) * (1 - t1 * t2)) =
      (2 * t1) * (1 - t2 * t2) + (1 - t1 * t1) * (2 * t2) := by
    have ha : (2 * u) * ((1 - t1 * t2) * (1 - t1 * t2)) =
        2 * (u * (1 - t1 * t2)) * (1 - t1 * t2) := by grind
    rw [ha, hu_mul]
    grind
  unfold cayleyRot Rot2.mul cayleyCos cayleySin
  simp only [Rot2.mk.injEq]
  constructor
  · apply Eq.symm
    apply (rat_div_eq_iff hdu).mpr
    -- Goal: 1 - u * u = (c1 * c2 - s1 * s2) * (1 + u * u)
    -- Multiply both sides by (1 - t1*t2)^2
    have hscaled : ((1 - u * u) - (((1 - t1 * t1) / (1 + t1 * t1)) * ((1 - t2 * t2) / (1 + t2 * t2)) -
        ((2 * t1) / (1 + t1 * t1)) * ((2 * t2) / (1 + t2 * t2))) * (1 + u * u)) *
        ((1 - t1 * t2) * (1 - t1 * t2)) = 0 := by
      have hdist : ((1 - u * u) - (((1 - t1 * t1) / (1 + t1 * t1)) * ((1 - t2 * t2) / (1 + t2 * t2)) -
          ((2 * t1) / (1 + t1 * t1)) * ((2 * t2) / (1 + t2 * t2))) * (1 + u * u)) *
          ((1 - t1 * t2) * (1 - t1 * t2)) =
          (1 - u * u) * ((1 - t1 * t2) * (1 - t1 * t2)) -
          (((1 - t1 * t1) / (1 + t1 * t1)) * ((1 - t2 * t2) / (1 + t2 * t2)) -
           ((2 * t1) / (1 + t1 * t1)) * ((2 * t2) / (1 + t2 * t2))) *
          ((1 + u * u) * ((1 - t1 * t2) * (1 - t1 * t2))) := by grind
      rw [hdist, hu_num_c, hu_den_eq]
      have hc12 : (((1 - t1 * t1) / (1 + t1 * t1)) * ((1 - t2 * t2) / (1 + t2 * t2))) *
          ((1 + t1 * t1) * (1 + t2 * t2)) = (1 - t1 * t1) * (1 - t2 * t2) := by
        have ha : (((1 - t1 * t1) / (1 + t1 * t1)) * ((1 - t2 * t2) / (1 + t2 * t2))) *
            ((1 + t1 * t1) * (1 + t2 * t2)) =
            (((1 - t1 * t1) / (1 + t1 * t1)) * (1 + t1 * t1)) *
            (((1 - t2 * t2) / (1 + t2 * t2)) * (1 + t2 * t2)) := by grind
        rw [ha, rat_div_mul_cancel hd1, rat_div_mul_cancel hd2]
      have hs12 : (((2 * t1) / (1 + t1 * t1)) * ((2 * t2) / (1 + t2 * t2))) *
          ((1 + t1 * t1) * (1 + t2 * t2)) = (2 * t1) * (2 * t2) := by
        have ha : (((2 * t1) / (1 + t1 * t1)) * ((2 * t2) / (1 + t2 * t2))) *
            ((1 + t1 * t1) * (1 + t2 * t2)) =
            (((2 * t1) / (1 + t1 * t1)) * (1 + t1 * t1)) *
            (((2 * t2) / (1 + t2 * t2)) * (1 + t2 * t2)) := by grind
        rw [ha, rat_div_mul_cancel hd1, rat_div_mul_cancel hd2]
      grind
    cases Rat.mul_eq_zero.mp hscaled with
    | inl h0 => grind
    | inr h0 => exact absurd h0 h12_sq
  · apply Eq.symm
    apply (rat_div_eq_iff hdu).mpr
    have hscaled : ((2 * u) - (((2 * t1) / (1 + t1 * t1)) * ((1 - t2 * t2) / (1 + t2 * t2)) +
        ((1 - t1 * t1) / (1 + t1 * t1)) * ((2 * t2) / (1 + t2 * t2))) * (1 + u * u)) *
        ((1 - t1 * t2) * (1 - t1 * t2)) = 0 := by
      have hdist : ((2 * u) - (((2 * t1) / (1 + t1 * t1)) * ((1 - t2 * t2) / (1 + t2 * t2)) +
          ((1 - t1 * t1) / (1 + t1 * t1)) * ((2 * t2) / (1 + t2 * t2))) * (1 + u * u)) *
          ((1 - t1 * t2) * (1 - t1 * t2)) =
          (2 * u) * ((1 - t1 * t2) * (1 - t1 * t2)) -
          (((2 * t1) / (1 + t1 * t1)) * ((1 - t2 * t2) / (1 + t2 * t2)) +
           ((1 - t1 * t1) / (1 + t1 * t1)) * ((2 * t2) / (1 + t2 * t2))) *
          ((1 + u * u) * ((1 - t1 * t2) * (1 - t1 * t2))) := by grind
      rw [hdist, hu_num_s, hu_den_eq]
      have hsc : (((2 * t1) / (1 + t1 * t1)) * ((1 - t2 * t2) / (1 + t2 * t2))) *
          ((1 + t1 * t1) * (1 + t2 * t2)) = (2 * t1) * (1 - t2 * t2) := by
        have ha : (((2 * t1) / (1 + t1 * t1)) * ((1 - t2 * t2) / (1 + t2 * t2))) *
            ((1 + t1 * t1) * (1 + t2 * t2)) =
            (((2 * t1) / (1 + t1 * t1)) * (1 + t1 * t1)) *
            (((1 - t2 * t2) / (1 + t2 * t2)) * (1 + t2 * t2)) := by grind
        rw [ha, rat_div_mul_cancel hd1, rat_div_mul_cancel hd2]
      have hcs : (((1 - t1 * t1) / (1 + t1 * t1)) * ((2 * t2) / (1 + t2 * t2))) *
          ((1 + t1 * t1) * (1 + t2 * t2)) = (1 - t1 * t1) * (2 * t2) := by
        have ha : (((1 - t1 * t1) / (1 + t1 * t1)) * ((2 * t2) / (1 + t2 * t2))) *
            ((1 + t1 * t1) * (1 + t2 * t2)) =
            (((1 - t1 * t1) / (1 + t1 * t1)) * (1 + t1 * t1)) *
            (((2 * t2) / (1 + t2 * t2)) * (1 + t2 * t2)) := by grind
        rw [ha, rat_div_mul_cancel hd1, rat_div_mul_cancel hd2]
      grind
    cases Rat.mul_eq_zero.mp hscaled with
    | inl h0 => grind
    | inr h0 => exact absurd h0 h12_sq

theorem dyadic_cayley_relative_composition_exact :
    (cayleyRot 0 = Rot2.id) ∧
    (∀ t : Rat, (cayleyRot t).transpose = cayleyRot (-t)) ∧
    (∀ t : Rat,
      (cayleyRot t).transpose.mul (cayleyRot t) = Rot2.id ∧
      (cayleyRot t).mul (cayleyRot t).transpose = Rot2.id) ∧
    (∀ (t : Rat) (v : Rat × Rat),
      normSq2 ((cayleyRot t).apply v) = normSq2 v) ∧
    (∀ t1 t2 : Rat, t1 * t2 ≠ 1 →
      (cayleyRot t1).mul (cayleyRot t2) = cayleyRot ((t1 + t2) / (1 - t1 * t2))) ∧
    (∀ t1 t2 : Rat, t1 * t2 ≠ -1 →
      (cayleyRot t1).transpose.mul (cayleyRot t2) = cayleyRot ((t2 - t1) / (1 + t1 * t2))) := by
  refine ⟨?_, cayleyRot_transpose, fun t => ⟨cayleyRot_orthog_left t, cayleyRot_orthog_right t⟩,
          ?_, cayleyRot_mul, ?_⟩
  · unfold cayleyRot cayleyCos cayleySin Rot2.id
    simp only [Rot2.mk.injEq]
    constructor <;> grind
  · intro t v
    unfold normSq2 Rot2.apply cayleyRot
    have hunit := cayley_unit_circle t
    have hfactor : (cayleyCos t * v.1 - cayleySin t * v.2) * (cayleyCos t * v.1 - cayleySin t * v.2) +
        (cayleySin t * v.1 + cayleyCos t * v.2) * (cayleySin t * v.1 + cayleyCos t * v.2) =
        (cayleyCos t * cayleyCos t + cayleySin t * cayleySin t) * (v.1 * v.1 + v.2 * v.2) := by
      grind
    rw [hfactor, hunit, Rat.one_mul]
  · intro t1 t2 hne
    rw [cayleyRot_transpose]
    have hne' : (-t1) * t2 ≠ 1 := by
      intro h0; exact hne (by grind)
    rw [cayleyRot_mul (-t1) t2 hne']
    have heq : (-t1 + t2) / (1 - (-t1) * t2) = (t2 - t1) / (1 + t1 * t2) := by
      have h1 : -t1 + t2 = t2 - t1 := by grind
      have h2 : 1 - (-t1) * t2 = 1 + t1 * t2 := by grind
      rw [h1, h2]
    rw [heq]

end RopeQ32Coprime
