/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlibiBitsplitKulisch.RatOrder

/-!
# Pillar 2: Bilinear `INT_b` Bit-Split Crossovers, Absmax Super-Outlier Reversal & `MXFP_b` Parity

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. Exact finite-level symmetric `INT_b` bilinear bit-split crossover law (`125/22`, `24025/92`, `10143/2350`).
2. Absmax-pinned super-outlier reversal theorem (`W5A3` beats `W4A4`, `W4A2` beats `W3A3`).
3. Microscaling `MXFP5-E2M2 × MXFP7-E3M3` (`W5A7`) mantissa-parity dominance over `MXFP6-E3M2 × MXFP6-E3M2` (`W6A6`).
-/

namespace AlibiBitsplitKulisch

/-- For `b ≥ 2`, `intQ b = 2^{b-1} - 1 ≥ 1`. -/
theorem intQ_pos {b : Nat} (hb : 2 ≤ b) : 0 < intQ b := by
  unfold intQ
  have h1 : 2 ^ 1 ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- Strict monotonicity of `intQ`: `intQ b < intQ (b + 1)` for `b ≥ 2`. -/
theorem intQ_lt_succ {b : Nat} (hb : 2 ≤ b) : intQ b < intQ (b + 1) := by
  unfold intQ
  have hsub : b + 1 - 1 = (b - 1) + 1 := by omega
  rw [hsub, Nat.pow_succ]
  have hpos : 0 < 2 ^ (b - 1) := Nat.pow_pos (by decide)
  omega

/-- Strict anti-monotonicity of `intInvQ2`: `intInvQ2 (b + 1) < intInvQ2 b` for `b ≥ 2`. -/
theorem intInvQ2_succ_lt {b : Nat} (hb : 2 ≤ b) : intInvQ2 (b + 1) < intInvQ2 b := by
  unfold intInvQ2
  have hq0 : 0 < intQ b := intQ_pos hb
  have hlt : intQ b < intQ (b + 1) := intQ_lt_succ hb
  have hsq_pos1 : 0 < intQ b * intQ b := Nat.mul_pos hq0 hq0
  have hsq_pos2 : 0 < intQ (b + 1) * intQ (b + 1) :=
    Nat.mul_pos (Nat.lt_trans hq0 hlt) (Nat.lt_trans hq0 hlt)
  have hsq_lt : intQ b * intQ b < intQ (b + 1) * intQ (b + 1) :=
    Nat.mul_lt_mul_of_lt_of_lt hlt hlt
  have hr1 : (0 : Rat) < ((intQ b * intQ b : Nat) : Rat) := rat_natCast_pos hsq_pos1
  have hr2 : (0 : Rat) < ((intQ (b + 1) * intQ (b + 1) : Nat) : Rat) := rat_natCast_pos hsq_pos2
  have hrlt : ((intQ b * intQ b : Nat) : Rat) < ((intQ (b + 1) * intQ (b + 1) : Nat) : Rat) :=
    rat_natCast_lt hsq_lt
  apply rat_lt_of_mul_pos_right (rat_mul_pos hr1 hr2)
  have hL : (1 / ((intQ (b + 1) * intQ (b + 1) : Nat) : Rat)) *
      (((intQ b * intQ b : Nat) : Rat) * ((intQ (b + 1) * intQ (b + 1) : Nat) : Rat)) =
      ((intQ b * intQ b : Nat) : Rat) := by
    have hrw : (1 / ((intQ (b + 1) * intQ (b + 1) : Nat) : Rat)) *
        (((intQ b * intQ b : Nat) : Rat) * ((intQ (b + 1) * intQ (b + 1) : Nat) : Rat)) =
        ((1 / ((intQ (b + 1) * intQ (b + 1) : Nat) : Rat)) *
          ((intQ (b + 1) * intQ (b + 1) : Nat) : Rat)) * ((intQ b * intQ b : Nat) : Rat) := by
      grind
    rw [hrw, rat_div_mul_cancel (Rat.ne_of_gt hr2), Rat.one_mul]
  have hR : (1 / ((intQ b * intQ b : Nat) : Rat)) *
      (((intQ b * intQ b : Nat) : Rat) * ((intQ (b + 1) * intQ (b + 1) : Nat) : Rat)) =
      ((intQ (b + 1) * intQ (b + 1) : Nat) : Rat) := by
    rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hr1), Rat.one_mul]
  rw [hL, hR]
  exact hrlt

/-- Universal finite-level bilinear `INT_b` bit-split crossover equivalence:
    `(bW - 1, bX + 1)` strictly beats `(bW, bX)` iff `R = cX / cW > R^*(bW, bX)`. -/
theorem bilinearIntMSE_step_lt_iff {bW bX : Nat} (_hbW : 3 ≤ bW) (hbX : 2 ≤ bX)
    {cW cX : Rat} (hcW : (0 : Rat) < cW) :
    bilinearIntMSE (bW - 1) (bX + 1) cW cX < bilinearIntMSE bW bX cW cX ↔
      bilinearCrossoverR bW bX < cX / cW := by
  have hden_pos : (0 : Rat) < intInvQ2 bX - intInvQ2 (bX + 1) :=
    rat_sub_pos (intInvQ2_succ_lt hbX)
  unfold bilinearIntMSE bilinearCrossoverR
  constructor
  · intro hlt
    have hdiff : (0 : Rat) < (cW * intInvQ2 bW + cX * intInvQ2 bX) -
        (cW * intInvQ2 (bW - 1) + cX * intInvQ2 (bX + 1)) := rat_sub_pos hlt
    have hrearr : cW * (intInvQ2 (bW - 1) - intInvQ2 bW) <
        cX * (intInvQ2 bX - intInvQ2 (bX + 1)) := by
      apply rat_lt_of_sub_pos
      have heq : cX * (intInvQ2 bX - intInvQ2 (bX + 1)) -
          cW * (intInvQ2 (bW - 1) - intInvQ2 bW) =
          (cW * intInvQ2 bW + cX * intInvQ2 bX) -
          (cW * intInvQ2 (bW - 1) + cX * intInvQ2 (bX + 1)) := by grind
      rw [heq]; exact hdiff
    apply rat_div_lt_of_mul_lt hden_pos
    apply rat_lt_of_mul_pos_right hcW
    have hR : (cX / cW) * (intInvQ2 bX - intInvQ2 (bX + 1)) * cW =
        cX * (intInvQ2 bX - intInvQ2 (bX + 1)) := by
      have hrw : (cX / cW) * (intInvQ2 bX - intInvQ2 (bX + 1)) * cW =
          ((cX / cW) * cW) * (intInvQ2 bX - intInvQ2 (bX + 1)) := by grind
      rw [hrw, rat_div_mul_cancel (Rat.ne_of_gt hcW)]
    rw [hR, Rat.mul_comm (intInvQ2 (bW - 1) - intInvQ2 bW) cW]
    exact hrearr
  · intro hgt
    have hmul1 : intInvQ2 (bW - 1) - intInvQ2 bW <
        (cX / cW) * (intInvQ2 bX - intInvQ2 (bX + 1)) := by
      have h := rat_mul_lt_mul_of_pos_right hgt hden_pos
      rw [rat_div_mul_cancel (Rat.ne_of_gt hden_pos)] at h
      exact h
    have hmul2 := rat_mul_lt_mul_of_pos_left hmul1 hcW
    have hR : cW * ((cX / cW) * (intInvQ2 bX - intInvQ2 (bX + 1))) =
        cX * (intInvQ2 bX - intInvQ2 (bX + 1)) := by
      rw [← Rat.mul_assoc, rat_mul_div_cancel (Rat.ne_of_gt hcW)]
    rw [hR] at hmul2
    apply rat_lt_of_sub_pos
    have heq : (cW * intInvQ2 bW + cX * intInvQ2 bX) -
        (cW * intInvQ2 (bW - 1) + cX * intInvQ2 (bX + 1)) =
        cX * (intInvQ2 bX - intInvQ2 (bX + 1)) -
        cW * (intInvQ2 (bW - 1) - intInvQ2 bW) := by grind
    rw [heq]
    exact rat_sub_pos hmul2

/-- Headline Theorem 2 (`bilinear_int_asymmetric_bitsplit_crossovers_exact`):
    Universal exact finite-level symmetric `INT_b` bit-split crossover equivalence and
    exact rational thresholds:
    - `W4A4 -> W3A5` iff `R > 125/22` (`1.42x` harder than asymptotic `4`),
    - `W3A5 -> W2A6` iff `R > 24025/92` (`4.08x` harder than asymptotic `64`),
    - `W6A6 -> W5A7` iff `R > 10143/2350` (`1.08x` harder than asymptotic `4`),
    plus `W3A3 -> W2A4` (`49/5`) and `W5A5 -> W4A6` (`10571/2254`). -/
theorem rat_div_eq_div_of_nat {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) (h : a * d = c * b) :
    (a : Rat) / (b : Rat) = (c : Rat) / (d : Rat) := by
  have hbr : (0 : Rat) < (b : Rat) := rat_natCast_pos hb
  have hdr : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hne : (b : Rat) * (d : Rat) ≠ 0 := Rat.ne_of_gt (rat_mul_pos hbr hdr)
  have hL : ((a : Rat) / (b : Rat)) * ((b : Rat) * (d : Rat)) = ((a * d : Nat) : Rat) := by
    rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hbr), Rat.natCast_mul]
  have hR : ((c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) = ((c * b : Nat) : Rat) := by
    have hrw : ((c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) =
        (((c : Rat) / (d : Rat)) * (d : Rat)) * (b : Rat) := by grind
    rw [hrw, rat_div_mul_cancel (Rat.ne_of_gt hdr), Rat.natCast_mul]
  have hsub : ((a : Rat) / (b : Rat) - (c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) = 0 := by
    have hrw : ((a : Rat) / (b : Rat) - (c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) =
        ((a : Rat) / (b : Rat)) * ((b : Rat) * (d : Rat)) -
        ((c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) := by grind
    rw [hrw, hL, hR, h]; grind
  cases Rat.mul_eq_zero.mp hsub with
  | inl h0 => grind
  | inr h0 => exact False.elim (hne h0)

theorem inv_sub_inv_nat {a b : Nat} (ha : 0 < a) (hab : a < b) :
    (1 : Rat) / (a : Rat) - (1 : Rat) / (b : Rat) = ((b - a : Nat) : Rat) / ((a * b : Nat) : Rat) := by
  have har : (0 : Rat) < (a : Rat) := rat_natCast_pos ha
  have hbr : (0 : Rat) < (b : Rat) := rat_natCast_pos (Nat.lt_trans ha hab)
  have habr : (0 : Rat) < ((a * b : Nat) : Rat) := rat_natCast_pos (Nat.mul_pos ha (Nat.lt_trans ha hab))
  have hne : ((a * b : Nat) : Rat) ≠ 0 := Rat.ne_of_gt habr
  have hL : ((1 : Rat) / (a : Rat) - (1 : Rat) / (b : Rat)) * ((a * b : Nat) : Rat) =
      ((b - a : Nat) : Rat) := by
    rw [Rat.natCast_mul]
    have hrw : ((1 : Rat) / (a : Rat) - (1 : Rat) / (b : Rat)) * ((a : Rat) * (b : Rat)) =
        ((1 : Rat) / (a : Rat) * (a : Rat)) * (b : Rat) -
        ((1 : Rat) / (b : Rat) * (b : Rat)) * (a : Rat) := by grind
    rw [hrw, rat_div_mul_cancel (Rat.ne_of_gt har), rat_div_mul_cancel (Rat.ne_of_gt hbr),
        Rat.one_mul, Rat.one_mul]
    have hnat : b = (b - a) + a := (Nat.sub_add_cancel (Nat.le_of_lt hab)).symm
    have hcast : (b : Rat) = ((b - a : Nat) : Rat) + (a : Rat) := by
      have h1 : ((b : Nat) : Rat) = (((b - a) + a : Nat) : Rat) := congrArg Nat.cast hnat
      rw [h1, Rat.natCast_add]
    rw [hcast]; grind
  have hR : (((b - a : Nat) : Rat) / ((a * b : Nat) : Rat)) * ((a * b : Nat) : Rat) =
      ((b - a : Nat) : Rat) := rat_div_mul_cancel hne
  have hsub : (((1 : Rat) / (a : Rat) - (1 : Rat) / (b : Rat)) -
      (((b - a : Nat) : Rat) / ((a * b : Nat) : Rat))) * ((a * b : Nat) : Rat) = 0 := by
    have hrw : (((1 : Rat) / (a : Rat) - (1 : Rat) / (b : Rat)) -
        (((b - a : Nat) : Rat) / ((a * b : Nat) : Rat))) * ((a * b : Nat) : Rat) =
        ((1 : Rat) / (a : Rat) - (1 : Rat) / (b : Rat)) * ((a * b : Nat) : Rat) -
        (((b - a : Nat) : Rat) / ((a * b : Nat) : Rat)) * ((a * b : Nat) : Rat) := by grind
    rw [hrw, hL, hR]; grind
  cases Rat.mul_eq_zero.mp hsub with
  | inl h0 => grind
  | inr h0 => exact False.elim (hne h0)

theorem div_div_div_nat {a b c d : Nat} (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ((a : Rat) / (b : Rat)) / ((c : Rat) / (d : Rat)) = ((a * d : Nat) : Rat) / ((b * c : Nat) : Rat) := by
  have hbr : (0 : Rat) < (b : Rat) := rat_natCast_pos hb
  have hcr : (0 : Rat) < (c : Rat) := rat_natCast_pos hc
  have hdr : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  have hcd : (c : Rat) / (d : Rat) ≠ 0 := Rat.ne_of_gt (rat_div_pos hcr hdr)
  have hbc : ((b * c : Nat) : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (Nat.mul_pos hb hc))
  have hne : ((c : Rat) / (d : Rat)) * ((b * c : Nat) : Rat) ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact hcd h
    | inr h => exact hbc h
  have hL : (((a : Rat) / (b : Rat)) / ((c : Rat) / (d : Rat))) *
      (((c : Rat) / (d : Rat)) * ((b * c : Nat) : Rat)) = (a : Rat) * (c : Rat) := by
    rw [← Rat.mul_assoc, rat_div_mul_cancel hcd, Rat.natCast_mul, ← Rat.mul_assoc,
        rat_div_mul_cancel (Rat.ne_of_gt hbr)]
  have hR : (((a * d : Nat) : Rat) / ((b * c : Nat) : Rat)) *
      (((c : Rat) / (d : Rat)) * ((b * c : Nat) : Rat)) = (a : Rat) * (c : Rat) := by
    have hrw : (((a * d : Nat) : Rat) / ((b * c : Nat) : Rat)) *
        (((c : Rat) / (d : Rat)) * ((b * c : Nat) : Rat)) =
        ((((a * d : Nat) : Rat) / ((b * c : Nat) : Rat)) * ((b * c : Nat) : Rat)) *
        ((c : Rat) / (d : Rat)) := by grind
    rw [hrw, rat_div_mul_cancel hbc, Rat.natCast_mul]
    have hrw2 : ((a : Rat) * (d : Rat)) * ((c : Rat) / (d : Rat)) =
        (a : Rat) * ((d : Rat) * ((c : Rat) / (d : Rat))) := by grind
    rw [hrw2, rat_mul_div_cancel (Rat.ne_of_gt hdr)]
  have hsub : ((((a : Rat) / (b : Rat)) / ((c : Rat) / (d : Rat))) -
      (((a * d : Nat) : Rat) / ((b * c : Nat) : Rat))) *
      (((c : Rat) / (d : Rat)) * ((b * c : Nat) : Rat)) = 0 := by
    have hrw : ((((a : Rat) / (b : Rat)) / ((c : Rat) / (d : Rat))) -
        (((a * d : Nat) : Rat) / ((b * c : Nat) : Rat))) *
        (((c : Rat) / (d : Rat)) * ((b * c : Nat) : Rat)) =
        (((a : Rat) / (b : Rat)) / ((c : Rat) / (d : Rat))) *
          (((c : Rat) / (d : Rat)) * ((b * c : Nat) : Rat)) -
        (((a * d : Nat) : Rat) / ((b * c : Nat) : Rat)) *
          (((c : Rat) / (d : Rat)) * ((b * c : Nat) : Rat)) := by grind
    rw [hrw, hL, hR]; grind
  cases Rat.mul_eq_zero.mp hsub with
  | inl h0 => grind
  | inr h0 => exact False.elim (hne h0)

theorem bilinearCrossoverR_eq_nat_div {bW bX p q : Nat}
    (hbW : 3 ≤ bW) (hbX : 2 ≤ bX) (hq : 0 < q)
    (heq : ((intQ bW * intQ bW - intQ (bW - 1) * intQ (bW - 1)) *
            (intQ bX * intQ bX * (intQ (bX + 1) * intQ (bX + 1)))) * q =
           p * ((intQ (bW - 1) * intQ (bW - 1) * (intQ bW * intQ bW)) *
                (intQ (bX + 1) * intQ (bX + 1) - intQ bX * intQ bX))) :
    bilinearCrossoverR bW bX = (p : Rat) / (q : Rat) := by
  unfold bilinearCrossoverR intInvQ2
  have hqW0 : 0 < intQ (bW - 1) := intQ_pos (by omega)
  have hqWlt : intQ (bW - 1) < intQ bW := by
    have h := intQ_lt_succ (b := bW - 1) (by omega)
    have hsub : bW - 1 + 1 = bW := by omega
    rw [hsub] at h; exact h
  have hqX0 : 0 < intQ bX := intQ_pos hbX
  have hqXlt : intQ bX < intQ (bX + 1) := intQ_lt_succ hbX
  have hWsq_pos : 0 < intQ (bW - 1) * intQ (bW - 1) := Nat.mul_pos hqW0 hqW0
  have hWsq_lt : intQ (bW - 1) * intQ (bW - 1) < intQ bW * intQ bW :=
    Nat.mul_lt_mul_of_lt_of_lt hqWlt hqWlt
  have hXsq_pos : 0 < intQ bX * intQ bX := Nat.mul_pos hqX0 hqX0
  have hXsq_lt : intQ bX * intQ bX < intQ (bX + 1) * intQ (bX + 1) :=
    Nat.mul_lt_mul_of_lt_of_lt hqXlt hqXlt
  rw [inv_sub_inv_nat hWsq_pos hWsq_lt, inv_sub_inv_nat hXsq_pos hXsq_lt,
      div_div_div_nat (Nat.mul_pos hWsq_pos (Nat.lt_trans hWsq_pos hWsq_lt))
        (Nat.sub_pos_of_lt hXsq_lt) (Nat.mul_pos hXsq_pos (Nat.lt_trans hXsq_pos hXsq_lt))]
  exact rat_div_eq_div_of_nat
    (Nat.mul_pos (Nat.mul_pos hWsq_pos (Nat.lt_trans hWsq_pos hWsq_lt)) (Nat.sub_pos_of_lt hXsq_lt))
    hq heq

theorem rat_div_lt_div_of_nat {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) (h : a * d < c * b) :
    (a : Rat) / (b : Rat) < (c : Rat) / (d : Rat) := by
  have hbr : (0 : Rat) < (b : Rat) := rat_natCast_pos hb
  have hdr : (0 : Rat) < (d : Rat) := rat_natCast_pos hd
  apply rat_lt_of_mul_pos_right (rat_mul_pos hbr hdr)
  have hL : ((a : Rat) / (b : Rat)) * ((b : Rat) * (d : Rat)) = ((a * d : Nat) : Rat) := by
    rw [← Rat.mul_assoc, rat_div_mul_cancel (Rat.ne_of_gt hbr), Rat.natCast_mul]
  have hR : ((c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) = ((c * b : Nat) : Rat) := by
    have hrw : ((c : Rat) / (d : Rat)) * ((b : Rat) * (d : Rat)) =
        (((c : Rat) / (d : Rat)) * (d : Rat)) * (b : Rat) := by grind
    rw [hrw, rat_div_mul_cancel (Rat.ne_of_gt hdr), Rat.natCast_mul]
  rw [hL, hR]
  exact rat_natCast_lt h

theorem bilinear_int_asymmetric_bitsplit_crossovers_exact :
    (∀ (bW bX : Nat) (cW cX : Rat), 3 ≤ bW → 2 ≤ bX → (0 : Rat) < cW →
      (bilinearIntMSE (bW - 1) (bX + 1) cW cX < bilinearIntMSE bW bX cW cX ↔
        bilinearCrossoverR bW bX < cX / cW)) ∧
    (bilinearCrossoverR 4 4 = 125 / 22 ∧
      (142 / 100 : Rat) < bilinearCrossoverR 4 4 / 4) ∧
    (bilinearCrossoverR 3 5 = 24025 / 92 ∧
      (408 / 100 : Rat) < bilinearCrossoverR 3 5 / 64) ∧
    (bilinearCrossoverR 6 6 = 10143 / 2350 ∧
      (1079 / 1000 : Rat) < bilinearCrossoverR 6 6 / 4) ∧
    (bilinearCrossoverR 3 3 = 49 / 5 ∧
      bilinearCrossoverR 5 5 = 10571 / 2254) := by
  have h44 : bilinearCrossoverR 4 4 = 125 / 22 :=
    bilinearCrossoverR_eq_nat_div (bW := 4) (bX := 4) (p := 125) (q := 22)
      (by decide) (by decide) (by decide) (by decide)
  have h35 : bilinearCrossoverR 3 5 = 24025 / 92 :=
    bilinearCrossoverR_eq_nat_div (bW := 3) (bX := 5) (p := 24025) (q := 92)
      (by decide) (by decide) (by decide) (by decide)
  have h66 : bilinearCrossoverR 6 6 = 10143 / 2350 :=
    bilinearCrossoverR_eq_nat_div (bW := 6) (bX := 6) (p := 10143) (q := 2350)
      (by decide) (by decide) (by decide) (by decide)
  have h33 : bilinearCrossoverR 3 3 = 49 / 5 :=
    bilinearCrossoverR_eq_nat_div (bW := 3) (bX := 3) (p := 49) (q := 5)
      (by decide) (by decide) (by decide) (by decide)
  have h55 : bilinearCrossoverR 5 5 = 10571 / 2254 :=
    bilinearCrossoverR_eq_nat_div (bW := 5) (bX := 5) (p := 10571) (q := 2254)
      (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ⟨h33, h55⟩⟩
  · intro bW bX cW cX hbW hbX hcW
    exact bilinearIntMSE_step_lt_iff hbW hbX hcW
  · refine ⟨h44, ?_⟩
    rw [h44]
    have heq : ((125 / 22 : Rat) / 4) = (125 : Rat) / 88 := by grind
    rw [heq]
    exact rat_div_lt_div_of_nat (a := 142) (b := 100) (c := 125) (d := 88)
      (by decide) (by decide) (by decide)
  · refine ⟨h35, ?_⟩
    rw [h35]
    have heq : ((24025 / 92 : Rat) / 64) = (24025 : Rat) / 5888 := by grind
    rw [heq]
    exact rat_div_lt_div_of_nat (a := 408) (b := 100) (c := 24025) (d := 5888)
      (by decide) (by decide) (by decide)
  · refine ⟨h66, ?_⟩
    rw [h66]
    have heq : ((10143 / 2350 : Rat) / 4) = (10143 : Rat) / 9400 := by grind
    rw [heq]
    exact rat_div_lt_div_of_nat (a := 1079) (b := 1000) (c := 10143) (d := 9400)
      (by decide) (by decide) (by decide)

/-! ### Absmax-Pinned Super-Outlier Reversal -/

/-- Exact absmax pinning identity: the absmax spike `S` reconstructs with zero error (`e_X = 0`). -/
theorem absmaxPinnedQuant_exact {bX : Nat} (hbX : 2 ≤ bX) (S : Rat) :
    absmaxPinnedQuant S bX = S := by
  unfold absmaxPinnedQuant absmaxStep
  have hq : ((intQ bX : Nat) : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (intQ_pos hbX))
  exact rat_div_mul_cancel hq

/-- Universal absmax-pinned super-outlier bit-split reversal equivalence:
    giving one more bit to weights (`bW + 1, bX - 1`) strictly beats `(bW, bX)`
    iff `S^2 + bulkX > (cX / cW) * R^*(bX, bW)`. -/
theorem pinnedSuperOutlierMSE_reversal_iff {bW bX : Nat} (hbW : 2 ≤ bW) (_hbX : 3 ≤ bX)
    {S cW cX bulkX : Rat} (hcW : (0 : Rat) < cW) :
    pinnedSuperOutlierMSE (bW + 1) (bX - 1) S cW cX bulkX <
      pinnedSuperOutlierMSE bW bX S cW cX bulkX ↔
      (cX / cW) * bilinearCrossoverR bX bW < S * S + bulkX := by
  have hden_pos : (0 : Rat) < intInvQ2 bW - intInvQ2 (bW + 1) :=
    rat_sub_pos (intInvQ2_succ_lt hbW)
  unfold pinnedSuperOutlierMSE bilinearCrossoverR
  constructor
  · intro hlt
    have hdiff : (0 : Rat) < (cW * (S * S + bulkX) * intInvQ2 bW + cX * intInvQ2 bX) -
        (cW * (S * S + bulkX) * intInvQ2 (bW + 1) + cX * intInvQ2 (bX - 1)) := rat_sub_pos hlt
    have hrearr : cX * (intInvQ2 (bX - 1) - intInvQ2 bX) <
        cW * (S * S + bulkX) * (intInvQ2 bW - intInvQ2 (bW + 1)) := by
      apply rat_lt_of_sub_pos
      have heq : cW * (S * S + bulkX) * (intInvQ2 bW - intInvQ2 (bW + 1)) -
          cX * (intInvQ2 (bX - 1) - intInvQ2 bX) =
          (cW * (S * S + bulkX) * intInvQ2 bW + cX * intInvQ2 bX) -
          (cW * (S * S + bulkX) * intInvQ2 (bW + 1) + cX * intInvQ2 (bX - 1)) := by grind
      rw [heq]; exact hdiff
    apply rat_lt_of_mul_pos_right (rat_mul_pos hcW hden_pos)
    have hL : (cX / cW) * ((intInvQ2 (bX - 1) - intInvQ2 bX) / (intInvQ2 bW - intInvQ2 (bW + 1))) *
        (cW * (intInvQ2 bW - intInvQ2 (bW + 1))) =
        cX * (intInvQ2 (bX - 1) - intInvQ2 bX) := by
      have hrw : (cX / cW) * ((intInvQ2 (bX - 1) - intInvQ2 bX) / (intInvQ2 bW - intInvQ2 (bW + 1))) *
          (cW * (intInvQ2 bW - intInvQ2 (bW + 1))) =
          ((cX / cW) * cW) * (((intInvQ2 (bX - 1) - intInvQ2 bX) /
            (intInvQ2 bW - intInvQ2 (bW + 1))) * (intInvQ2 bW - intInvQ2 (bW + 1))) := by grind
      rw [hrw, rat_div_mul_cancel (Rat.ne_of_gt hcW), rat_div_mul_cancel (Rat.ne_of_gt hden_pos)]
    have hR : (S * S + bulkX) * (cW * (intInvQ2 bW - intInvQ2 (bW + 1))) =
        cW * (S * S + bulkX) * (intInvQ2 bW - intInvQ2 (bW + 1)) := by grind
    rw [hL, hR]
    exact hrearr
  · intro hgt
    have hmul := rat_mul_lt_mul_of_pos_right hgt (rat_mul_pos hcW hden_pos)
    have hL : (cX / cW) * ((intInvQ2 (bX - 1) - intInvQ2 bX) / (intInvQ2 bW - intInvQ2 (bW + 1))) *
        (cW * (intInvQ2 bW - intInvQ2 (bW + 1))) =
        cX * (intInvQ2 (bX - 1) - intInvQ2 bX) := by
      have hrw : (cX / cW) * ((intInvQ2 (bX - 1) - intInvQ2 bX) / (intInvQ2 bW - intInvQ2 (bW + 1))) *
          (cW * (intInvQ2 bW - intInvQ2 (bW + 1))) =
          ((cX / cW) * cW) * (((intInvQ2 (bX - 1) - intInvQ2 bX) /
            (intInvQ2 bW - intInvQ2 (bW + 1))) * (intInvQ2 bW - intInvQ2 (bW + 1))) := by grind
      rw [hrw, rat_div_mul_cancel (Rat.ne_of_gt hcW), rat_div_mul_cancel (Rat.ne_of_gt hden_pos)]
    have hR : (S * S + bulkX) * (cW * (intInvQ2 bW - intInvQ2 (bW + 1))) =
        cW * (S * S + bulkX) * (intInvQ2 bW - intInvQ2 (bW + 1)) := by grind
    rw [hL, hR] at hmul
    apply rat_lt_of_sub_pos
    have heq : (cW * (S * S + bulkX) * intInvQ2 bW + cX * intInvQ2 bX) -
        (cW * (S * S + bulkX) * intInvQ2 (bW + 1) + cX * intInvQ2 (bX - 1)) =
        cW * (S * S + bulkX) * (intInvQ2 bW - intInvQ2 (bW + 1)) -
        cX * (intInvQ2 (bX - 1) - intInvQ2 bX) := by grind
    rw [heq]
    exact rat_sub_pos hmul

/-- Headline Theorem 3 (`absmax_pinned_superoutlier_bitsplit_reversal`):
    Proves exact zero activation error (`e_X = 0`) on the absmax-pinned spike `S` so the spike
    dot-product error is purely `S * (wHat - w)`, the universal bit-split reversal threshold,
    and concrete reversals: `W5A3` strictly beats `W4A4` iff `S^2 > 125/22` (hence for all `S ≥ 3`),
    and `W4A2` strictly beats `W3A3` iff `S^2 > 49/5` (hence for all `S ≥ 4`). -/
theorem absmax_pinned_superoutlier_bitsplit_reversal :
    (∀ (bX : Nat) (S w wHat : Rat), 2 ≤ bX →
      absmaxPinnedQuant S bX = S ∧
      wHat * absmaxPinnedQuant S bX - w * S = (wHat - w) * S) ∧
    (∀ (bW bX : Nat) (S cW cX bulkX : Rat), 2 ≤ bW → 3 ≤ bX → (0 : Rat) < cW →
      (pinnedSuperOutlierMSE (bW + 1) (bX - 1) S cW cX bulkX <
        pinnedSuperOutlierMSE bW bX S cW cX bulkX ↔
        (cX / cW) * bilinearCrossoverR bX bW < S * S + bulkX)) ∧
    (∀ S : Rat,
      (pinnedSuperOutlierMSE 5 3 S 1 1 0 < pinnedSuperOutlierMSE 4 4 S 1 1 0 ↔
        (125 / 22 : Rat) < S * S) ∧
      ((3 : Rat) ≤ S → pinnedSuperOutlierMSE 5 3 S 1 1 0 < pinnedSuperOutlierMSE 4 4 S 1 1 0)) ∧
    (∀ S : Rat,
      (pinnedSuperOutlierMSE 4 2 S 1 1 0 < pinnedSuperOutlierMSE 3 3 S 1 1 0 ↔
        (49 / 5 : Rat) < S * S) ∧
      ((4 : Rat) ≤ S → pinnedSuperOutlierMSE 4 2 S 1 1 0 < pinnedSuperOutlierMSE 3 3 S 1 1 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro bX S w wHat hbX
    have hpin := absmaxPinnedQuant_exact hbX S
    refine ⟨hpin, ?_⟩
    rw [hpin]; grind
  · intro bW bX S cW cX bulkX hbW hbX hcW
    exact pinnedSuperOutlierMSE_reversal_iff hbW hbX hcW
  · intro S
    have hiff := pinnedSuperOutlierMSE_reversal_iff (bW := 4) (bX := 4) (S := S)
      (cW := 1) (cX := 1) (bulkX := 0) (by decide) (by decide) (by decide)
    have hR : ((1 : Rat) / 1) * bilinearCrossoverR 4 4 = 125 / 22 := by
      have h44 : bilinearCrossoverR 4 4 = 125 / 22 :=
        bilinearCrossoverR_eq_nat_div (bW := 4) (bX := 4) (p := 125) (q := 22)
          (by decide) (by decide) (by decide) (by decide)
      rw [h44]; grind
    have hS0 : S * S + 0 = S * S := Rat.add_zero _
    rw [hR, hS0] at hiff
    refine ⟨hiff, ?_⟩
    intro h3
    apply hiff.mpr
    have h9 : (9 : Rat) ≤ S * S := by
      have h1 : (3 : Rat) * 3 ≤ (3 : Rat) * S := rat_mul_le_mul_of_nonneg_left h3 (by decide)
      have h2 : (3 : Rat) * S ≤ S * S :=
        rat_mul_le_mul_of_nonneg_right h3 (Rat.le_trans (by decide) h3)
      have h33 : (3 : Rat) * 3 = 9 := by grind
      rw [h33] at h1
      exact Rat.le_trans h1 h2
    have hlt9 : (125 / 22 : Rat) < 9 := by
      apply rat_div_lt_of_mul_lt (by decide : (0 : Rat) < 22)
      have hmul : (9 : Rat) * 22 = 198 := by grind
      rw [hmul]; decide
    exact rat_lt_of_lt_of_le hlt9 h9
  · intro S
    have hiff := pinnedSuperOutlierMSE_reversal_iff (bW := 3) (bX := 3) (S := S)
      (cW := 1) (cX := 1) (bulkX := 0) (by decide) (by decide) (by decide)
    have hR : ((1 : Rat) / 1) * bilinearCrossoverR 3 3 = 49 / 5 := by
      have h33 : bilinearCrossoverR 3 3 = 49 / 5 :=
        bilinearCrossoverR_eq_nat_div (bW := 3) (bX := 3) (p := 49) (q := 5)
          (by decide) (by decide) (by decide) (by decide)
      rw [h33]; grind
    have hS0 : S * S + 0 = S * S := Rat.add_zero _
    rw [hR, hS0] at hiff
    refine ⟨hiff, ?_⟩
    intro h4
    apply hiff.mpr
    have h16 : (16 : Rat) ≤ S * S := by
      have h1 : (4 : Rat) * 4 ≤ (4 : Rat) * S := rat_mul_le_mul_of_nonneg_left h4 (by decide)
      have h2 : (4 : Rat) * S ≤ S * S :=
        rat_mul_le_mul_of_nonneg_right h4 (Rat.le_trans (by decide) h4)
      have h44 : (4 : Rat) * 4 = 16 := by grind
      rw [h44] at h1
      exact Rat.le_trans h1 h2
    have hlt16 : (49 / 5 : Rat) < 16 := by
      apply rat_div_lt_of_mul_lt (by decide : (0 : Rat) < 5)
      have hmul : (16 : Rat) * 5 = 80 := by grind
      rw [hmul]; decide
    exact rat_lt_of_lt_of_le hlt16 h16

/-! ### Pillar 2B: `MXFP_b` Exponent-vs-Mantissa Parity Dominance -/

/-- Headline Theorem 4 (`mxfp_w5a7_beats_w6a6_mantissa_parity_exact`):
    At identical 12-bit budget (`B_tot = 12`), asymmetric `W5A7` (`MXFP5-E2M2 × MXFP7-E3M3`,
    5 total mantissa bits) strictly beats symmetric `W6A6` (`MXFP6-E3M2 × MXFP6-E3M2`,
    4 total mantissa bits) in normal-range relative quantization MSE by an exact constant factor
    `8/5` (`1.6x`) for symmetric weighting, an exact `4x` reduction on the activation factor with
    zero weight-factor penalty, and unconditionally for ALL positive `(cW, cX)` (every kurtosis). -/
theorem mxfp_w5a7_beats_w6a6_mantissa_parity_exact :
    (mxfp5E2M2.totalBits + mxfp7E3M3.totalBits = 12 ∧
      mxfp6E3M2.totalBits + mxfp6E3M2.totalBits = 12 ∧
      mxfp5E2M2.mbits + mxfp7E3M3.mbits = 5 ∧
      mxfp6E3M2.mbits + mxfp6E3M2.mbits = 4) ∧
    (mxfpRelMSE mxfp5E2M2 = 1 / 192 ∧
      mxfpRelMSE mxfp6E3M2 = 1 / 192 ∧
      mxfpRelMSE mxfp7E3M3 = 1 / 768 ∧
      mxfpRelMSE mxfp6E3M2 / mxfpRelMSE mxfp7E3M3 = 4) ∧
    (∀ c : Rat, (0 : Rat) < c →
      mxfpProdRelMSE mxfp6E3M2 mxfp6E3M2 c c / mxfpProdRelMSE mxfp5E2M2 mxfp7E3M3 c c = 8 / 5 ∧
      mxfpProdRelMSE mxfp5E2M2 mxfp7E3M3 c c < mxfpProdRelMSE mxfp6E3M2 mxfp6E3M2 c c) ∧
    (∀ cW cX : Rat, (0 : Rat) < cW → (0 : Rat) < cX →
      mxfpProdRelMSE mxfp5E2M2 mxfp7E3M3 cW cX < mxfpProdRelMSE mxfp6E3M2 mxfp6E3M2 cW cX ∧
      mxfpProdRelMSE mxfp7E3M3 mxfp5E2M2 cW cX < mxfpProdRelMSE mxfp6E3M2 mxfp6E3M2 cW cX) := by
  have h5 : mxfpRelMSE mxfp5E2M2 = 1 / 192 := by
    unfold mxfpRelMSE mxfp5E2M2 invPow2Rat pow2Rat; grind
  have h6 : mxfpRelMSE mxfp6E3M2 = 1 / 192 := by
    unfold mxfpRelMSE mxfp6E3M2 invPow2Rat pow2Rat; grind
  have h7 : mxfpRelMSE mxfp7E3M3 = 1 / 768 := by
    unfold mxfpRelMSE mxfp7E3M3 invPow2Rat pow2Rat; grind
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mxfp5E2M2 mxfp6E3M2 mxfp7E3M3; decide
  · refine ⟨h5, h6, h7, ?_⟩
    rw [h6, h7]; grind
  · intro c hc
    unfold mxfpProdRelMSE
    rw [h5, h6, h7]
    have hnum : c * (1 / 192 : Rat) + c * (1 / 192 : Rat) = c * (1 / 96 : Rat) := by grind
    have hden : c * (1 / 192 : Rat) + c * (1 / 768 : Rat) = c * (5 / 768 : Rat) := by grind
    rw [hnum, hden]
    constructor
    · have h5pos : (0 : Rat) < (5 / 768 : Rat) := rat_div_pos (by decide) (by decide)
      have hne : c * (5 / 768 : Rat) ≠ 0 := Rat.ne_of_gt (rat_mul_pos hc h5pos)
      have hmul : (c * (1 / 96 : Rat) / (c * (5 / 768 : Rat))) * (c * (5 / 768 : Rat)) =
          (8 / 5 : Rat) * (c * (5 / 768 : Rat)) := by
        rw [rat_div_mul_cancel hne]; grind
      have hsub : ((c * (1 / 96 : Rat) / (c * (5 / 768 : Rat))) - (8 / 5 : Rat)) *
          (c * (5 / 768 : Rat)) = 0 := by
        have hrw : ((c * (1 / 96 : Rat) / (c * (5 / 768 : Rat))) - (8 / 5 : Rat)) *
            (c * (5 / 768 : Rat)) =
            (c * (1 / 96 : Rat) / (c * (5 / 768 : Rat))) * (c * (5 / 768 : Rat)) -
            (8 / 5 : Rat) * (c * (5 / 768 : Rat)) := by grind
        rw [hrw, hmul]; grind
      cases Rat.mul_eq_zero.mp hsub with
      | inl h => grind
      | inr h => exact False.elim (hne h)
    · have hlt : (5 / 768 : Rat) < 1 / 96 :=
        rat_div_lt_div_of_nat (a := 5) (b := 768) (c := 1) (d := 96)
          (by decide) (by decide) (by decide)
      exact rat_mul_lt_mul_of_pos_left hlt hc
  · intro cW cX hcW hcX
    unfold mxfpProdRelMSE
    rw [h5, h6, h7]
    have h3pos : (0 : Rat) < (3 / 768 : Rat) := rat_div_pos (by decide) (by decide)
    constructor
    · apply rat_lt_of_sub_pos
      have heq : (cW * (1 / 192 : Rat) + cX * (1 / 192 : Rat)) -
          (cW * (1 / 192 : Rat) + cX * (1 / 768 : Rat)) = cX * (3 / 768 : Rat) := by grind
      rw [heq]
      exact rat_mul_pos hcX h3pos
    · apply rat_lt_of_sub_pos
      have heq : (cW * (1 / 192 : Rat) + cX * (1 / 192 : Rat)) -
          (cW * (1 / 768 : Rat) + cX * (1 / 192 : Rat)) = cW * (3 / 768 : Rat) := by grind
      rw [heq]
      exact rat_mul_pos hcW h3pos

end AlibiBitsplitKulisch
