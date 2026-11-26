/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import UnsignedFp4SoftmaxV.RatOrder

/-!
# Theorems 3 & 4: Softmax Simplex RTN Drift & Zero-Drift Stratified XOR-VDC SR

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
3. `softmax_simplex_rtn_drift_exact`: Universal exact rational bound
   `|1 - ∑ Q(p_j)| ≤ max_k ((N-1) h_k)/(1 + (N-1) m_k)` across all simplex sizes `N ≥ 2`,
   exact downward and upward midpoint attainment, exact `N = 128` instantiations
   (`S-E2M1 > 84%`, `UINT4 > 80%`, `U-E3M1 < 25%`), and universal OCP `FP8-E4M3` bound `< 6%`.
4. `stratified_xor_vdc_simplex_zero_drift`: Exact discrete proof that pair-antithetic SR
   achieves exact `0` simplex-sum drift on midpoint uniform rows (`f = 1/2`), and zero-carry
   stratified XOR-VDC SR (`(bitRev b j) ^^^ mask`) is an exact bijection on `{0, ..., 2^b - 1}`
   achieving exact `0` simplex-sum drift across ALL dyadic fractional residues `f = k / 2^b`.
-/

namespace UnsignedFp4SoftmaxV

/-! ### Theorem 3: Softmax Simplex RTN Conservation Drift -/

theorem ratAbs_rtnSignedErr {u0 u1 x : Rat} (hx0 : u0 ≤ x) (hx1 : x ≤ u1) :
    ratAbs (rtnSignedErr u0 u1 x) = rtnDist u0 u1 x := by
  unfold rtnSignedErr rtnDist
  split
  · rw [← ratAbs_neg (u0 - x)]
    have eq : -(u0 - x) = x - u0 := by grind
    rw [eq, ratAbs_of_nonneg (rat_sub_nonneg hx0)]
  · rw [ratAbs_of_nonneg (rat_sub_nonneg hx1)]

/-- Per-coordinate exact RTN simplex-drift midpoint optimality:
    for any `c > 0` and `0 ≤ u0 ≤ x ≤ u1`, `rtnDist(u0, u1, x) ≤ (h / (c + m)) * (c + x)`. -/
theorem drift_coord_bound {u0 u1 x c : Rat}
    (hu0 : (0 : Rat) ≤ u0) (hx0 : u0 ≤ x) (hx1 : x ≤ u1) (hc : (0 : Rat) < c) :
    let h := (u1 - u0) / 2
    let m := (u0 + u1) / 2
    rtnDist u0 u1 x ≤ (h / (c + m)) * (c + x) := by
  intro h m
  have hu1 : (0 : Rat) ≤ u1 := Rat.le_trans hu0 (Rat.le_trans hx0 hx1)
  have hm_nonneg : (0 : Rat) ≤ m := rat_div_nonneg (rat_add_nonneg hu0 hu1) (by decide)
  have hden_pos : (0 : Rat) < c + m := rat_add_pos_of_pos_of_nonneg hc hm_nonneg
  have hden_ne : c + m ≠ 0 := Rat.ne_of_gt hden_pos
  have hgoal :
      rtnDist u0 u1 x * (c + m) ≤ h * (c + x) →
      rtnDist u0 u1 x ≤ (h / (c + m)) * (c + x) := by
    intro hcross
    apply rat_le_of_mul_pos_right hden_pos
    have eq1 : (h / (c + m)) * (c + x) * (c + m) = h * (c + x) := by
      rw [Rat.mul_comm (h / (c + m)) (c + x), Rat.mul_assoc,
          rat_div_mul_cancel hden_ne, Rat.mul_comm]
    rw [eq1]; exact hcross
  apply hgoal
  unfold rtnDist
  split
  · rename_i hxm
    have hmx_nonneg : (0 : Rat) ≤ m - x := rat_sub_nonneg hxm
    have hcu0_nonneg : (0 : Rat) ≤ c + u0 := rat_add_nonneg (Rat.le_of_lt hc) hu0
    apply rat_le_of_sub_nonneg
    have hid : h * (c + x) - (x - u0) * (c + m) = (m - x) * (c + u0) := by
      dsimp only [h, m]; grind
    rw [hid]
    exact Rat.mul_nonneg hmx_nonneg hcu0_nonneg
  · rename_i hnot
    have hmx : m < x := Rat.not_le.mp hnot
    have hxm_nonneg : (0 : Rat) ≤ x - m := rat_sub_nonneg (Rat.le_of_lt hmx)
    have hu1x_le_h : u1 - x ≤ h := by
      apply rat_le_of_sub_nonneg
      have eq : h - (u1 - x) = x - m := by dsimp only [h, m]; grind
      rw [eq]; exact hxm_nonneg
    have hh_nonneg : (0 : Rat) ≤ h :=
      rat_div_nonneg (rat_sub_nonneg (Rat.le_trans hx0 hx1)) (by decide)
    have hcx_le : c + m ≤ c + x := rat_add_le_add Rat.le_refl (Rat.le_of_lt hmx)
    exact Rat.le_trans (rat_mul_le_mul_of_nonneg_right hu1x_le_h (Rat.le_of_lt hden_pos))
                       (rat_mul_le_mul_of_nonneg_left hcx_le hh_nonneg)

/-- Universal vector-level RTN simplex-sum drift bound for any simplex dimension `N ≥ 2`. -/
theorem simplex_rtn_drift_upper_bound {N : Nat} (hN : 2 ≤ N) {D s : Rat}
    (hs : (0 : Rat) < s) (p q : Fin (N - 1) → Rat)
    (hsimplex : s + sumFin p = 1)
    (hcoord : ∀ j : Fin (N - 1), ∃ u0 u1 : Rat,
      (0 : Rat) ≤ u0 ∧ u0 ≤ p j / s ∧ p j / s ≤ u1 ∧
      q j - p j = s * rtnSignedErr u0 u1 (p j / s) ∧
      driftBin u0 u1 N ≤ D) :
    ratAbs (1 - (s + sumFin q)) ≤ D := by
  have hn1_nat : 0 < N - 1 := by omega
  have hn1_pos : (0 : Rat) < ((N - 1 : Nat) : Rat) := rat_natCast_pos hn1_nat
  have hn1_ne : ((N - 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hn1_pos
  have hs_ne : s ≠ 0 := Rat.ne_of_gt hs
  let c : Rat := 1 / ((N - 1 : Nat) : Rat)
  have hc_pos : (0 : Rat) < c := rat_div_pos (by decide) hn1_pos
  have hdiff_eq : 1 - (s + sumFin q) = -(sumFin (fun j => q j - p j)) := by
    rw [sumFin_sub, ← hsimplex]; grind
  rw [hdiff_eq, ratAbs_neg]
  have htri := ratAbs_sumFin_le (fun j => q j - p j)
  have hterm : ∀ j : Fin (N - 1),
      ratAbs (q j - p j) ≤ D * (s * c + p j) := by
    intro j
    rcases hcoord j with ⟨u0, u1, hu0, hx0, hx1, heq, hbin⟩
    rw [heq, ratAbs_mul_nonneg (Rat.le_of_lt hs), ratAbs_rtnSignedErr hx0 hx1]
    have h1 := drift_coord_bound hu0 hx0 hx1 hc_pos
    let h := (u1 - u0) / 2
    let m := (u0 + u1) / 2
    have hfrac_eq : h / (c + m) = driftBin u0 u1 N := by
      unfold driftBin
      dsimp only [h, m, c]
      have hu1 : (0 : Rat) ≤ u1 := Rat.le_trans hu0 (Rat.le_trans hx0 hx1)
      have hm_nonneg : (0 : Rat) ≤ (u0 + u1) / 2 :=
        rat_div_nonneg (rat_add_nonneg hu0 hu1) (by decide)
      have hd1 : 1 / ((N - 1 : Nat) : Rat) + (u0 + u1) / 2 ≠ 0 :=
        Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg hc_pos hm_nonneg)
      have hd2 : 1 + ((N - 1 : Nat) : Rat) * ((u0 + u1) / 2) ≠ 0 :=
        Rat.ne_of_gt (rat_add_pos_of_pos_of_nonneg (by decide)
          (Rat.mul_nonneg (Rat.le_of_lt hn1_pos) hm_nonneg))
      apply rat_div_eq_of_cross hd1 hd2
      have hmul : (1 / ((N - 1 : Nat) : Rat)) * ((N - 1 : Nat) : Rat) = 1 :=
        rat_div_mul_cancel hn1_ne
      grind
    change rtnDist u0 u1 (p j / s) ≤ (h / (c + m)) * (c + p j / s) at h1
    rw [hfrac_eq] at h1
    have hcx_nonneg : (0 : Rat) ≤ c + p j / s :=
      Rat.le_of_lt (rat_add_pos_of_pos_of_nonneg hc_pos (Rat.le_trans hu0 hx0))
    have h2 : rtnDist u0 u1 (p j / s) ≤ D * (c + p j / s) :=
      Rat.le_trans h1 (rat_mul_le_mul_of_nonneg_right hbin hcx_nonneg)
    have h3 := rat_mul_le_mul_of_nonneg_left h2 (Rat.le_of_lt hs)
    have eqR : s * (D * (c + p j / s)) = D * (s * c + p j) := by
      have hsp : s * (p j / s) = p j := rat_mul_div_cancel hs_ne
      grind
    rw [eqR] at h3
    exact h3
  have hsum_le := sumFin_le_sumFin hterm
  rw [sumFin_mul_left, sumFin_add, sumFin_const] at hsum_le
  have hsc : ((N - 1 : Nat) : Rat) * (s * c) = s := by
    dsimp only [c]
    have hmul : ((N - 1 : Nat) : Rat) * (1 / ((N - 1 : Nat) : Rat)) = 1 :=
      rat_mul_div_cancel hn1_ne
    grind
  rw [hsc, hsimplex, Rat.mul_one] at hsum_le
  exact Rat.le_trans htri hsum_le

/-- Exact attainment of both downward and upward simplex drift `driftBin u0 u1 N`
    at the uniform midpoint row `(s, s*m, ..., s*m)` with `s = 1 / (1 + (N-1)*m)`. -/
theorem simplex_rtn_drift_attainment {N : Nat} {u0 u1 : Rat}
    (hu0 : (0 : Rat) ≤ u0) (hu1 : u0 ≤ u1) :
    let m := (u0 + u1) / 2
    let s := 1 / (1 + ((N - 1 : Nat) : Rat) * m)
    (s + sumFin (fun _ : Fin (N - 1) => s * m) = 1) ∧
    (1 - (s + sumFin (fun _ : Fin (N - 1) => s * u0)) = driftBin u0 u1 N) ∧
    ((s + sumFin (fun _ : Fin (N - 1) => s * u1)) - 1 = driftBin u0 u1 N) := by
  intro m s
  have hm_nonneg : (0 : Rat) ≤ m :=
    rat_div_nonneg (rat_add_nonneg hu0 (Rat.le_trans hu0 hu1)) (by decide)
  have hden_pos : (0 : Rat) < 1 + ((N - 1 : Nat) : Rat) * m :=
    rat_add_pos_of_pos_of_nonneg (by decide)
      (Rat.mul_nonneg (rat_natCast_nonneg (N - 1)) hm_nonneg)
  have hden_ne : 1 + ((N - 1 : Nat) : Rat) * m ≠ 0 := Rat.ne_of_gt hden_pos
  have hs_mul : s * (1 + ((N - 1 : Nat) : Rat) * m) = 1 := rat_div_mul_cancel hden_ne
  refine ⟨?_, ?_, ?_⟩
  · rw [sumFin_const]
    have eq : s + ((N - 1 : Nat) : Rat) * (s * m) = s * (1 + ((N - 1 : Nat) : Rat) * m) := by grind
    rw [eq, hs_mul]
  · rw [sumFin_const]
    unfold driftBin
    dsimp only [s, m] at *
    have hleft : (1 - (1 / (1 + ((N - 1 : Nat) : Rat) * ((u0 + u1) / 2)) +
        ((N - 1 : Nat) : Rat) * (1 / (1 + ((N - 1 : Nat) : Rat) * ((u0 + u1) / 2)) * u0))) *
        (1 + ((N - 1 : Nat) : Rat) * ((u0 + u1) / 2)) = ((N - 1 : Nat) : Rat) * ((u1 - u0) / 2) := by
      grind
    have hdiv := rat_div_mul_cancel (a := ((N - 1 : Nat) : Rat) * ((u1 - u0) / 2)) hden_ne
    have hsub : ((1 - (1 / (1 + ((N - 1 : Nat) : Rat) * ((u0 + u1) / 2)) +
        ((N - 1 : Nat) : Rat) * (1 / (1 + ((N - 1 : Nat) : Rat) * ((u0 + u1) / 2)) * u0))) -
        (((N - 1 : Nat) : Rat) * ((u1 - u0) / 2)) / (1 + ((N - 1 : Nat) : Rat) * ((u0 + u1) / 2))) *
        (1 + ((N - 1 : Nat) : Rat) * ((u0 + u1) / 2)) = 0 := by grind
    cases Rat.mul_eq_zero.mp hsub with
    | inl h0 => grind
    | inr hd => exact False.elim (hden_ne hd)
  · rw [sumFin_const]
    unfold driftBin
    dsimp only [s, m] at *
    have hleft : ((s + ((N - 1 : Nat) : Rat) * (s * u1)) - 1) *
        (1 + ((N - 1 : Nat) : Rat) * m) = ((N - 1 : Nat) : Rat) * ((u1 - u0) / 2) := by
      dsimp only [m] at *; grind
    have hdiv := (rat_div_mul_cancel (a := ((N - 1 : Nat) : Rat) * ((u1 - u0) / 2)) hden_ne)
    have hsub : (((s + ((N - 1 : Nat) : Rat) * (s * u1)) - 1) -
        (((N - 1 : Nat) : Rat) * ((u1 - u0) / 2)) / (1 + ((N - 1 : Nat) : Rat) * m)) *
        (1 + ((N - 1 : Nat) : Rat) * m) = 0 := by grind
    cases Rat.mul_eq_zero.mp hsub with
    | inl h0 => grind
    | inr hd => exact False.elim (hden_ne hd)

/-! ### Exact `N = 128` Drift Instantiations (`S-E2M1`, `UINT4`, `U-E3M1`, `FP8-E4M3`) -/

private theorem driftBin_int_form (a b M : Nat) (hM : 0 < M) (N : Nat) (hab : a ≤ b) :
    driftBin ((a : Rat) / (M : Rat)) ((b : Rat) / (M : Rat)) N =
      ((N - 1 : Nat) : Rat) * ((b - a : Nat) : Rat) /
        (2 * (M : Rat) + ((N - 1 : Nat) : Rat) * ((a + b : Nat) : Rat)) := by
  unfold driftBin
  have hMpos : (0 : Rat) < (M : Rat) := rat_natCast_pos hM
  have hMne : (M : Rat) ≠ 0 := Rat.ne_of_gt hMpos
  have hsub_cast : ((b - a : Nat) : Rat) = (b : Rat) - (a : Rat) := by
    have hk : b = a + (b - a) := (Nat.add_sub_of_le hab).symm
    have hc : (b : Rat) = (a : Rat) + ((b - a : Nat) : Rat) := by
      conv => lhs; rw [hk]
      rw [Rat.natCast_add]
    grind
  have hadd_cast : ((a + b : Nat) : Rat) = (a : Rat) + (b : Rat) := Rat.natCast_add a b
  have hd1 : (0 : Rat) < 1 + ((N - 1 : Nat) : Rat) *
      (((a : Rat) / (M : Rat) + (b : Rat) / (M : Rat)) / 2) :=
    rat_add_pos_of_pos_of_nonneg (by decide)
      (Rat.mul_nonneg (rat_natCast_nonneg (N - 1))
        (rat_div_nonneg (rat_add_nonneg (rat_div_nonneg (rat_natCast_nonneg a) hMpos)
                                        (rat_div_nonneg (rat_natCast_nonneg b) hMpos)) (by decide)))
  have hd2 : (0 : Rat) < 2 * (M : Rat) + ((N - 1 : Nat) : Rat) * ((a + b : Nat) : Rat) :=
    rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) hMpos)
      (Rat.mul_nonneg (rat_natCast_nonneg (N - 1)) (rat_natCast_nonneg (a + b)))
  apply rat_div_eq_of_cross (Rat.ne_of_gt hd1) (Rat.ne_of_gt hd2)
  rw [hsub_cast, hadd_cast]
  have ha : ((a : Rat) / (M : Rat)) * (M : Rat) = (a : Rat) := rat_div_mul_cancel hMne
  have hb : ((b : Rat) / (M : Rat)) * (M : Rat) = (b : Rat) := rat_div_mul_cancel hMne
  grind

private theorem drift_bin_le_nat_frac (a b M N P Q : Nat)
    (hM : 0 < M) (hQ : 0 < Q) (hab : a ≤ b)
    (hcross : (N - 1) * (b - a) * Q ≤ P * (2 * M + (N - 1) * (a + b))) :
    driftBin ((a : Rat) / (M : Rat)) ((b : Rat) / (M : Rat)) N ≤ (P : Rat) / (Q : Rat) := by
  rw [driftBin_int_form a b M hM N hab]
  have hd1 : (0 : Rat) < 2 * (M : Rat) + ((N - 1 : Nat) : Rat) * ((a + b : Nat) : Rat) :=
    rat_add_pos_of_pos_of_nonneg (rat_mul_pos (by decide) (rat_natCast_pos hM))
      (Rat.mul_nonneg (rat_natCast_nonneg (N - 1)) (rat_natCast_nonneg (a + b)))
  apply rat_div_le_div_of_cross hd1 (rat_natCast_pos hQ)
  have h1 := rat_natCast_le hcross
  simp only [Rat.natCast_mul, Rat.natCast_add] at h1
  have eqR : (P : Rat) * (2 * (M : Rat) + ((N - 1 : Nat) : Rat) * ((a : Rat) + (b : Rat))) =
      (P : Rat) * (2 * (M : Rat) + ((N - 1 : Nat) : Rat) * ((a + b : Nat) : Rat)) := by
    rw [Rat.natCast_add]
  rw [← eqR]
  exact h1

private theorem drift_sE2M1_128 : simplexRtnDrift sE2M1Levels 128 = 127 / 151 := by
  have h0 : driftBin (((0 : Nat) : Rat) / ((12 : Nat) : Rat)) (((1 : Nat) : Rat) / ((12 : Nat) : Rat)) 128 = 127 / 151 := by
    rw [driftBin_int_form 0 1 12 (by omega) 128 (by omega)]; grind
  have hdom : ∀ a b : Nat, a ≤ b →
      127 * (b - a) * 151 ≤ 127 * (2 * 12 + 127 * (a + b)) →
      driftBin ((a : Rat) / (12 : Rat)) ((b : Rat) / (12 : Rat)) 128 ≤ 127 / 151 := by
    intro a b hab h
    exact drift_bin_le_nat_frac a b 12 128 127 151 (by omega) (by omega) hab h
  have hnn : (0 : Rat) ≤ 127 / 151 := rat_div_nonneg (by decide) (by decide)
  unfold simplexRtnDrift sE2M1Levels normalizeLevels
  simp only [List.map, maxAdjacentBins]
  apply Rat.le_antisymm
  · repeat (first | apply rat_max_le | exact hnn | (apply hdom <;> omega))
  · rw [← h0]; exact rat_le_max_left _ _

private theorem drift_uE0M4_128 : simplexRtnDrift uE0M4Levels 128 = 127 / 157 := by
  have h0 : driftBin (((0 : Nat) : Rat) / ((15 : Nat) : Rat)) (((1 : Nat) : Rat) / ((15 : Nat) : Rat)) 128 = 127 / 157 := by
    rw [driftBin_int_form 0 1 15 (by omega) 128 (by omega)]; grind
  have hdom : ∀ a b : Nat, a ≤ b →
      127 * (b - a) * 157 ≤ 127 * (2 * 15 + 127 * (a + b)) →
      driftBin ((a : Rat) / (15 : Rat)) ((b : Rat) / (15 : Rat)) 128 ≤ 127 / 157 := by
    intro a b hab h
    exact drift_bin_le_nat_frac a b 15 128 127 157 (by omega) (by omega) hab h
  have hnn : (0 : Rat) ≤ 127 / 157 := rat_div_nonneg (by decide) (by decide)
  have hL : unsignedFp4IntLevels 0 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := rfl
  unfold simplexRtnDrift uE0M4Levels normalizeLevels
  rw [hL]
  simp only [List.map, maxAdjacentBins]
  apply Rat.le_antisymm
  · repeat (first | apply rat_max_le | exact hnn | (apply hdom <;> omega))
  · rw [← h0]; exact rat_le_max_left _ _

private theorem drift_uE3M1_128 : simplexRtnDrift uE3M1Levels 128 = 127 / 511 := by
  have h0 : driftBin (((0 : Nat) : Rat) / ((192 : Nat) : Rat)) (((1 : Nat) : Rat) / ((192 : Nat) : Rat)) 128 = 127 / 511 := by
    rw [driftBin_int_form 0 1 192 (by omega) 128 (by omega)]; grind
  have hdom : ∀ a b : Nat, a ≤ b →
      127 * (b - a) * 511 ≤ 127 * (2 * 192 + 127 * (a + b)) →
      driftBin ((a : Rat) / (192 : Rat)) ((b : Rat) / (192 : Rat)) 128 ≤ 127 / 511 := by
    intro a b hab h
    exact drift_bin_le_nat_frac a b 192 128 127 511 (by omega) (by omega) hab h
  have hnn : (0 : Rat) ≤ 127 / 511 := rat_div_nonneg (by decide) (by decide)
  have hL : unsignedFp4IntLevels 3 1 = [0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192] := rfl
  unfold simplexRtnDrift uE3M1Levels normalizeLevels
  rw [hL]
  simp only [List.map, maxAdjacentBins]
  apply Rat.le_antisymm
  · repeat (first | apply rat_max_le | exact hnn | (apply hdom <;> omega))
  · rw [← h0]; exact rat_le_max_left _ _

/-- Universal exact `N = 128` bound over ALL 126 adjacent bins of OCP `FP8-E4M3`:
    attained at `(E = 15, M = 0..1)` with exact value `127 / 2187 < 6 / 100`. -/
theorem drift_fp8E4M3_128_all_bins :
    driftBin ((fp8E4M3IntLevel 15 0 : Rat) / (fp8E4M3MaxInt : Rat))
             ((fp8E4M3IntLevel 15 1 : Rat) / (fp8E4M3MaxInt : Rat)) 128 = 127 / 2187 ∧
    (∀ e m : Nat, e < 16 → m < 8 → ¬(e = 15 ∧ 6 ≤ m) →
      let a := fp8E4M3IntLevel e m
      let b := if m < 7 then fp8E4M3IntLevel e (m + 1) else fp8E4M3IntLevel (e + 1) 0
      driftBin ((a : Rat) / (fp8E4M3MaxInt : Rat)) ((b : Rat) / (fp8E4M3MaxInt : Rat)) 128 ≤
        127 / 2187) := by
  constructor
  · have h1 : fp8E4M3IntLevel 15 0 = 131072 := rfl
    have h2 : fp8E4M3IntLevel 15 1 = 147456 := rfl
    have h3 : fp8E4M3MaxInt = 229376 := rfl
    rw [h1, h2, h3, driftBin_int_form 131072 147456 229376 (by omega) 128 (by omega)]
    grind
  · intro e m he hm hnan a b
    have hpow_le : ∀ k : Nat, k ≤ 14 → 2 ^ k ≤ 16384 := by
      intro k hk
      have h1 : 2 ^ k ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) hk
      omega
    by_cases he0 : e = 0
    · subst he0
      by_cases hm7 : m < 7
      · have ha : a = m := by simp [a, fp8E4M3IntLevel]
        have hb : b = m + 1 := by simp [b, hm7, fp8E4M3IntLevel]
        rw [ha, hb]
        exact drift_bin_le_nat_frac m (m + 1) fp8E4M3MaxInt 128 127 2187
          (by unfold fp8E4M3MaxInt; omega) (by omega) (by omega)
          (by unfold fp8E4M3MaxInt; omega)
      · have hm7eq : m = 7 := by omega
        subst hm7eq
        have ha : a = 7 := by simp [a, fp8E4M3IntLevel]
        have hb : b = 8 := by simp [b, fp8E4M3IntLevel]
        rw [ha, hb]
        exact drift_bin_le_nat_frac 7 8 fp8E4M3MaxInt 128 127 2187
          (by unfold fp8E4M3MaxInt; omega) (by omega) (by omega)
          (by unfold fp8E4M3MaxInt; omega)
    · have hp_le : 2 ^ (e - 1) ≤ 16384 := hpow_le (e - 1) (by omega)
      have ha : a = (8 + m) * 2 ^ (e - 1) := by simp [a, fp8E4M3IntLevel, he0]
      have hb : b = (8 + m + 1) * 2 ^ (e - 1) := by
        by_cases hm7 : m < 7
        · simp only [b, hm7, ↓reduceIte, fp8E4M3IntLevel, he0]
          have : 8 + (m + 1) = 8 + m + 1 := by omega
          rw [this]
        · have hm7eq : m = 7 := by omega
          subst hm7eq
          have hstep : 2 ^ e = 2 * 2 ^ (e - 1) := by
            have heq : e = (e - 1) + 1 := by omega
            conv => lhs; rw [heq]
            rw [Nat.pow_succ, Nat.mul_comm]
          simp only [b, Nat.lt_irrefl, ↓reduceIte, fp8E4M3IntLevel, Nat.add_eq_zero_iff,
                     Nat.one_ne_zero, and_false, Nat.add_sub_cancel, Nat.add_zero]
          rw [hstep, ← Nat.mul_assoc]
      rw [ha, hb]
      apply drift_bin_le_nat_frac ((8 + m) * 2 ^ (e - 1)) ((8 + m + 1) * 2 ^ (e - 1))
        fp8E4M3MaxInt 128 127 2187 (by unfold fp8E4M3MaxInt; omega) (by omega)
      · exact Nat.mul_le_mul_right _ (by omega)
      · unfold fp8E4M3MaxInt
        have hdiff : (8 + m + 1) * 2 ^ (e - 1) - (8 + m) * 2 ^ (e - 1) = 2 ^ (e - 1) := by
          apply Nat.sub_eq_of_eq_add
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        have hsum : (8 + m) * 2 ^ (e - 1) + (8 + m + 1) * 2 ^ (e - 1) =
            (17 + 2 * m) * 2 ^ (e - 1) := by
          rw [← Nat.add_mul]; congr 1; omega
        rw [hdiff, hsum]
        have h17 : 17 * 2 ^ (e - 1) ≤ (17 + 2 * m) * 2 ^ (e - 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega

/-- Headline Theorem 3: Universal exact RTN Softmax simplex-sum conservation drift bound,
    exact downward and upward attainment, and exact `N = 128` instantiations. -/
theorem softmax_simplex_rtn_drift_exact :
    (∀ (N : Nat) (_ : 2 ≤ N) (D s : Rat) (_ : (0 : Rat) < s) (p q : Fin (N - 1) → Rat),
      s + sumFin p = 1 →
      (∀ j : Fin (N - 1), ∃ u0 u1 : Rat,
        (0 : Rat) ≤ u0 ∧ u0 ≤ p j / s ∧ p j / s ≤ u1 ∧
        q j - p j = s * rtnSignedErr u0 u1 (p j / s) ∧
        driftBin u0 u1 N ≤ D) →
      ratAbs (1 - (s + sumFin q)) ≤ D) ∧
    (∀ (N : Nat) (u0 u1 : Rat), (0 : Rat) ≤ u0 → u0 ≤ u1 →
      let m := (u0 + u1) / 2
      let s := 1 / (1 + ((N - 1 : Nat) : Rat) * m)
      (s + sumFin (fun _ : Fin (N - 1) => s * m) = 1) ∧
      (1 - (s + sumFin (fun _ : Fin (N - 1) => s * u0)) = driftBin u0 u1 N) ∧
      ((s + sumFin (fun _ : Fin (N - 1) => s * u1)) - 1 = driftBin u0 u1 N)) ∧
    ((simplexRtnDrift sE2M1Levels 128 = 127 / 151 ∧ (84 / 100 : Rat) < simplexRtnDrift sE2M1Levels 128) ∧
     (simplexRtnDrift uE0M4Levels 128 = 127 / 157 ∧ (80 / 100 : Rat) < simplexRtnDrift uE0M4Levels 128) ∧
     (simplexRtnDrift uE3M1Levels 128 = 127 / 511 ∧ simplexRtnDrift uE3M1Levels 128 < (25 / 100 : Rat)) ∧
     (driftBin ((fp8E4M3IntLevel 15 0 : Rat) / (fp8E4M3MaxInt : Rat))
               ((fp8E4M3IntLevel 15 1 : Rat) / (fp8E4M3MaxInt : Rat)) 128 = 127 / 2187 ∧
      (127 / 2187 : Rat) < (6 / 100 : Rat) ∧
      (∀ e m : Nat, e < 16 → m < 8 → ¬(e = 15 ∧ 6 ≤ m) →
        let a := fp8E4M3IntLevel e m
        let b := if m < 7 then fp8E4M3IntLevel e (m + 1) else fp8E4M3IntLevel (e + 1) 0
        driftBin ((a : Rat) / (fp8E4M3MaxInt : Rat)) ((b : Rat) / (fp8E4M3MaxInt : Rat)) 128 ≤
          127 / 2187))) := by
  refine ⟨fun N hN D s hs p q hsim hc => simplex_rtn_drift_upper_bound hN hs p q hsim hc,
          fun N u0 u1 hu0 hu1 => simplex_rtn_drift_attainment hu0 hu1, ?_⟩
  have hlt : ∀ a b c d : Nat, 0 < b → 0 < d → a * d < c * b →
      ((a : Rat) / (b : Rat)) < ((c : Rat) / (d : Rat)) := by
    intro a b c d hb hd h
    apply rat_div_lt_div_of_cross (rat_natCast_pos hb) (rat_natCast_pos hd)
    have h1 := rat_natCast_lt h
    simpa only [Rat.natCast_mul] using h1
  refine ⟨⟨drift_sE2M1_128, ?_⟩, ⟨drift_uE0M4_128, ?_⟩, ⟨drift_uE3M1_128, ?_⟩,
          drift_fp8E4M3_128_all_bins.1, ?_, drift_fp8E4M3_128_all_bins.2⟩
  · rw [drift_sE2M1_128]; exact hlt 84 100 127 151 (by omega) (by omega) (by omega)
  · rw [drift_uE0M4_128]; exact hlt 80 100 127 157 (by omega) (by omega) (by omega)
  · rw [drift_uE3M1_128]; exact hlt 127 511 25 100 (by omega) (by omega) (by omega)
  · exact hlt 127 2187 6 100 (by omega) (by omega) (by omega)

/-! ### Theorem 4: Pair-Antithetic SR & Zero-Carry Stratified XOR-VDC SR -/

/-- Single pair-antithetic cancellation at midpoint `k = 2^(b - 1)` for `b ≥ 1` and `u < 2^b`. -/
theorem pair_antithetic_srBit_midpoint {b u : Nat} (hb : 1 ≤ b) (hu : u < 2 ^ b) :
    srBit (2 ^ (b - 1)) u + srBit (2 ^ (b - 1)) ((2 ^ b - 1) - u) = 1 := by
  have h2 : 2 ^ b = 2 * 2 ^ (b - 1) := by
    have heq : b = (b - 1) + 1 := by omega
    conv => lhs; rw [heq]
    rw [Nat.pow_succ, Nat.mul_comm]
  unfold srBit
  split <;> split <;> omega

/-- Bit-reversal accumulator shift identity: `bitRevAux b x acc = acc * 2^b + bitRev b x`. -/
theorem bitRevAux_eq (b x acc : Nat) :
    bitRevAux b x acc = acc * 2 ^ b + bitRev b x := by
  induction b generalizing x acc with
  | zero => simp [bitRevAux, bitRev]
  | succ b ih =>
    unfold bitRev
    simp only [bitRevAux]
    rw [ih (x / 2) (2 * acc + x % 2), ih (x / 2) (2 * 0 + x % 2)]
    rw [Nat.pow_succ]
    have h0 : 2 * 0 + x % 2 = x % 2 := by omega
    rw [h0]
    have hmul : (2 * acc + x % 2) * 2 ^ b = acc * (2 ^ b * 2) + (x % 2) * 2 ^ b := by
      rw [Nat.add_mul]
      congr 1
      rw [Nat.mul_comm 2 acc, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ b)]
    omega

theorem bitRev_succ (b x : Nat) :
    bitRev (b + 1) x = (x % 2) * 2 ^ b + bitRev b (x / 2) := by
  unfold bitRev
  simp only [bitRevAux]
  rw [bitRevAux_eq]
  have h0 : 2 * 0 + x % 2 = x % 2 := by omega
  rw [h0]; rfl

theorem bitRev_lt (b x : Nat) : bitRev b x < 2 ^ b := by
  induction b generalizing x with
  | zero => simp [bitRev, bitRevAux]
  | succ b ih =>
    rw [bitRev_succ, Nat.pow_succ]
    have hmod : x % 2 ≤ 1 := by omega
    have hsub := ih (x / 2)
    have hmul : (x % 2) * 2 ^ b ≤ 2 ^ b := by
      have := Nat.mul_le_mul_right (2 ^ b) hmod
      simpa using this
    omega

private theorem bitRev_shift_add (b r y : Nat) (hr : r < 2) (hy : y < 2 ^ b) :
    bitRev (b + 1) (r * 2 ^ b + y) = 2 * bitRev b y + r := by
  induction b generalizing y with
  | zero =>
    have hy0 : y = 0 := by simp at hy; omega
    subst hy0
    simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
    rw [bitRev_succ]
    simp [bitRev, bitRevAux]
    omega
  | succ b ih =>
    rw [bitRev_succ (b + 1) (r * 2 ^ (b + 1) + y)]
    have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
    have hmod : (r * 2 ^ (b + 1) + y) % 2 = y % 2 := by
      rw [h2]
      have : r * (2 * 2 ^ b) + y = 2 * (r * 2 ^ b) + y := by
        rw [Nat.mul_left_comm]
      rw [this]; omega
    have hdiv : (r * 2 ^ (b + 1) + y) / 2 = r * 2 ^ b + y / 2 := by
      rw [h2]
      have : r * (2 * 2 ^ b) + y = 2 * (r * 2 ^ b) + y := by
        rw [Nat.mul_left_comm]
      rw [this]; omega
    rw [hmod, hdiv, ih (y / 2) (by rw [h2] at hy; omega), bitRev_succ b y]
    rw [h2]
    have hmul : (y % 2) * (2 * 2 ^ b) = 2 * ((y % 2) * 2 ^ b) := by
      rw [Nat.mul_left_comm]
    omega

/-- `bitRev b` is an exact involution on `{0, ..., 2^b - 1}`. -/
theorem bitRev_invol (b x : Nat) (hx : x < 2 ^ b) :
    bitRev b (bitRev b x) = x := by
  induction b generalizing x with
  | zero => simp [bitRev, bitRevAux]; simp at hx; omega
  | succ b ih =>
    rw [bitRev_succ b x]
    have hlt : bitRev b (x / 2) < 2 ^ b := bitRev_lt b (x / 2)
    rw [bitRev_shift_add b (x % 2) (bitRev b (x / 2)) (by omega) hlt]
    have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [ih (x / 2) (by rw [h2] at hx; omega)]
    omega

/-- `xorVdcThreshold b mask` stays inside `{0, ..., 2^b - 1}` for `mask < 2^b`. -/
theorem xorVdcThreshold_lt (b mask j : Nat) (hmask : mask < 2 ^ b) :
    xorVdcThreshold b mask j < 2 ^ b := by
  unfold xorVdcThreshold
  exact Nat.xor_lt_two_pow (bitRev_lt b j) hmask

/-- Exact two-sided inverse of `xorVdcThreshold b mask` on `{0, ..., 2^b - 1}`. -/
theorem xorVdcThreshold_inv (b mask j : Nat) (hmask : mask < 2 ^ b) (hj : j < 2 ^ b) :
    bitRev b ((xorVdcThreshold b mask j) ^^^ mask) = j ∧
    xorVdcThreshold b mask (bitRev b (j ^^^ mask)) = j := by
  unfold xorVdcThreshold
  constructor
  · rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    exact bitRev_invol b j hj
  · have hlt : j ^^^ mask < 2 ^ b := Nat.xor_lt_two_pow hj hmask
    rw [bitRev_invol b (j ^^^ mask) hlt, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-! ### Permutation Invariance of `sumFinNat` (Pure `Init`) -/

private theorem sumFinNat_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    sumFinNat f = sumFinNat g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFinNat]
    rw [ih (fun i => h i.castSucc), h (Fin.last n)]

private theorem sumFinNat_update_add {n : Nat} (f : Fin n → Nat) (p : Fin n) (v : Nat) :
    sumFinNat (fun i => if i = p then v else f i) + f p = sumFinNat f + v := by
  induction n with
  | zero => exact Fin.elim0 p
  | succ n ih =>
    simp only [sumFinNat]
    cases p using Fin.lastCases with
    | last =>
      have hne : ∀ i : Fin n, i.castSucc ≠ Fin.last n := fun i h => by
        have := congrArg Fin.val h; simp at this; omega
      have hcongr : sumFinNat (fun i : Fin n => if i.castSucc = Fin.last n then v else f i.castSucc) =
          sumFinNat (fun i : Fin n => f i.castSucc) :=
        sumFinNat_congr (fun i => by simp [hne i])
      simp only [↓reduceIte, hcongr]
      omega
    | cast p' =>
      have hne : Fin.last n ≠ p'.castSucc := fun h => by
        have := congrArg Fin.val h; simp at this; omega
      have hcongr : sumFinNat (fun i : Fin n => if i.castSucc = p'.castSucc then v else f i.castSucc) =
          sumFinNat (fun i : Fin n => if i = p' then v else f i.castSucc) :=
        sumFinNat_congr (fun i => by
          by_cases heq : i = p'
          · subst heq; simp
          · have hneq : i.castSucc ≠ p'.castSucc := fun h => heq (Fin.ext (by
              have := congrArg Fin.val h; simpa using this))
            simp [heq, hneq])
      simp only [hne, ↓reduceIte, hcongr]
      have hrec := ih (fun i : Fin n => f i.castSucc) p'
      omega

private theorem sumFinNat_swap {n : Nat} (f : Fin n → Nat) (a b : Fin n) :
    sumFinNat (fun i => f (if i = a then b else if i = b then a else i)) = sumFinNat f := by
  by_cases hab : a = b
  · subst hab
    exact sumFinNat_congr (fun i => by split <;> simp_all)
  · let g : Fin n → Nat := fun i => if i = b then f a else f i
    have h1 : sumFinNat (fun i => if i = a then f b else g i) + g a = sumFinNat g + f b :=
      sumFinNat_update_add g a (f b)
    have h2 : sumFinNat g + f b = sumFinNat f + f a :=
      sumFinNat_update_add f b (f a)
    have hga : g a = f a := by simp only [g, hab, ↓reduceIte]
    have hcongr : sumFinNat (fun i => f (if i = a then b else if i = b then a else i)) =
        sumFinNat (fun i => if i = a then f b else g i) :=
      sumFinNat_congr (fun i => by
        by_cases hia : i = a
        · simp only [hia, ↓reduceIte]
        · by_cases hib : i = b
          · simp only [hib, Ne.symm hab, ↓reduceIte, g]
          · simp only [hia, hib, ↓reduceIte, g])
    rw [hcongr]
    omega

/-- Any bijection on `Fin n` preserves `sumFinNat`. -/
theorem sumFinNat_bijection {n : Nat} (f : Fin n → Nat) (π πInv : Fin n → Fin n)
    (hL : ∀ i, πInv (π i) = i) (hR : ∀ i, π (πInv i) = i) :
    sumFinNat (fun j => f (π j)) = sumFinNat f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let j0 : Fin (n + 1) := πInv (Fin.last n)
    let swap : Fin (n + 1) → Fin (n + 1) :=
      fun i => if i = j0 then Fin.last n else if i = Fin.last n then j0 else i
    have hswap_invol : ∀ i, swap (swap i) = i := by
      intro i
      dsimp only [swap]
      by_cases hj : j0 = Fin.last n
      · rw [hj]
        by_cases hi : i = Fin.last n
        · simp only [hi, ↓reduceIte]
        · simp only [hi, ↓reduceIte]
      · by_cases hi1 : i = j0
        · subst hi1; simp only [↓reduceIte, Ne.symm hj]
        · by_cases hi2 : i = Fin.last n
          · subst hi2; simp only [↓reduceIte, Ne.symm hj]
          · simp only [hi1, hi2, ↓reduceIte]
    let ρ : Fin (n + 1) → Fin (n + 1) := fun i => π (swap i)
    let ρInv : Fin (n + 1) → Fin (n + 1) := fun i => swap (πInv i)
    have hρ_last : ρ (Fin.last n) = Fin.last n := by
      dsimp only [ρ, swap]
      by_cases hj : Fin.last n = j0
      · simp only [hj, ↓reduceIte]
        exact (hR (Fin.last n)).trans hj
      · simp only [hj, ↓reduceIte]
        dsimp only [j0]; exact hR (Fin.last n)
    have hρ_inj : ∀ i j, ρ i = ρ j → i = j := by
      intro i j h
      have h1 : swap i = swap j := by
        have := congrArg πInv h
        simpa [ρ, hL] using this
      have := congrArg swap h1
      simpa [hswap_invol] using this
    have hρ_lt : ∀ i : Fin n, (ρ i.castSucc).val < n := by
      intro i
      have hne : ρ i.castSucc ≠ Fin.last n := by
        intro heq
        have hi := hρ_inj i.castSucc (Fin.last n) (heq.trans hρ_last.symm)
        have := congrArg Fin.val hi; simp at this; omega
      have hle := (ρ i.castSucc).isLt
      have : (ρ i.castSucc).val ≠ n := fun h => hne (Fin.ext h)
      omega
    have hρInv_lt : ∀ i : Fin n, (ρInv i.castSucc).val < n := by
      intro i
      have hne : ρInv i.castSucc ≠ Fin.last n := by
        intro heq
        have h1 : π (swap (ρInv i.castSucc)) = Fin.last n := by
          rw [heq]; exact hρ_last
        have h2 : swap (ρInv i.castSucc) = πInv i.castSucc := hswap_invol (πInv i.castSucc)
        rw [h2, hR] at h1
        have := congrArg Fin.val h1; simp at this; omega
      have hle := (ρInv i.castSucc).isLt
      have : (ρInv i.castSucc).val ≠ n := fun h => hne (Fin.ext h)
      omega
    let ρ' : Fin n → Fin n := fun i => ⟨(ρ i.castSucc).val, hρ_lt i⟩
    let ρInv' : Fin n → Fin n := fun i => ⟨(ρInv i.castSucc).val, hρInv_lt i⟩
    have hL' : ∀ i : Fin n, ρInv' (ρ' i) = i := by
      intro i
      apply Fin.ext
      have hcast : (ρ' i).castSucc = ρ i.castSucc := Fin.ext rfl
      change (ρInv (ρ' i).castSucc).val = i.val
      rw [hcast]
      dsimp only [ρInv, ρ]
      rw [hL, hswap_invol]; rfl
    have hR' : ∀ i : Fin n, ρ' (ρInv' i) = i := by
      intro i
      apply Fin.ext
      have hcast : (ρInv' i).castSucc = ρInv i.castSucc := Fin.ext rfl
      change (ρ (ρInv' i).castSucc).val = i.val
      rw [hcast]
      dsimp only [ρInv, ρ]
      rw [hswap_invol, hR]; rfl
    have hstep : sumFinNat (fun j => f (π j)) = sumFinNat (fun j => f (ρ j)) :=
      (sumFinNat_swap (fun j => f (π j)) j0 (Fin.last n)).symm
    rw [hstep]
    simp only [sumFinNat, hρ_last]
    have hrec := ih (fun i : Fin n => f i.castSucc) ρ' ρInv' hL' hR'
    have hcongr : sumFinNat (fun i : Fin n => f (ρ i.castSucc)) =
        sumFinNat (fun i : Fin n => f (ρ' i).castSucc) :=
      sumFinNat_congr (fun i => by
        have hcast : (ρ' i).castSucc = ρ i.castSucc := Fin.ext rfl
        rw [hcast])
    rw [hcongr, hrec]

theorem sumFinNat_srBit_id (n k : Nat) (hk : k ≤ n) :
    sumFinNat (fun j : Fin n => srBit k j.val) = k := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0; rfl
  | succ n ih =>
    simp only [sumFinNat, Fin.val_castSucc, Fin.val_last]
    by_cases hkn : k ≤ n
    · have hlast : srBit k n = 0 := by unfold srBit; simp [Nat.not_lt.mpr hkn]
      rw [hlast, Nat.add_zero]
      exact ih k hkn
    · have hkeq : k = n + 1 := by omega
      subst hkeq
      have hlast : srBit (n + 1) n = 1 := by unfold srBit; simp
      have hcongr : sumFinNat (fun i : Fin n => srBit (n + 1) i.val) =
          sumFinNat (fun i : Fin n => srBit n i.val) :=
        sumFinNat_congr (fun i => by unfold srBit; simp [i.isLt, Nat.lt_succ_of_lt i.isLt])
      rw [hlast, hcongr, ih n (Nat.le_refl n)]

/-- Exact zero-carry count for stratified XOR-VDC SR:
    for ANY `b : Nat`, `mask < 2^b`, and dyadic numerator `k ≤ 2^b`,
    exactly `k` out of `2^b` coordinates round up! -/
theorem xorVdc_srBit_exact_sum (b mask k : Nat) (hmask : mask < 2 ^ b) (hk : k ≤ 2 ^ b) :
    sumFinNat (fun j : Fin (2 ^ b) => srBit k (xorVdcThreshold b mask j.val)) = k := by
  let π : Fin (2 ^ b) → Fin (2 ^ b) :=
    fun j => ⟨xorVdcThreshold b mask j.val, xorVdcThreshold_lt b mask j.val hmask⟩
  let πInv : Fin (2 ^ b) → Fin (2 ^ b) :=
    fun j => ⟨bitRev b (j.val ^^^ mask), bitRev_lt b (j.val ^^^ mask)⟩
  have hL : ∀ j : Fin (2 ^ b), πInv (π j) = j := fun j =>
    Fin.ext (xorVdcThreshold_inv b mask j.val hmask j.isLt).1
  have hR : ∀ j : Fin (2 ^ b), π (πInv j) = j := fun j =>
    Fin.ext (xorVdcThreshold_inv b mask j.val hmask j.isLt).2
  have hbij := sumFinNat_bijection (fun j : Fin (2 ^ b) => srBit k j.val) π πInv hL hR
  exact hbij.trans (sumFinNat_srBit_id (2 ^ b) k hk)

/-- Headline Theorem 4: Exact zero simplex-sum drift for pair-antithetic SR on midpoint rows
    and for zero-carry stratified XOR-VDC SR across ALL dyadic fractional residues `f = k / 2^b`. -/
theorem stratified_xor_vdc_simplex_zero_drift :
    (∀ b u : Nat, 1 ≤ b → u < 2 ^ b →
      srBit (2 ^ (b - 1)) u + srBit (2 ^ (b - 1)) ((2 ^ b - 1) - u) = 1) ∧
    (∀ (b m : Nat) (s u0 Δ : Rat) (u : Fin m → Nat),
      1 ≤ b → (∀ i, u i < 2 ^ b) →
      s + sumFin (fun _ : Fin m => 2 * (s * (u0 + (1 / 2 : Rat) * Δ))) = 1 →
      let qPair : Fin m → Rat := fun i =>
        s * (u0 + ((srBit (2 ^ (b - 1)) (u i) : Nat) : Rat) * Δ) +
        s * (u0 + ((srBit (2 ^ (b - 1)) ((2 ^ b - 1) - u i) : Nat) : Rat) * Δ)
      ratAbs (1 - (s + sumFin qPair)) = 0) ∧
    (∀ b mask k : Nat, mask < 2 ^ b → k ≤ 2 ^ b →
      sumFinNat (fun j : Fin (2 ^ b) => srBit k (xorVdcThreshold b mask j.val)) = k) ∧
    (∀ (b mask k : Nat) (s u0 Δ : Rat),
      mask < 2 ^ b → k ≤ 2 ^ b →
      let f : Rat := (k : Rat) / ((2 ^ b : Nat) : Rat)
      s + sumFin (fun _ : Fin (2 ^ b) => s * (u0 + f * Δ)) = 1 →
      let qVdc : Fin (2 ^ b) → Rat := fun j =>
        s * (u0 + ((srBit k (xorVdcThreshold b mask j.val) : Nat) : Rat) * Δ)
      ratAbs (1 - (s + sumFin qVdc)) = 0) := by
  refine ⟨fun b u hb hu => pair_antithetic_srBit_midpoint hb hu, ?_,
          fun b mask k hm hk => xorVdc_srBit_exact_sum b mask k hm hk, ?_⟩
  · intro b m s u0 Δ u hb hu hsim qPair
    have hpair_eq : ∀ i : Fin m, qPair i = 2 * (s * (u0 + (1 / 2 : Rat) * Δ)) := by
      intro i
      dsimp only [qPair]
      have h1 := pair_antithetic_srBit_midpoint hb (hu i)
      have hcast : ((srBit (2 ^ (b - 1)) (u i) : Nat) : Rat) +
          ((srBit (2 ^ (b - 1)) ((2 ^ b - 1) - u i) : Nat) : Rat) = 1 := by
        rw [← Rat.natCast_add, h1]; rfl
      grind
    have hsum : sumFin qPair = sumFin (fun _ : Fin m => 2 * (s * (u0 + (1 / 2 : Rat) * Δ))) := by
      have : qPair = (fun _ : Fin m => 2 * (s * (u0 + (1 / 2 : Rat) * Δ))) := funext hpair_eq
      rw [this]
    rw [hsum, hsim]
    have h0 : (1 : Rat) - 1 = 0 := by grind
    rw [h0, ratAbs_of_nonneg Rat.le_refl]
  · intro b mask k s u0 Δ hmask hk f hsim qVdc
    have hpow_pos : (0 : Rat) < ((2 ^ b : Nat) : Rat) :=
      rat_natCast_pos (Nat.pow_pos (by omega))
    have hpow_ne : ((2 ^ b : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hpow_pos
    have hsum_bits :
        sumFin (fun j : Fin (2 ^ b) => ((srBit k (xorVdcThreshold b mask j.val) : Nat) : Rat)) =
        (k : Rat) := by
      rw [← sumFinNat_cast, xorVdc_srBit_exact_sum b mask k hmask hk]
    have hq_eq : sumFin qVdc = ((2 ^ b : Nat) : Rat) * (s * u0) + (k : Rat) * (s * Δ) := by
      have hsplit : qVdc = fun j => s * u0 + ((srBit k (xorVdcThreshold b mask j.val) : Nat) : Rat) * (s * Δ) := by
        funext j; dsimp only [qVdc]; grind
      rw [hsplit, sumFin_add, sumFin_const, sumFin_mul_right, hsum_bits]
    have hp_eq : sumFin (fun _ : Fin (2 ^ b) => s * (u0 + f * Δ)) =
        ((2 ^ b : Nat) : Rat) * (s * u0) + (k : Rat) * (s * Δ) := by
      rw [sumFin_const]
      dsimp only [f]
      have hcancel : ((2 ^ b : Nat) : Rat) * ((k : Rat) / ((2 ^ b : Nat) : Rat)) = (k : Rat) :=
        rat_mul_div_cancel hpow_ne
      grind
    rw [hq_eq, ← hp_eq, hsim]
    have h0 : (1 : Rat) - 1 = 0 := by grind
    rw [h0, ratAbs_of_nonneg Rat.le_refl]

end UnsignedFp4SoftmaxV
