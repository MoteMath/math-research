/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EmbedZipfLazyStamp.RatOrder

/-!
# Theorem 2: Rare-Token RNE Weight-Update Flush & FP8 Subnormal Underflow

Pure-`Init` universal IEEE-754 / OCP Round-to-Nearest-Even (RNE) theorems:
1. Weight update `Δw` flushes identically to `0` whenever `|Δw| < (1/2) ulp_F(w) = 2^(e_w - M - 1)`
   (and at exact half-ULP when the grid index `q` is even).
2. Half-ULP over-rounding window: when `(1/2) ulp < Δw < ulp`, RNE rounds up to a full ULP.
3. Unscaled `FP8` gradient storage flushes identically to `0` whenever `|g| ≤ 2^-10` (`FP8-E4M3FN`)
   or `|g| ≤ 2^-17` (`FP8-E5M2`).
4. Explicit Zipf-rank flush thresholds for `BF16`, `FP16`, `FP8-E5M2`, and `FP8-E4M3FN`.
-/

namespace EmbedZipfLazyStamp

/-! ### Exact `Rat` Decomposition & Universal RNE Grid Theorems -/

theorem int_ediv_emod_unique {n d q rem : Int} (hd : 0 < d) (heq : n = d * q + rem)
    (hlo : 0 ≤ rem) (hhi : rem < d) : n / d = q ∧ n % d = rem := by
  have hq : n / d = q := by
    rw [heq, Int.mul_add_ediv_left q rem (Int.ne_of_gt hd), Int.ediv_eq_zero_of_lt hlo hhi, Int.add_zero]
  have hrem : n % d = rem := by
    have hmul := Int.mul_ediv_add_emod n d
    rw [hq] at hmul
    omega
  exact ⟨hq, hrem⟩

theorem rat_mul_den_eq_num (r : Rat) : r * ((r.den : Int) : Rat) = (r.num : Rat) := by
  rw [Rat.mul_def, Rat.normalize_eq_mkRat]
  have h1 : ((r.den : Int) : Rat).num = (r.den : Int) := rfl
  have h2 : ((r.den : Int) : Rat).den = 1 := rfl
  rw [h1, h2, Nat.mul_one]
  conv => lhs; arg 2; rw [← Nat.one_mul r.den]
  rw [Rat.mkRat_mul_right r.den_nz]
  exact Rat.mkRat_one r.num

theorem rneInt_eq_of_strict_half (k : Int) (ε : Rat)
    (hlo : -(1 / 2 : Rat) < ε) (hhi : ε < 1 / 2) :
    rneInt ((k : Rat) + ε) = k := by
  let r : Rat := (k : Rat) + ε
  let d : Int := (r.den : Int)
  have hd_pos : 0 < d := by
    change 0 < (r.den : Int)
    have := Nat.pos_of_ne_zero r.den_nz
    omega
  have hd_rat : (0 : Rat) < (d : Rat) := rat_natCast_pos (Nat.pos_of_ne_zero r.den_nz)
  have hnum_eq : (r.num : Rat) = (k : Rat) * (d : Rat) + ε * (d : Rat) := by
    have h := rat_mul_den_eq_num r
    change ((k : Rat) + ε) * (d : Rat) = (r.num : Rat) at h
    grind
  have h2d_pos : (0 : Rat) < 2 * (d : Rat) := rat_mul_pos (by decide) hd_rat
  have hlt1 : (-(1 / 2 : Rat)) * (2 * (d : Rat)) < ε * (2 * (d : Rat)) :=
    rat_mul_lt_mul_of_pos_right hlo h2d_pos
  have hlt2 : ε * (2 * (d : Rat)) < (1 / 2 : Rat) * (2 * (d : Rat)) :=
    rat_mul_lt_mul_of_pos_right hhi h2d_pos
  have hlo_rat : (((2 * k - 1) * d : Int) : Rat) < ((2 * r.num : Int) : Rat) := by
    have h1 : (((2 * k - 1) * d : Int) : Rat) = 2 * (k : Rat) * (d : Rat) - (d : Rat) := by
      rw [Rat.intCast_mul, Rat.intCast_sub, Rat.intCast_mul]; grind
    have h2 : ((2 * r.num : Int) : Rat) = 2 * (k : Rat) * (d : Rat) + ε * (2 * (d : Rat)) := by
      rw [Rat.intCast_mul, hnum_eq]; grind
    have h3 : -(1 / 2 : Rat) * (2 * (d : Rat)) = -(d : Rat) := by grind
    rw [h3] at hlt1
    rw [h1, h2]
    have := rat_sub_pos hlt1
    have hdiff : (0 : Rat) < (2 * (k : Rat) * (d : Rat) + ε * (2 * (d : Rat))) -
        (2 * (k : Rat) * (d : Rat) - (d : Rat)) := by grind
    exact rat_lt_of_sub_pos hdiff
  have hhi_rat : ((2 * r.num : Int) : Rat) < (((2 * k + 1) * d : Int) : Rat) := by
    have h1 : (((2 * k + 1) * d : Int) : Rat) = 2 * (k : Rat) * (d : Rat) + (d : Rat) := by
      rw [Rat.intCast_mul, Rat.intCast_add, Rat.intCast_mul]; grind
    have h2 : ((2 * r.num : Int) : Rat) = 2 * (k : Rat) * (d : Rat) + ε * (2 * (d : Rat)) := by
      rw [Rat.intCast_mul, hnum_eq]; grind
    have h3 : (1 / 2 : Rat) * (2 * (d : Rat)) = (d : Rat) := by grind
    rw [h3] at hlt2
    rw [h1, h2]
    have := rat_sub_pos hlt2
    have hdiff : (0 : Rat) < (2 * (k : Rat) * (d : Rat) + (d : Rat)) -
        (2 * (k : Rat) * (d : Rat) + ε * (2 * (d : Rat))) := by grind
    exact rat_lt_of_sub_pos hdiff
  have hlo_int : (2 * k - 1) * d < 2 * r.num := Rat.intCast_lt_intCast.mp hlo_rat
  have hhi_int : 2 * r.num < (2 * k + 1) * d := Rat.intCast_lt_intCast.mp hhi_rat
  have hlo_lin : 2 * (d * k) - d < 2 * r.num := by
    have : (2 * k - 1) * d = 2 * (d * k) - d := by grind
    omega
  have hhi_lin : 2 * r.num < 2 * (d * k) + d := by
    have : (2 * k + 1) * d = 2 * (d * k) + d := by grind
    omega
  unfold rneInt
  change (let q := r.num / d; let rem := r.num % d;
    if 2 * rem < d then q else if 2 * rem > d then q + 1 else if q % 2 == 0 then q else q + 1) = k
  by_cases hge : d * k ≤ r.num
  · have ⟨hq, hrem⟩ := int_ediv_emod_unique (n := r.num) hd_pos (q := k) (rem := r.num - d * k)
      (by omega) (by omega) (by omega)
    have h2rem : 2 * (r.num % d) < d := by omega
    simp [hq, h2rem]
  · have hstep : d * (k - 1) = d * k - d := by grind
    have ⟨hq, hrem⟩ := int_ediv_emod_unique (n := r.num) hd_pos (q := k - 1) (rem := r.num - d * (k - 1))
      (by omega) (by omega) (by omega)
    have h2rem_gt : 2 * (r.num % d) > d := by omega
    have h2rem_nlt : ¬ (2 * (r.num % d) < d) := by omega
    simp [hq, h2rem_nlt, h2rem_gt]

theorem rneInt_eq_of_even_half (k : Int) (hk : k % 2 = 0) (ε : Rat)
    (hlo : -(1 / 2 : Rat) ≤ ε) (hhi : ε ≤ 1 / 2) :
    rneInt ((k : Rat) + ε) = k := by
  let r : Rat := (k : Rat) + ε
  let d : Int := (r.den : Int)
  have hd_pos : 0 < d := by
    change 0 < (r.den : Int)
    have := Nat.pos_of_ne_zero r.den_nz
    omega
  have hd_rat : (0 : Rat) < (d : Rat) := rat_natCast_pos (Nat.pos_of_ne_zero r.den_nz)
  have hnum_eq : (r.num : Rat) = (k : Rat) * (d : Rat) + ε * (d : Rat) := by
    have h := rat_mul_den_eq_num r
    change ((k : Rat) + ε) * (d : Rat) = (r.num : Rat) at h
    grind
  have h2d_pos : (0 : Rat) < 2 * (d : Rat) := rat_mul_pos (by decide) hd_rat
  have hle1 : (-(1 / 2 : Rat)) * (2 * (d : Rat)) ≤ ε * (2 * (d : Rat)) :=
    rat_mul_le_mul_of_nonneg_right hlo (Rat.le_of_lt h2d_pos)
  have hle2 : ε * (2 * (d : Rat)) ≤ (1 / 2 : Rat) * (2 * (d : Rat)) :=
    rat_mul_le_mul_of_nonneg_right hhi (Rat.le_of_lt h2d_pos)
  have hlo_rat : (((2 * k - 1) * d : Int) : Rat) ≤ ((2 * r.num : Int) : Rat) := by
    have h1 : (((2 * k - 1) * d : Int) : Rat) = 2 * (k : Rat) * (d : Rat) - (d : Rat) := by
      rw [Rat.intCast_mul, Rat.intCast_sub, Rat.intCast_mul]; grind
    have h2 : ((2 * r.num : Int) : Rat) = 2 * (k : Rat) * (d : Rat) + ε * (2 * (d : Rat)) := by
      rw [Rat.intCast_mul, hnum_eq]; grind
    have h3 : -(1 / 2 : Rat) * (2 * (d : Rat)) = -(d : Rat) := by grind
    rw [h3] at hle1
    rw [h1, h2]
    have := rat_sub_nonneg hle1
    have hdiff : (0 : Rat) ≤ (2 * (k : Rat) * (d : Rat) + ε * (2 * (d : Rat))) -
        (2 * (k : Rat) * (d : Rat) - (d : Rat)) := by grind
    exact rat_le_of_sub_nonneg hdiff
  have hhi_rat : ((2 * r.num : Int) : Rat) ≤ (((2 * k + 1) * d : Int) : Rat) := by
    have h1 : (((2 * k + 1) * d : Int) : Rat) = 2 * (k : Rat) * (d : Rat) + (d : Rat) := by
      rw [Rat.intCast_mul, Rat.intCast_add, Rat.intCast_mul]; grind
    have h2 : ((2 * r.num : Int) : Rat) = 2 * (k : Rat) * (d : Rat) + ε * (2 * (d : Rat)) := by
      rw [Rat.intCast_mul, hnum_eq]; grind
    have h3 : (1 / 2 : Rat) * (2 * (d : Rat)) = (d : Rat) := by grind
    rw [h3] at hle2
    rw [h1, h2]
    have := rat_sub_nonneg hle2
    have hdiff : (0 : Rat) ≤ (2 * (k : Rat) * (d : Rat) + (d : Rat)) -
        (2 * (k : Rat) * (d : Rat) + ε * (2 * (d : Rat))) := by grind
    exact rat_le_of_sub_nonneg hdiff
  have hlo_int : (2 * k - 1) * d ≤ 2 * r.num := Rat.intCast_le_intCast.mp hlo_rat
  have hhi_int : 2 * r.num ≤ (2 * k + 1) * d := Rat.intCast_le_intCast.mp hhi_rat
  have hlo_lin : 2 * (d * k) - d ≤ 2 * r.num := by
    have : (2 * k - 1) * d = 2 * (d * k) - d := by grind
    omega
  have hhi_lin : 2 * r.num ≤ 2 * (d * k) + d := by
    have : (2 * k + 1) * d = 2 * (d * k) + d := by grind
    omega
  unfold rneInt
  change (let q := r.num / d; let rem := r.num % d;
    if 2 * rem < d then q else if 2 * rem > d then q + 1 else if q % 2 == 0 then q else q + 1) = k
  by_cases hge : d * k ≤ r.num
  · have ⟨hq, hrem⟩ := int_ediv_emod_unique (n := r.num) hd_pos (q := k) (rem := r.num - d * k)
      (by omega) (by omega) (by omega)
    by_cases hlt : 2 * (r.num % d) < d
    · simp [hq, hlt]
    · have hngt : ¬ (2 * (r.num % d) > d) := by omega
      simp [hq, hlt, hngt, hk]
  · have hstep : d * (k - 1) = d * k - d := by grind
    have ⟨hq, hrem⟩ := int_ediv_emod_unique (n := r.num) hd_pos (q := k - 1) (rem := r.num - d * (k - 1))
      (by omega) (by omega) (by omega)
    have hnlt : ¬ (2 * (r.num % d) < d) := by omega
    by_cases hgt : 2 * (r.num % d) > d
    · simp [hq, hnlt, hgt]
    · have hodd : (k - 1) % 2 ≠ 0 := by omega
      have hbeq : ((k - 1) % 2 == 0) = false := beq_false_of_ne hodd
      simp [hq, hnlt, hgt, hbeq]

theorem rneGrid_flush_strict (q : Int) (u dw : Rat) (hu : (0 : Rat) < u)
    (hdw : ratAbs dw < u / 2) :
    rneGrid u ((q : Rat) * u + dw) = (q : Rat) * u := by
  unfold rneGrid
  have hu_ne : u ≠ 0 := Rat.ne_of_gt hu
  have hdiv : ((q : Rat) * u + dw) / u = (q : Rat) + dw / u := by
    rw [rat_div_eq_iff hu_ne]
    have : ((q : Rat) + dw / u) * u = (q : Rat) * u + (dw / u) * u := by grind
    rw [this, rat_div_mul_cancel hu_ne]
  rw [hdiv]
  have ⟨hlo, hhi⟩ := ratAbs_lt_iff.mp hdw
  have hlo' : -(1 / 2 : Rat) < dw / u := by
    apply rat_lt_div_of_mul_lt hu
    have : -(1 / 2 : Rat) * u = -(u / 2) := by grind
    rw [this]; exact hlo
  have hhi' : dw / u < 1 / 2 := by
    apply rat_div_lt_of_mul_lt hu
    have : (1 / 2 : Rat) * u = u / 2 := by grind
    rw [this]; exact hhi
  rw [rneInt_eq_of_strict_half q (dw / u) hlo' hhi']

theorem rneGrid_flush_even (q : Int) (hq : q % 2 = 0) (u dw : Rat) (hu : (0 : Rat) < u)
    (hdw : ratAbs dw ≤ u / 2) :
    rneGrid u ((q : Rat) * u + dw) = (q : Rat) * u := by
  unfold rneGrid
  have hu_ne : u ≠ 0 := Rat.ne_of_gt hu
  have hdiv : ((q : Rat) * u + dw) / u = (q : Rat) + dw / u := by
    rw [rat_div_eq_iff hu_ne]
    have : ((q : Rat) + dw / u) * u = (q : Rat) * u + (dw / u) * u := by grind
    rw [this, rat_div_mul_cancel hu_ne]
  rw [hdiv]
  have ⟨hlo, hhi⟩ := ratAbs_le_iff.mp hdw
  have hlo' : -(1 / 2 : Rat) ≤ dw / u := by
    apply rat_le_div_of_mul_le hu
    have : -(1 / 2 : Rat) * u = -(u / 2) := by grind
    rw [this]; exact hlo
  have hhi' : dw / u ≤ 1 / 2 := by
    apply rat_div_le_of_mul_le hu
    have : (1 / 2 : Rat) * u = u / 2 := by grind
    rw [this]; exact hhi
  rw [rneInt_eq_of_even_half q hq (dw / u) hlo' hhi']

theorem rneGrid_overround_half_ulp (q : Int) (u dw : Rat) (hu : (0 : Rat) < u)
    (hlo : u / 2 < dw) (hhi : dw < u) :
    rneGrid u ((q : Rat) * u + dw) = ((q + 1 : Int) : Rat) * u ∧
    rneGrid u ((q : Rat) * u + dw) - (q : Rat) * u = u := by
  have hu_ne : u ≠ 0 := Rat.ne_of_gt hu
  have hsplit : (q : Rat) * u + dw = ((q + 1 : Int) : Rat) * u + (dw - u) := by
    rw [Rat.intCast_add]; grind
  have hdw' : ratAbs (dw - u) < u / 2 := by
    rw [ratAbs_lt_iff]
    constructor
    · have := rat_sub_pos hlo
      have : (0 : Rat) < (dw - u) - (-(u / 2)) := by grind
      exact rat_lt_of_sub_pos this
    · have := rat_sub_pos hhi
      have hneg : dw - u < 0 := by
        have : (0 : Rat) < 0 - (dw - u) := by grind
        exact rat_lt_of_sub_pos this
      exact rat_lt_trans hneg (rat_div_pos hu (by decide))
  have hr : rneGrid u ((q : Rat) * u + dw) = ((q + 1 : Int) : Rat) * u := by
    rw [hsplit]
    exact rneGrid_flush_strict (q + 1) u (dw - u) hu hdw'
  refine ⟨hr, ?_⟩
  rw [hr, Rat.intCast_add]
  grind

theorem rneGrid_subnormal_underflow (subMin g : Rat) (hs : (0 : Rat) < subMin)
    (hg : ratAbs g ≤ subMin / 2) :
    rneGrid subMin g = 0 := by
  have h0 : g = ((0 : Int) : Rat) * subMin + g := by grind
  rw [h0]
  have h := rneGrid_flush_even 0 (by omega) subMin g hs hg
  simpa using h

theorem halfUlpBinade_eq_ulp_div_two (e_w : Int) (M : Nat) :
    halfUlpBinade e_w M = ulpBinade e_w M / 2 := by
  unfold halfUlpBinade ulpBinade
  exact pow2Int_sub_one (e_w - (M : Int))

theorem zipf_weight_flush_of_rank (e_w : Int) (M : Nat) (q : Int)
    (Z η H p_r h : Rat) (r : Nat)
    (hZ : (0 : Rat) < Z) (hη : (0 : Rat) < η) (hr : 0 < r)
    (hp_pos : (0 : Rat) ≤ p_r) (hp : p_r ≤ 1 / (Z * (r : Rat)))
    (hh : ratAbs h ≤ H)
    (hr_thresh : (η * H) / (Z * halfUlpBinade e_w M) < (r : Rat)) :
    rneGrid (ulpBinade e_w M) ((q : Rat) * ulpBinade e_w M + η * p_r * h) -
      (q : Rat) * ulpBinade e_w M = 0 := by
  have hu_pos : (0 : Rat) < ulpBinade e_w M := pow2Int_pos _
  have hhalf_pos : (0 : Rat) < halfUlpBinade e_w M := pow2Int_pos _
  have hZr_pos : (0 : Rat) < Z * (r : Rat) := rat_mul_pos hZ (rat_natCast_pos hr)
  have hZhalf_pos : (0 : Rat) < Z * halfUlpBinade e_w M := rat_mul_pos hZ hhalf_pos
  have habs : ratAbs (η * p_r * h) < ulpBinade e_w M / 2 := by
    rw [← halfUlpBinade_eq_ulp_div_two]
    rw [ratAbs_mul, ratAbs_mul, ratAbs_of_nonneg (Rat.le_of_lt hη), ratAbs_of_nonneg hp_pos]
    have h1 : η * p_r * ratAbs h ≤ η * (1 / (Z * (r : Rat))) * H := by
      have hH_nn : (0 : Rat) ≤ H := Rat.le_trans (ratAbs_nonneg h) hh
      have hηp_le : η * p_r ≤ η * (1 / (Z * (r : Rat))) :=
        rat_mul_le_mul_of_nonneg_left hp (Rat.le_of_lt hη)
      have hηp_nn : (0 : Rat) ≤ η * p_r := Rat.mul_nonneg (Rat.le_of_lt hη) hp_pos
      exact Rat.le_trans (rat_mul_le_mul_of_nonneg_left hh hηp_nn)
        (rat_mul_le_mul_of_nonneg_right hηp_le hH_nn)
    have h2 : η * (1 / (Z * (r : Rat))) * H < halfUlpBinade e_w M := by
      have hmul : η * H < (r : Rat) * (Z * halfUlpBinade e_w M) := by
        have := rat_mul_lt_mul_of_pos_right hr_thresh hZhalf_pos
        rw [rat_div_mul_cancel (Rat.ne_of_gt hZhalf_pos)] at this
        exact this
      apply rat_lt_of_mul_pos_right hZr_pos
      have hlhs : η * (1 / (Z * (r : Rat))) * H * (Z * (r : Rat)) =
          (1 / (Z * (r : Rat)) * (Z * (r : Rat))) * (η * H) := by grind
      rw [hlhs, rat_div_mul_cancel (Rat.ne_of_gt hZr_pos), Rat.one_mul]
      have hrhs : halfUlpBinade e_w M * (Z * (r : Rat)) =
          (r : Rat) * (Z * halfUlpBinade e_w M) := by grind
      rw [hrhs]; exact hmul
    exact rat_lt_of_le_of_lt h1 h2
  rw [rneGrid_flush_strict q (ulpBinade e_w M) (η * p_r * h) hu_pos habs]
  grind

theorem zipf_fp8_grad_underflow_of_rank (subMin Z H p_r h : Rat) (r : Nat)
    (hs : (0 : Rat) < subMin) (hZ : (0 : Rat) < Z) (hr : 0 < r)
    (hp_pos : (0 : Rat) ≤ p_r) (hp : p_r ≤ 1 / (Z * (r : Rat)))
    (hh : ratAbs h ≤ H)
    (hr_thresh : H / (Z * (subMin / 2)) ≤ (r : Rat)) :
    rneGrid subMin (p_r * h) = 0 := by
  have hhalf_pos : (0 : Rat) < subMin / 2 := rat_div_pos hs (by decide)
  have hZr_pos : (0 : Rat) < Z * (r : Rat) := rat_mul_pos hZ (rat_natCast_pos hr)
  have hZhalf_pos : (0 : Rat) < Z * (subMin / 2) := rat_mul_pos hZ hhalf_pos
  apply rneGrid_subnormal_underflow subMin (p_r * h) hs
  rw [ratAbs_mul, ratAbs_of_nonneg hp_pos]
  have h1 : p_r * ratAbs h ≤ (1 / (Z * (r : Rat))) * H := by
    have hH_nn : (0 : Rat) ≤ H := Rat.le_trans (ratAbs_nonneg h) hh
    exact Rat.le_trans (rat_mul_le_mul_of_nonneg_left hh hp_pos)
      (rat_mul_le_mul_of_nonneg_right hp hH_nn)
  have h2 : (1 / (Z * (r : Rat))) * H ≤ subMin / 2 := by
    have hmul : H ≤ (r : Rat) * (Z * (subMin / 2)) := by
      have := rat_mul_le_mul_of_nonneg_right hr_thresh (Rat.le_of_lt hZhalf_pos)
      rw [rat_div_mul_cancel (Rat.ne_of_gt hZhalf_pos)] at this
      exact this
    apply rat_le_of_mul_pos_right hZr_pos
    have hlhs : 1 / (Z * (r : Rat)) * H * (Z * (r : Rat)) =
        (1 / (Z * (r : Rat)) * (Z * (r : Rat))) * H := by grind
    rw [hlhs, rat_div_mul_cancel (Rat.ne_of_gt hZr_pos), Rat.one_mul]
    have hrhs : subMin / 2 * (Z * (r : Rat)) = (r : Rat) * (Z * (subMin / 2)) := by grind
    rw [hrhs]; exact hmul
  exact Rat.le_trans h1 h2

/-- Headline Theorem 2 (`rare_token_rne_weight_flush_and_fp8_subnormal_underflow`):
    Universal IEEE-754 / OCP RNE half-ULP weight-update flush, half-ULP over-rounding window,
    `FP8-E4M3FN` (`2^-10`) and `FP8-E5M2` (`2^-17`) subnormal gradient blackout, and exact
    Zipf-rank flush thresholds across `BF16`, `FP16`, `FP8-E5M2`, and `FP8-E4M3FN`. -/
theorem rare_token_rne_weight_flush_and_fp8_subnormal_underflow :
    (∀ (e_w : Int) (M : Nat) (q : Int) (dw : Rat),
      ratAbs dw < halfUlpBinade e_w M →
      rneGrid (ulpBinade e_w M) ((q : Rat) * ulpBinade e_w M + dw) -
        (q : Rat) * ulpBinade e_w M = 0) ∧
    (∀ (e_w : Int) (M : Nat) (q : Int) (dw : Rat),
      halfUlpBinade e_w M < dw → dw < ulpBinade e_w M →
      rneGrid (ulpBinade e_w M) ((q : Rat) * ulpBinade e_w M + dw) -
        (q : Rat) * ulpBinade e_w M = ulpBinade e_w M) ∧
    (fp8E4M3MinSubnormal = 1 / 512 ∧ fp8E4M3HalfSubnormal = 1 / 1024 ∧
     (∀ g : Rat, ratAbs g ≤ fp8E4M3HalfSubnormal → rneGrid fp8E4M3MinSubnormal g = 0)) ∧
    (fp8E5M2MinSubnormal = 1 / 65536 ∧ fp8E5M2HalfSubnormal = 1 / 131072 ∧
     (∀ g : Rat, ratAbs g ≤ fp8E5M2HalfSubnormal → rneGrid fp8E5M2MinSubnormal g = 0)) ∧
    (halfUlpBinade (-5) 7 = 1 / 8192 ∧
     halfUlpBinade (-5) 10 = 1 / 65536 ∧
     halfUlpBinade (-5) 2 = 1 / 256 ∧
     halfUlpBinade (-5) 3 = 1 / 512) ∧
    (∀ (e_w : Int) (M : Nat) (q : Int) (Z η H p_r h : Rat) (r : Nat),
      (0 : Rat) < Z → (0 : Rat) < η → 0 < r →
      (0 : Rat) ≤ p_r → p_r ≤ 1 / (Z * (r : Rat)) → ratAbs h ≤ H →
      (η * H) / (Z * halfUlpBinade e_w M) < (r : Rat) →
      rneGrid (ulpBinade e_w M) ((q : Rat) * ulpBinade e_w M + η * p_r * h) -
        (q : Rat) * ulpBinade e_w M = 0) ∧
    (∀ (Z H p_r h : Rat) (r : Nat),
      (0 : Rat) < Z → 0 < r → (0 : Rat) ≤ p_r → p_r ≤ 1 / (Z * (r : Rat)) → ratAbs h ≤ H →
      (H / (Z * fp8E4M3HalfSubnormal) ≤ (r : Rat) → rneGrid fp8E4M3MinSubnormal (p_r * h) = 0) ∧
      (H / (Z * fp8E5M2HalfSubnormal) ≤ (r : Rat) → rneGrid fp8E5M2MinSubnormal (p_r * h) = 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e_w M q dw hdw
    rw [halfUlpBinade_eq_ulp_div_two] at hdw
    rw [rneGrid_flush_strict q (ulpBinade e_w M) dw (pow2Int_pos _) hdw]
    grind
  · intro e_w M q dw hlo hhi
    rw [halfUlpBinade_eq_ulp_div_two] at hlo
    exact (rneGrid_overround_half_ulp q (ulpBinade e_w M) dw (pow2Int_pos _) hlo hhi).2
  · refine ⟨by unfold fp8E4M3MinSubnormal pow2Int; rfl,
            by unfold fp8E4M3HalfSubnormal pow2Int; rfl, ?_⟩
    intro g hg
    have hhalf : fp8E4M3HalfSubnormal = fp8E4M3MinSubnormal / 2 := by
      unfold fp8E4M3HalfSubnormal fp8E4M3MinSubnormal
      exact pow2Int_sub_one (-9)
    rw [hhalf] at hg
    exact rneGrid_subnormal_underflow fp8E4M3MinSubnormal g (pow2Int_pos _) hg
  · refine ⟨by unfold fp8E5M2MinSubnormal pow2Int; rfl,
            by unfold fp8E5M2HalfSubnormal pow2Int; rfl, ?_⟩
    intro g hg
    have hhalf : fp8E5M2HalfSubnormal = fp8E5M2MinSubnormal / 2 := by
      unfold fp8E5M2HalfSubnormal fp8E5M2MinSubnormal
      exact pow2Int_sub_one (-16)
    rw [hhalf] at hg
    exact rneGrid_subnormal_underflow fp8E5M2MinSubnormal g (pow2Int_pos _) hg
  · refine ⟨by unfold halfUlpBinade pow2Int; rfl,
            by unfold halfUlpBinade pow2Int; rfl,
            by unfold halfUlpBinade pow2Int; rfl,
            by unfold halfUlpBinade pow2Int; rfl⟩
  · intro e_w M q Z η H p_r h r hZ hη hr hp_pos hp hh hr_thresh
    exact zipf_weight_flush_of_rank e_w M q Z η H p_r h r hZ hη hr hp_pos hp hh hr_thresh
  · intro Z H p_r h r hZ hr hp_pos hp hh
    have h4 : fp8E4M3HalfSubnormal = fp8E4M3MinSubnormal / 2 := by
      unfold fp8E4M3HalfSubnormal fp8E4M3MinSubnormal; exact pow2Int_sub_one (-9)
    have h5 : fp8E5M2HalfSubnormal = fp8E5M2MinSubnormal / 2 := by
      unfold fp8E5M2HalfSubnormal fp8E5M2MinSubnormal; exact pow2Int_sub_one (-16)
    exact ⟨fun ht => by rw [h4] at ht; exact zipf_fp8_grad_underflow_of_rank _ Z H p_r h r (pow2Int_pos _) hZ hr hp_pos hp hh ht,
           fun ht => by rw [h5] at ht; exact zipf_fp8_grad_underflow_of_rank _ Z H p_r h r (pow2Int_pos _) hZ hr hp_pos hp hh ht⟩

end EmbedZipfLazyStamp
