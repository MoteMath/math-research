/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import XorVdcFp4Dither.RatBasic

/-!
# Zero-Carry XOR-VDC Unbiasedness and Exact Closed-Form Pairwise Covariance (Theorem 1)

Proves for all `b ≤ m`:
1. Strict discrete unbiasedness: `E_{u0}[Q_SR(x; u0 ^^^ (bitrev_b(i) << (m - b)))] = x`
   for every coordinate `i`, every interval `[l, r]`, and every threshold `p ≤ 2^m`.
2. Exact closed-form pairwise average covariance over uniform `m`-bit `u0` and `p1, p2`:
   `avgDiscreteSrCov m (xorVdcLane m b i) (xorVdcLane m b j) = xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j)`.
-/

namespace XorVdcFp4Dither

/-! ### 1. Strict Discrete Unbiasedness -/

theorem srVal_mean_uniform (m : Nat) (l r : Rat) (p : Nat) (hp : p ≤ 2 ^ m) :
    discreteMean (2 ^ m) (fun u => srVal l r p u) =
    l + (r - l) * ((p : Rat) / ((2 ^ m : Nat) : Rat)) := by
  unfold discreteMean srVal
  have hrew : sumRange (2 ^ m) (fun u => if u < p then r else l) =
      sumRange (2 ^ m) (fun u => l + (r - l) * (if u < p then (1 : Rat) else 0)) := by
    apply sumRange_congr
    intro u _
    by_cases h : u < p <;> simp [h] <;> grind
  rw [hrew, sumRange_add, sumRange_const, sumRange_mul_left, sumRange_lt_indicator (2 ^ m) p hp]
  have hne : ((2 ^ m : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero m
  grind

theorem srVal_mean_xor (m d : Nat) (hd : d < 2 ^ m) (l r : Rat) (p : Nat) (hp : p ≤ 2 ^ m) :
    discreteMean (2 ^ m) (fun u => srVal l r p (u ^^^ d)) =
    l + (r - l) * ((p : Rat) / ((2 ^ m : Nat) : Rat)) := by
  unfold discreteMean
  rw [sumRange_xor m d hd (fun u => srVal l r p u)]
  exact srVal_mean_uniform m l r p hp

theorem xorVdcLane_unbiased (m b i : Nat) (hbm : b ≤ m) (l r : Rat) (p : Nat) (hp : p ≤ 2 ^ m) :
    discreteMean (2 ^ m) (fun u0 => srVal l r p (xorVdcLane m b i u0)) =
    l + (r - l) * ((p : Rat) / ((2 ^ m : Nat) : Rat)) :=
  srVal_mean_xor m (xorVdcOffset m b i) (xorVdcOffset_lt m b i hbm) l r p hp

theorem srErr_mean_xor (m d : Nat) (hd : d < 2 ^ m) (p : Nat) (hp : p ≤ 2 ^ m) :
    discreteMean (2 ^ m) (fun u => srErr p (2 ^ m) (u ^^^ d)) = 0 := by
  unfold discreteMean
  rw [sumRange_xor m d hd (fun u => srErr p (2 ^ m) u)]
  unfold srErr
  rw [sumRange_sub, sumRange_lt_indicator (2 ^ m) p hp, sumRange_const]
  have hne : ((2 ^ m : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero m
  grind

/-! ### 2. Exact Fubini Reduction for Discrete Average Covariance -/

theorem sumRange_gt_indicator (M v : Nat) (hv : v < M) :
    sumRange M (fun p => if v < p then (1 : Rat) else 0) = ((M : Rat) - 1 - (v : Rat)) := by
  induction M with
  | zero => omega
  | succ M ih =>
    simp only [sumRange]
    by_cases hlt : v < M
    · rw [ih hlt]
      simp only [hlt, ↓reduceIte]
      rw [rat_natCast_add]
      have h1 : ((1 : Nat) : Rat) = 1 := rfl
      rw [h1]
      grind
    · have hvEq : v = M := by omega
      subst hvEq
      have h0 : sumRange v (fun p => if v < p then (1 : Rat) else 0) = 0 := by
        have hcongr : sumRange v (fun p => if v < p then (1 : Rat) else 0) =
            sumRange v (fun _ => (0 : Rat)) := by
          apply sumRange_congr
          intro p hp
          have hnot : ¬ (v < p) := by omega
          simp [hnot]
        rw [hcongr, sumRange_const]
        grind
      have hnot : ¬ (v < v) := Nat.lt_irrefl v
      rw [h0]
      simp only [hnot, ↓reduceIte]
      rw [rat_natCast_add]
      have h1 : ((1 : Nat) : Rat) = 1 := rfl
      rw [h1]
      grind

theorem mean_srErr_over_p (M v : Nat) (hM : 0 < M) (hv : v < M) :
    discreteMean M (fun p => srErr p M v) =
    -(2 * (v : Rat) - ((M : Rat) - 1)) / (2 * (M : Rat)) := by
  unfold discreteMean srErr
  rw [sumRange_sub, sumRange_gt_indicator M v hv, sumRange_div_const, sumRange_nat_id]
  have hne : (M : Rat) ≠ 0 := rat_natCast_ne_zero hM
  grind

theorem avgDiscreteSrCov_xor_eq_centered_sum (m d1 d2 : Nat)
    (hd1 : d1 < 2 ^ m) (hd2 : d2 < 2 ^ m) :
    avgDiscreteSrCov m (fun u => u ^^^ d1) (fun u => u ^^^ d2) =
    sumRange (2 ^ m) (fun u =>
      (2 * ((u ^^^ d1 : Nat) : Rat) - (((2 ^ m : Nat) : Rat) - 1)) *
      (2 * ((u ^^^ d2 : Nat) : Rat) - (((2 ^ m : Nat) : Rat) - 1))) /
      (4 * ((2 ^ m : Nat) : Rat) * ((2 ^ m : Nat) : Rat) * ((2 ^ m : Nat) : Rat)) := by
  unfold avgDiscreteSrCov discreteCov discreteMean
  have hMpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hMne : ((2 ^ m : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero m
  have hinner :
      sumRange (2 ^ m) (fun p1 =>
        sumRange (2 ^ m) (fun p2 =>
          sumRange (2 ^ m) (fun u =>
            (srErr p1 (2 ^ m) (u ^^^ d1) -
              sumRange (2 ^ m) (fun u => srErr p1 (2 ^ m) (u ^^^ d1)) / ((2 ^ m : Nat) : Rat)) *
            (srErr p2 (2 ^ m) (u ^^^ d2) -
              sumRange (2 ^ m) (fun u => srErr p2 (2 ^ m) (u ^^^ d2)) / ((2 ^ m : Nat) : Rat))) /
          ((2 ^ m : Nat) : Rat)) /
        ((2 ^ m : Nat) : Rat)) / ((2 ^ m : Nat) : Rat) =
      sumRange (2 ^ m) (fun p1 =>
        sumRange (2 ^ m) (fun p2 =>
          sumRange (2 ^ m) (fun u =>
            srErr p1 (2 ^ m) (u ^^^ d1) * srErr p2 (2 ^ m) (u ^^^ d2)))) /
        (((2 ^ m : Nat) : Rat) * ((2 ^ m : Nat) : Rat) * ((2 ^ m : Nat) : Rat)) := by
    have hsimp :
        sumRange (2 ^ m) (fun p1 =>
          sumRange (2 ^ m) (fun p2 =>
            sumRange (2 ^ m) (fun u =>
              (srErr p1 (2 ^ m) (u ^^^ d1) -
                sumRange (2 ^ m) (fun u => srErr p1 (2 ^ m) (u ^^^ d1)) / ((2 ^ m : Nat) : Rat)) *
              (srErr p2 (2 ^ m) (u ^^^ d2) -
                sumRange (2 ^ m) (fun u => srErr p2 (2 ^ m) (u ^^^ d2)) / ((2 ^ m : Nat) : Rat))) /
            ((2 ^ m : Nat) : Rat)) /
          ((2 ^ m : Nat) : Rat)) =
        sumRange (2 ^ m) (fun p1 =>
          sumRange (2 ^ m) (fun p2 =>
            sumRange (2 ^ m) (fun u =>
              srErr p1 (2 ^ m) (u ^^^ d1) * srErr p2 (2 ^ m) (u ^^^ d2)) /
            ((2 ^ m : Nat) : Rat)) /
          ((2 ^ m : Nat) : Rat)) := by
      apply sumRange_congr
      intro p1 hp1
      congr 1
      apply sumRange_congr
      intro p2 hp2
      congr 1
      have h1 : sumRange (2 ^ m) (fun u => srErr p1 (2 ^ m) (u ^^^ d1)) / ((2 ^ m : Nat) : Rat) = 0 :=
        srErr_mean_xor m d1 hd1 p1 (Nat.le_of_lt hp1)
      have h2 : sumRange (2 ^ m) (fun u => srErr p2 (2 ^ m) (u ^^^ d2)) / ((2 ^ m : Nat) : Rat) = 0 :=
        srErr_mean_xor m d2 hd2 p2 (Nat.le_of_lt hp2)
      rw [h1, h2]
      apply sumRange_congr
      intro u _
      grind
    rw [hsimp]
    have hdiv1 :
        sumRange (2 ^ m) (fun p1 =>
          sumRange (2 ^ m) (fun p2 =>
            sumRange (2 ^ m) (fun u =>
              srErr p1 (2 ^ m) (u ^^^ d1) * srErr p2 (2 ^ m) (u ^^^ d2)) /
            ((2 ^ m : Nat) : Rat)) /
          ((2 ^ m : Nat) : Rat)) =
        sumRange (2 ^ m) (fun p1 =>
          sumRange (2 ^ m) (fun p2 =>
            sumRange (2 ^ m) (fun u =>
              srErr p1 (2 ^ m) (u ^^^ d1) * srErr p2 (2 ^ m) (u ^^^ d2)))) /
          (((2 ^ m : Nat) : Rat) * ((2 ^ m : Nat) : Rat)) := by
      rw [sumRange_div_const]
      have hcongr :
          sumRange (2 ^ m) (fun p1 =>
            sumRange (2 ^ m) (fun p2 =>
              sumRange (2 ^ m) (fun u =>
                srErr p1 (2 ^ m) (u ^^^ d1) * srErr p2 (2 ^ m) (u ^^^ d2)) /
              ((2 ^ m : Nat) : Rat))) =
          sumRange (2 ^ m) (fun p1 =>
            sumRange (2 ^ m) (fun p2 =>
              sumRange (2 ^ m) (fun u =>
                srErr p1 (2 ^ m) (u ^^^ d1) * srErr p2 (2 ^ m) (u ^^^ d2))) /
            ((2 ^ m : Nat) : Rat)) := by
        apply sumRange_congr
        intro p1 _
        exact sumRange_div_const (2 ^ m) _ _
      rw [hcongr, sumRange_div_const]
      grind
    rw [hdiv1]
    grind
  rw [hinner]
  -- Swap sums: ∑_{p1} ∑_{p2} ∑_{u} = ∑_{u} (∑_{p1} srErr) * (∑_{p2} srErr)
  have hswap1 :
      sumRange (2 ^ m) (fun p1 =>
        sumRange (2 ^ m) (fun p2 =>
          sumRange (2 ^ m) (fun u =>
            srErr p1 (2 ^ m) (u ^^^ d1) * srErr p2 (2 ^ m) (u ^^^ d2)))) =
      sumRange (2 ^ m) (fun p1 =>
        sumRange (2 ^ m) (fun u =>
          sumRange (2 ^ m) (fun p2 =>
            srErr p1 (2 ^ m) (u ^^^ d1) * srErr p2 (2 ^ m) (u ^^^ d2)))) := by
    apply sumRange_congr
    intro p1 _
    exact sumRange_swap (2 ^ m) (2 ^ m) _
  rw [hswap1, sumRange_swap (2 ^ m) (2 ^ m)]
  have hfactor :
      sumRange (2 ^ m) (fun u =>
        sumRange (2 ^ m) (fun p1 =>
          sumRange (2 ^ m) (fun p2 =>
            srErr p1 (2 ^ m) (u ^^^ d1) * srErr p2 (2 ^ m) (u ^^^ d2)))) =
      sumRange (2 ^ m) (fun u =>
        (sumRange (2 ^ m) (fun p1 => srErr p1 (2 ^ m) (u ^^^ d1))) *
        (sumRange (2 ^ m) (fun p2 => srErr p2 (2 ^ m) (u ^^^ d2)))) := by
    apply sumRange_congr
    intro u _
    have h1 :
        sumRange (2 ^ m) (fun p1 =>
          sumRange (2 ^ m) (fun p2 =>
            srErr p1 (2 ^ m) (u ^^^ d1) * srErr p2 (2 ^ m) (u ^^^ d2))) =
        sumRange (2 ^ m) (fun p1 =>
          srErr p1 (2 ^ m) (u ^^^ d1) *
          sumRange (2 ^ m) (fun p2 => srErr p2 (2 ^ m) (u ^^^ d2))) := by
      apply sumRange_congr
      intro p1 _
      exact sumRange_mul_left (2 ^ m) _ _
    rw [h1, sumRange_mul_right]
  rw [hfactor]
  have heval :
      sumRange (2 ^ m) (fun u =>
        (sumRange (2 ^ m) (fun p1 => srErr p1 (2 ^ m) (u ^^^ d1))) *
        (sumRange (2 ^ m) (fun p2 => srErr p2 (2 ^ m) (u ^^^ d2)))) =
      sumRange (2 ^ m) (fun u =>
        ((2 * ((u ^^^ d1 : Nat) : Rat) - (((2 ^ m : Nat) : Rat) - 1)) *
         (2 * ((u ^^^ d2 : Nat) : Rat) - (((2 ^ m : Nat) : Rat) - 1))) / 4) := by
    apply sumRange_congr
    intro u hu
    have hu1 : u ^^^ d1 < 2 ^ m := Nat.xor_lt_two_pow hu hd1
    have hu2 : u ^^^ d2 < 2 ^ m := Nat.xor_lt_two_pow hu hd2
    have hm1 := mean_srErr_over_p (2 ^ m) (u ^^^ d1) hMpos hu1
    have hm2 := mean_srErr_over_p (2 ^ m) (u ^^^ d2) hMpos hu2
    unfold discreteMean at hm1 hm2
    have hs1 : sumRange (2 ^ m) (fun p1 => srErr p1 (2 ^ m) (u ^^^ d1)) =
        -(2 * ((u ^^^ d1 : Nat) : Rat) - (((2 ^ m : Nat) : Rat) - 1)) / 2 := by
      have := congrArg (fun t => t * ((2 ^ m : Nat) : Rat)) hm1
      grind
    have hs2 : sumRange (2 ^ m) (fun p2 => srErr p2 (2 ^ m) (u ^^^ d2)) =
        -(2 * ((u ^^^ d2 : Nat) : Rat) - (((2 ^ m : Nat) : Rat) - 1)) / 2 := by
      have := congrArg (fun t => t * ((2 ^ m : Nat) : Rat)) hm2
      grind
    rw [hs1, hs2]
    grind
  rw [heval, sumRange_div_const]
  grind

/-! ### 3. Dyadic Bitwise Induction for Centered XOR Covariance -/

theorem bitAt_xor (s a b : Nat) :
    bitAt s (a ^^^ b) = (bitAt s a + bitAt s b) % 2 := by
  unfold bitAt
  have h1 : (a ^^^ b).testBit s = (a.testBit s ^^ b.testBit s) := Nat.testBit_xor a b s
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      Nat.testBit_eq_decide_div_mod_eq] at h1
  have ha : (a / 2 ^ s) % 2 = 0 ∨ (a / 2 ^ s) % 2 = 1 := by omega
  have hb : (b / 2 ^ s) % 2 = 0 ∨ (b / 2 ^ s) % 2 = 1 := by omega
  have hab : ((a ^^^ b) / 2 ^ s) % 2 = 0 ∨ ((a ^^^ b) / 2 ^ s) % 2 = 1 := by omega
  rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1 <;> rcases hab with hab0 | hab1 <;>
    simp_all

theorem bitSign_xor (s a b : Nat) :
    bitSign s (a ^^^ b) = bitSign s a * bitSign s b := by
  unfold bitSign
  rw [bitAt_xor]
  have ha : bitAt s a = 0 ∨ bitAt s a = 1 := by unfold bitAt; omega
  have hb : bitAt s b = 0 ∨ bitAt s b = 1 := by unfold bitAt; omega
  rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1 <;> simp_all <;> grind

theorem bitAt_mod_two_pow {b s c : Nat} (hs : s < b) :
    bitAt s (c % 2 ^ b) = bitAt s c := by
  unfold bitAt
  have h1 : (c % 2 ^ b).testBit s = c.testBit s := by
    rw [Nat.testBit_mod_two_pow]
    simp [hs]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at h1
  have hmod1 : ((c % 2 ^ b) / 2 ^ s) % 2 = 0 ∨ ((c % 2 ^ b) / 2 ^ s) % 2 = 1 := by omega
  have hmod2 : (c / 2 ^ s) % 2 = 0 ∨ (c / 2 ^ s) % 2 = 1 := by omega
  rcases hmod1 with a | a <;> rcases hmod2 with b' | b' <;> simp_all

/-- Exact dyadic XOR covariance sum on `B = 2^b` strata:
    `∑_{q < 2^b} (2(q ^^^ c1) - (2^b - 1))(2(q ^^^ c2) - (2^b - 1)) = 2^b * ∑_{s < b} 4^s * (-1)^{bit_s(c1 ^^^ c2)}`. -/
theorem sumRange_xor_centered_prod (b c1 c2 : Nat)
    (hc1 : c1 < 2 ^ b) (hc2 : c2 < 2 ^ b) :
    sumRange (2 ^ b) (fun q =>
      (2 * ((q ^^^ c1 : Nat) : Rat) - (((2 ^ b : Nat) : Rat) - 1)) *
      (2 * ((q ^^^ c2 : Nat) : Rat) - (((2 ^ b : Nat) : Rat) - 1))) =
    ((2 ^ b : Nat) : Rat) *
      sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s (c1 ^^^ c2)) := by
  induction b generalizing c1 c2 with
  | zero =>
    have h1 : c1 = 0 := by omega
    have h2 : c2 = 0 := by omega
    subst h1; subst h2
    simp [sumRange]; grind
  | succ b ih =>
    have hpow2 : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
    let b1 := c1 / 2 ^ b
    let b2 := c2 / 2 ^ b
    let r1 := c1 % 2 ^ b
    let r2 := c2 % 2 ^ b
    have hr1 : r1 < 2 ^ b := Nat.mod_lt c1 (Nat.two_pow_pos b)
    have hr2 : r2 < 2 ^ b := Nat.mod_lt c2 (Nat.two_pow_pos b)
    have hb1_lt : b1 < 2 := by
      show c1 / 2 ^ b < 2
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)]
      omega
    have hb2_lt : b2 < 2 := by
      show c2 / 2 ^ b < 2
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)]
      omega
    have hb1 : b1 = 0 ∨ b1 = 1 := by
      match h : b1 with
      | 0 => exact Or.inl rfl
      | 1 => exact Or.inr rfl
      | _ + 2 => omega
    have hb2 : b2 = 0 ∨ b2 = 1 := by
      match h : b2 with
      | 0 => exact Or.inl rfl
      | 1 => exact Or.inr rfl
      | _ + 2 => omega
    have hc1_eq : 2 ^ b * b1 + r1 = c1 := Nat.div_add_mod c1 (2 ^ b)
    have hc2_eq : 2 ^ b * b2 + r2 = c2 := Nat.div_add_mod c2 (2 ^ b)
    have hbit1 : bitAt b c1 = b1 := by
      unfold bitAt; rcases hb1 with h | h <;> simp [b1, h]
    have hbit2 : bitAt b c2 = b2 := by
      unfold bitAt; rcases hb2 with h | h <;> simp [b2, h]
    -- Helper for the two halves of `q ∈ [0, 2^(b+1))`
    have hhalf0 : ∀ q, q < 2 ^ b →
        2 * ((q ^^^ c1 : Nat) : Rat) - (((2 ^ (b + 1) : Nat) : Rat) - 1) =
        (2 * ((q ^^^ r1 : Nat) : Rat) - (((2 ^ b : Nat) : Rat) - 1)) -
          bitSign b c1 * ((2 ^ b : Nat) : Rat) := by
      intro q hq
      unfold bitSign
      rw [hbit1, hpow2, rat_natCast_add]
      rcases hb1 with h0 | h1
      · have hc1' : c1 = r1 := by rw [← hc1_eq, h0]; simp
        rw [hc1', h0]; simp; grind
      · have hc1' : c1 = 2 ^ b + r1 := by rw [← hc1_eq, h1]; simp
        rw [hc1', h1, nat_xor_add_two_pow_right hq hr1, rat_natCast_add]
        simp; grind
    have hhalf1 : ∀ q, q < 2 ^ b →
        2 * (((2 ^ b + q) ^^^ c1 : Nat) : Rat) - (((2 ^ (b + 1) : Nat) : Rat) - 1) =
        (2 * ((q ^^^ r1 : Nat) : Rat) - (((2 ^ b : Nat) : Rat) - 1)) +
          bitSign b c1 * ((2 ^ b : Nat) : Rat) := by
      intro q hq
      unfold bitSign
      rw [hbit1, hpow2, rat_natCast_add]
      rcases hb1 with h0 | h1
      · have hc1' : c1 = r1 := by rw [← hc1_eq, h0]; simp
        rw [hc1', h0, nat_xor_add_two_pow_left hq hr1, rat_natCast_add]
        simp; grind
      · have hc1' : c1 = 2 ^ b + r1 := by rw [← hc1_eq, h1]; simp
        rw [hc1', h1, nat_xor_add_two_pow_both hq hr1]
        simp; grind
    have hhalf0_2 : ∀ q, q < 2 ^ b →
        2 * ((q ^^^ c2 : Nat) : Rat) - (((2 ^ (b + 1) : Nat) : Rat) - 1) =
        (2 * ((q ^^^ r2 : Nat) : Rat) - (((2 ^ b : Nat) : Rat) - 1)) -
          bitSign b c2 * ((2 ^ b : Nat) : Rat) := by
      intro q hq
      unfold bitSign
      rw [hbit2, hpow2, rat_natCast_add]
      rcases hb2 with h0 | h1
      · have hc2' : c2 = r2 := by rw [← hc2_eq, h0]; simp
        rw [hc2', h0]; simp; grind
      · have hc2' : c2 = 2 ^ b + r2 := by rw [← hc2_eq, h1]; simp
        rw [hc2', h1, nat_xor_add_two_pow_right hq hr2, rat_natCast_add]
        simp; grind
    have hhalf1_2 : ∀ q, q < 2 ^ b →
        2 * (((2 ^ b + q) ^^^ c2 : Nat) : Rat) - (((2 ^ (b + 1) : Nat) : Rat) - 1) =
        (2 * ((q ^^^ r2 : Nat) : Rat) - (((2 ^ b : Nat) : Rat) - 1)) +
          bitSign b c2 * ((2 ^ b : Nat) : Rat) := by
      intro q hq
      unfold bitSign
      rw [hbit2, hpow2, rat_natCast_add]
      rcases hb2 with h0 | h1
      · have hc2' : c2 = r2 := by rw [← hc2_eq, h0]; simp
        rw [hc2', h0, nat_xor_add_two_pow_left hq hr2, rat_natCast_add]
        simp; grind
      · have hc2' : c2 = 2 ^ b + r2 := by rw [← hc2_eq, h1]; simp
        rw [hc2', h1, nat_xor_add_two_pow_both hq hr2]
        simp; grind
    rw [hpow2, sumRange_append, ← sumRange_add]
    have hcancel :
        sumRange (2 ^ b) (fun q =>
          (2 * ((q ^^^ c1 : Nat) : Rat) - (((2 ^ b + 2 ^ b : Nat) : Rat) - 1)) *
            (2 * ((q ^^^ c2 : Nat) : Rat) - (((2 ^ b + 2 ^ b : Nat) : Rat) - 1)) +
          (2 * (((2 ^ b + q) ^^^ c1 : Nat) : Rat) - (((2 ^ b + 2 ^ b : Nat) : Rat) - 1)) *
            (2 * (((2 ^ b + q) ^^^ c2 : Nat) : Rat) - (((2 ^ b + 2 ^ b : Nat) : Rat) - 1))) =
        sumRange (2 ^ b) (fun q =>
          2 * ((2 * ((q ^^^ r1 : Nat) : Rat) - (((2 ^ b : Nat) : Rat) - 1)) *
               (2 * ((q ^^^ r2 : Nat) : Rat) - (((2 ^ b : Nat) : Rat) - 1))) +
          2 * (bitSign b c1 * bitSign b c2 * ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat))) := by
      apply sumRange_congr
      intro q hq
      have a0 := hhalf0 q hq
      have a1 := hhalf1 q hq
      have b0 := hhalf0_2 q hq
      have b1' := hhalf1_2 q hq
      rw [hpow2] at a0 a1 b0 b1'
      rw [a0, a1, b0, b1']
      grind
    rw [hcancel, sumRange_add, sumRange_mul_left, sumRange_const, ih r1 r2 hr1 hr2]
    -- Match lower bits `s < b` and top bit `s = b`
    have hlower :
        sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s (r1 ^^^ r2)) =
        sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s (c1 ^^^ c2)) := by
      apply sumRange_congr
      intro s hs
      rw [bitSign_xor, bitSign_xor]
      have h1 : bitSign s r1 = bitSign s c1 := by
        unfold bitSign; rw [bitAt_mod_two_pow hs]
      have h2 : bitSign s r2 = bitSign s c2 := by
        unfold bitSign; rw [bitAt_mod_two_pow hs]
      rw [h1, h2]
    rw [hlower]
    simp only [sumRange]
    rw [← bitSign_xor]
    have h4b : ((4 ^ b : Nat) : Rat) = ((2 ^ b : Nat) : Rat) * ((2 ^ b : Nat) : Rat) := by
      have hnat : 4 ^ b = 2 ^ b * 2 ^ b := by
        rw [← Nat.mul_pow]
      rw [hnat, rat_natCast_mul]
    rw [rat_natCast_add, h4b]
    grind

/-! ### 4. Combine `(q, r)` Split with Dyadic XOR Covariance -/

theorem testBit_mul_two_pow_add_lt {k x r i : Nat} (hi : i < k) :
    (x * 2 ^ k + r).testBit i = r.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hpow : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hi)]
  have heven : 2 ^ (k - i) % 2 = 0 := by
    have h1 : k - i = (k - i - 1) + 1 := by omega
    rw [h1, Nat.pow_succ]; omega
  have hmul_eq : x * 2 ^ k = 2 ^ i * (x * 2 ^ (k - i)) := by
    rw [hpow, Nat.mul_left_comm]
  rw [hmul_eq, Nat.mul_add_div (Nat.two_pow_pos i)]
  have hmod : (x * 2 ^ (k - i) + r / 2 ^ i) % 2 = (r / 2 ^ i) % 2 := by
    have hmul : (x * 2 ^ (k - i)) % 2 = 0 := by
      rw [Nat.mul_mod, heven]; simp
    omega
  rw [hmod]

theorem nat_xor_mul_two_pow_add {k q r c : Nat} (hr : r < 2 ^ k) :
    (q * 2 ^ k + r) ^^^ (c * 2 ^ k) = (q ^^^ c) * 2 ^ k + r := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  by_cases hi : i < k
  · have hdiv1 : (q * 2 ^ k + r).testBit i = r.testBit i :=
      testBit_mul_two_pow_add_lt hi
    have hdiv2 : (c * 2 ^ k).testBit i = false := by
      have h0 : (c * 2 ^ k + 0).testBit i = (0 : Nat).testBit i :=
        testBit_mul_two_pow_add_lt hi
      simpa using h0
    have hdiv3 : ((q ^^^ c) * 2 ^ k + r).testBit i = r.testBit i :=
      testBit_mul_two_pow_add_lt hi
    rw [hdiv1, hdiv2, hdiv3]
    simp
  · have hge : k ≤ i := by omega
    have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hge]
    have hdiv_shift : ∀ x, (x * 2 ^ k + r).testBit i = x.testBit (i - k) := by
      intro x
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hpow]
      rw [← Nat.div_div_eq_div_mul, Nat.mul_comm x (2 ^ k),
          Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt hr, Nat.add_zero]
    have hdiv_shift0 : (c * 2 ^ k).testBit i = c.testBit (i - k) := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hpow]
      rw [← Nat.div_div_eq_div_mul, Nat.mul_comm c (2 ^ k),
          Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)]
    rw [hdiv_shift q, hdiv_shift0, hdiv_shift (q ^^^ c), Nat.testBit_xor]

private theorem xor_cov_alg_identity (x y s : Rat) (hx : x ≠ 0) (hy : y ≠ 0) :
    (y * y * y * (x * s) + x * (y * (y * y - 1) / 3)) / (4 * (x * y) * (x * y) * (x * y)) =
    s / (4 * x * x) + (y * y - 1) / (12 * (x * y) * (x * y)) := by
  grind

theorem avgDiscreteSrCov_xor_shifted (m b c1 c2 : Nat) (hbm : b ≤ m)
    (hc1 : c1 < 2 ^ b) (hc2 : c2 < 2 ^ b) :
    avgDiscreteSrCov m (fun u => u ^^^ (c1 <<< (m - b))) (fun u => u ^^^ (c2 <<< (m - b))) =
    xorDiscreteAvgCovFormula m b c1 c2 := by
  have hpowM : 2 ^ m = 2 ^ b * 2 ^ (m - b) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hbm]
  have hd1 : c1 <<< (m - b) < 2 ^ m := by
    rw [Nat.shiftLeft_eq, hpowM]
    exact Nat.mul_lt_mul_of_pos_right hc1 (Nat.two_pow_pos (m - b))
  have hd2 : c2 <<< (m - b) < 2 ^ m := by
    rw [Nat.shiftLeft_eq, hpowM]
    exact Nat.mul_lt_mul_of_pos_right hc2 (Nat.two_pow_pos (m - b))
  rw [avgDiscreteSrCov_xor_eq_centered_sum m _ _ hd1 hd2]
  let B := 2 ^ b
  let R := 2 ^ (m - b)
  have hRpos : 0 < R := Nat.two_pow_pos (m - b)
  have hBne : (B : Rat) ≠ 0 := rat_pow2_ne_zero b
  have hRne : (R : Rat) ≠ 0 := rat_pow2_ne_zero (m - b)
  have hMne : ((2 ^ m : Nat) : Rat) ≠ 0 := rat_pow2_ne_zero m
  have hMrat : ((2 ^ m : Nat) : Rat) = (B : Rat) * (R : Rat) := by
    rw [hpowM, rat_natCast_mul]
  -- Rewrite the `2^m` sum using `sumRange_mul_split B R`
  have hsplit_sum :
      sumRange (2 ^ m) (fun u =>
        (2 * ((u ^^^ (c1 <<< (m - b)) : Nat) : Rat) - (((2 ^ m : Nat) : Rat) - 1)) *
        (2 * ((u ^^^ (c2 <<< (m - b)) : Nat) : Rat) - (((2 ^ m : Nat) : Rat) - 1))) =
      sumRange B (fun q => sumRange R (fun r =>
        ((R : Rat) * (2 * ((q ^^^ c1 : Nat) : Rat) - ((B : Rat) - 1)) +
          (2 * (r : Rat) - ((R : Rat) - 1))) *
        ((R : Rat) * (2 * ((q ^^^ c2 : Nat) : Rat) - ((B : Rat) - 1)) +
          (2 * (r : Rat) - ((R : Rat) - 1))))) := by
    rw [hpowM]
    have hcongr :
        sumRange (B * R) (fun u =>
          (2 * ((u ^^^ (c1 <<< (m - b)) : Nat) : Rat) - (((B * R : Nat) : Rat) - 1)) *
          (2 * ((u ^^^ (c2 <<< (m - b)) : Nat) : Rat) - (((B * R : Nat) : Rat) - 1))) =
        sumRange (B * R) (fun u =>
          ((R : Rat) * (2 * (((u / R) ^^^ c1 : Nat) : Rat) - ((B : Rat) - 1)) +
            (2 * ((u % R : Nat) : Rat) - ((R : Rat) - 1))) *
          ((R : Rat) * (2 * (((u / R) ^^^ c2 : Nat) : Rat) - ((B : Rat) - 1)) +
            (2 * ((u % R : Nat) : Rat) - ((R : Rat) - 1)))) := by
      apply sumRange_congr
      intro u _
      have huEq : u = (u / R) * R + u % R := by
        have := Nat.div_add_mod u R; rw [Nat.mul_comm] at this; exact this.symm
      have hrmod : u % R < R := Nat.mod_lt u hRpos
      have hx1 : u ^^^ (c1 <<< (m - b)) = ((u / R) ^^^ c1) * R + u % R := by
        rw [Nat.shiftLeft_eq]
        calc u ^^^ (c1 * R)
          _ = ((u / R) * R + u % R) ^^^ (c1 * R) := by rw [← huEq]
          _ = ((u / R) ^^^ c1) * R + u % R := nat_xor_mul_two_pow_add hrmod
      have hx2 : u ^^^ (c2 <<< (m - b)) = ((u / R) ^^^ c2) * R + u % R := by
        rw [Nat.shiftLeft_eq]
        calc u ^^^ (c2 * R)
          _ = ((u / R) * R + u % R) ^^^ (c2 * R) := by rw [← huEq]
          _ = ((u / R) ^^^ c2) * R + u % R := nat_xor_mul_two_pow_add hrmod
      rw [hx1, hx2, rat_natCast_add, rat_natCast_mul, rat_natCast_add, rat_natCast_mul,
          rat_natCast_mul]
      grind
    rw [hcongr]
    exact sumRange_mul_split B R hRpos (fun q r =>
      ((R : Rat) * (2 * ((q ^^^ c1 : Nat) : Rat) - ((B : Rat) - 1)) +
        (2 * (r : Rat) - ((R : Rat) - 1))) *
      ((R : Rat) * (2 * ((q ^^^ c2 : Nat) : Rat) - ((B : Rat) - 1)) +
        (2 * (r : Rat) - ((R : Rat) - 1))))
  rw [hsplit_sum]
  -- Evaluate the inner `R` sum
  have hmeanR0 : sumRange R (fun r => 2 * (r : Rat) - ((R : Rat) - 1)) = 0 := by
    rw [sumRange_sub, sumRange_mul_left, sumRange_nat_id, sumRange_const]
    grind
  have hinnerR :
      sumRange B (fun q => sumRange R (fun r =>
        ((R : Rat) * (2 * ((q ^^^ c1 : Nat) : Rat) - ((B : Rat) - 1)) +
          (2 * (r : Rat) - ((R : Rat) - 1))) *
        ((R : Rat) * (2 * ((q ^^^ c2 : Nat) : Rat) - ((B : Rat) - 1)) +
          (2 * (r : Rat) - ((R : Rat) - 1))))) =
      sumRange B (fun q =>
        (R : Rat) * (R : Rat) * (R : Rat) *
          ((2 * ((q ^^^ c1 : Nat) : Rat) - ((B : Rat) - 1)) *
           (2 * ((q ^^^ c2 : Nat) : Rat) - ((B : Rat) - 1))) +
        ((R : Rat) * ((R : Rat) * (R : Rat) - 1)) / 3) := by
    apply sumRange_congr
    intro q _
    let A1 := (R : Rat) * (2 * ((q ^^^ c1 : Nat) : Rat) - ((B : Rat) - 1))
    let A2 := (R : Rat) * (2 * ((q ^^^ c2 : Nat) : Rat) - ((B : Rat) - 1))
    have hexpand :
        sumRange R (fun r =>
          (A1 + (2 * (r : Rat) - ((R : Rat) - 1))) *
          (A2 + (2 * (r : Rat) - ((R : Rat) - 1)))) =
        sumRange R (fun r =>
          (A1 * A2 + (A1 + A2) * (2 * (r : Rat) - ((R : Rat) - 1))) +
          (2 * (r : Rat) - ((R : Rat) - 1)) * (2 * (r : Rat) - ((R : Rat) - 1))) := by
      apply sumRange_congr
      intro r _
      grind
    rw [hexpand, sumRange_add, sumRange_add, sumRange_const, sumRange_mul_left,
        hmeanR0, sumRange_centered_sq]
    grind
  rw [hinnerR, sumRange_add, sumRange_mul_left, sumRange_const,
      sumRange_xor_centered_prod b c1 c2 hc1 hc2]
  unfold xorDiscreteAvgCovFormula xorRankCov
  rw [hMrat]
  exact xor_cov_alg_identity ((2 ^ b : Nat) : Rat) ((2 ^ (m - b) : Nat) : Rat)
    (sumRange b (fun s => ((4 ^ s : Nat) : Rat) * bitSign s (c1 ^^^ c2))) hBne hRne

/-! ### 5. Headline Theorem 1 -/

theorem xor_vdc_sr_unbiased_and_covariance_exact (m b : Nat) (hbm : b ≤ m) :
    (∀ (i : Nat) (l r : Rat) (p : Nat), p ≤ 2 ^ m →
      discreteMean (2 ^ m) (fun u0 => srVal l r p (xorVdcLane m b i u0)) =
      l + (r - l) * ((p : Rat) / ((2 ^ m : Nat) : Rat))) ∧
    (∀ (i j : Nat),
      avgDiscreteSrCov m (xorVdcLane m b i) (xorVdcLane m b j) =
      xorDiscreteAvgCovFormula m b (bitrev b i) (bitrev b j)) := by
  constructor
  · intro i l r p hp
    exact xorVdcLane_unbiased m b i hbm l r p hp
  · intro i j
    unfold xorVdcLane xorVdcOffset
    exact avgDiscreteSrCov_xor_shifted m b (bitrev b i) (bitrev b j) hbm
      (bitrev_lt b i) (bitrev_lt b j)

end XorVdcFp4Dither
