/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SsmDecayCollapse.DecayStall

/-!
# Theorem 2: Exact One-ULP-Per-Step Sequential Decay Collapse Law

Proves the universal inductive law of bit-exact IEEE-754 RNE sequential multiplication
by `aMax p = 1 - 2^(-(p + 1))`:
1. Every normal float `floatVal p k m` with `0 < m < 2^p` decrements its mantissa by
   exact 1 ULP: `ieeeRne p (floatVal p k m * aMax p) = floatVal p k (m - 1)`.
2. Every binade boundary `floatVal p k 0 = 2^k` drops exactly 1 ULP into the lower
   binade: `ieeeRne p (floatVal p k 0 * aMax p) = floatVal p (k - 1) (2^p - 1)`.
3. By induction, `seqPow p (m * 2^p) = 2^(-m)` for all `p ≥ 1` and all `m : Nat`
   (effective half-life `2^p` tokens: `128` in BF16, and `2^(-32)` at `T = 4096`).
-/

namespace SsmDecayCollapse

theorem floatVal_mul_aMax_zero (p : Nat) (k : Int) :
    ieeeRne p (floatVal p k 0 * aMax p) = floatVal p (k - 1) (2 ^ p - 1) := by
  rw [floatVal_zero, aMax_eq_floatVal]
  have hmul : zpow2 k * floatVal p (-1) (2 ^ p - 1) = floatVal p (k - 1) (2 ^ p - 1) := by
    unfold floatVal
    rw [Rat.mul_comm (zpow2 k), Rat.mul_assoc, ← zpow2_add]
    have hexp : (-1 : Int) - (p : Int) + k = (k - 1) - (p : Int) := by omega
    rw [hexp]
  rw [hmul]
  have h1 : 1 ≤ 2 ^ p := nat_two_pow_pos p
  exact ieeeRne_floatVal p (k - 1) (2 ^ p - 1) (by omega)

theorem floatVal_mul_aMax_pos (p : Nat) (k : Int) (m : Nat) (hm0 : 0 < m) (hm : m < 2 ^ p) :
    ieeeRne p (floatVal p k m * aMax p) = floatVal p k (m - 1) := by
  have hprod_eq : floatVal p k m * aMax p =
      ((((2 ^ p + m : Nat) : Rat) - ((2 ^ p + m : Nat) : Rat) * zpow2 (-((p + 1 : Nat) : Int)))) *
        zpow2 (k - (p : Int)) := by
    unfold floatVal aMax
    rw [Rat.mul_comm (((2 ^ p + m : Nat) : Rat)) (zpow2 (k - (p : Int)))]
    rw [Rat.mul_assoc, Rat.mul_comm (zpow2 (k - (p : Int)))]
    have hdist : ((2 ^ p + m : Nat) : Rat) * (1 - zpow2 (-((p + 1 : Nat) : Int))) =
        ((2 ^ p + m : Nat) : Rat) - ((2 ^ p + m : Nat) : Rat) * zpow2 (-((p + 1 : Nat) : Int)) := by
      grind
    rw [hdist]
  have hdelta_lo : (1 / 2 : Rat) < ((2 ^ p + m : Nat) : Rat) * zpow2 (-((p + 1 : Nat) : Int)) := by
    have hgt : ((2 ^ p : Nat) : Rat) < ((2 ^ p + m : Nat) : Rat) :=
      Rat.natCast_lt_natCast.mpr (by omega)
    have hmul := rat_mul_lt_mul_of_pos_right hgt (zpow2_pos (-((p + 1 : Nat) : Int)))
    have hlhs : ((2 ^ p : Nat) : Rat) * zpow2 (-((p + 1 : Nat) : Int)) = 1 / 2 := by
      rw [← zpow2_ofNat p, ← zpow2_add]
      have hexp : (p : Int) + -((p + 1 : Nat) : Int) = -1 := by omega
      rw [hexp, zpow2_neg_one]
    rw [hlhs] at hmul
    exact hmul
  have hdelta_hi : ((2 ^ p + m : Nat) : Rat) * zpow2 (-((p + 1 : Nat) : Int)) < 1 := by
    have hlt : ((2 ^ p + m : Nat) : Rat) < ((2 ^ (p + 1) : Nat) : Rat) := by
      apply Rat.natCast_lt_natCast.mpr
      rw [Nat.pow_succ]
      omega
    have hmul := rat_mul_lt_mul_of_pos_right hlt (zpow2_pos (-((p + 1 : Nat) : Int)))
    rw [← zpow2_ofNat (p + 1), zpow2_mul_cancel] at hmul
    exact hmul
  have hpred : ((2 ^ p + (m - 1) : Nat) : Rat) = ((2 ^ p + m : Nat) : Rat) - 1 := by
    have heq : 2 ^ p + (m - 1) = (2 ^ p + m) - 1 := by omega
    rw [heq, rat_natCast_sub_one (by omega)]
  have hblo : zpow2 k ≤ floatVal p k m * aMax p := by
    rw [hprod_eq]
    have hsub : zpow2 k = ((2 ^ p : Nat) : Rat) * zpow2 (k - (p : Int)) := by
      have heq : k = (p : Int) + (k - (p : Int)) := by omega
      rw [heq, zpow2_add, zpow2_ofNat]
      have heq2 : (p : Int) + (k - (p : Int)) - (p : Int) = k - (p : Int) := by omega
      rw [heq2]
    rw [hsub]
    have hle1 : ((2 ^ p : Nat) : Rat) ≤ ((2 ^ p + (m - 1) : Nat) : Rat) :=
      Rat.natCast_le_natCast.mpr (by omega)
    have hle2 : ((2 ^ p : Nat) : Rat) ≤
        ((2 ^ p + m : Nat) : Rat) - ((2 ^ p + m : Nat) : Rat) * zpow2 (-((p + 1 : Nat) : Int)) := by
      grind
    exact rat_mul_le_mul_of_nonneg_right hle2 (Rat.le_of_lt (zpow2_pos _))
  have hbhi : floatVal p k m * aMax p < zpow2 (k + 1) := by
    have h1 := (floatVal_bounds p k m hm).2
    have hpos := floatVal_pos p k m
    have hamax := aMax_lt_one p
    have hmul := Rat.mul_lt_mul_of_pos_left hamax hpos
    rw [Rat.mul_one] at hmul
    grind
  rw [ieeeRne_eq_of_binade p hblo hbhi]
  rw [hprod_eq, Rat.mul_assoc]
  have hcancel : zpow2 (k - (p : Int)) * zpow2 ((p : Int) - k) = 1 := by
    rw [← zpow2_add]
    have h0 : k - (p : Int) + ((p : Int) - k) = 0 := by omega
    rw [h0, zpow2_zero]
  rw [hcancel, Rat.mul_one]
  have hci : (((2 ^ p + (m - 1) : Nat) : Int) : Rat) = ((2 ^ p + (m - 1) : Nat) : Rat) := rfl
  have hlo_r : (((2 ^ p + (m - 1) : Nat) : Int) : Rat) - 1 / 2 <
      ((2 ^ p + m : Nat) : Rat) - ((2 ^ p + m : Nat) : Rat) * zpow2 (-((p + 1 : Nat) : Int)) := by
    rw [hci, hpred]
    grind
  have hhi_r : ((2 ^ p + m : Nat) : Rat) - ((2 ^ p + m : Nat) : Rat) * zpow2 (-((p + 1 : Nat) : Int)) <
      (((2 ^ p + (m - 1) : Nat) : Int) : Rat) + 1 / 2 := by
    rw [hci, hpred]
    grind
  rw [rneInt_eq_of_bounds hlo_r hhi_r]
  unfold floatVal
  rw [hci]

theorem seqPow_binade_step (p : Nat) (k : Int) :
    ∀ x0 : Rat, x0 = floatVal p k 0 →
      ∀ r : Nat, r < 2 ^ p →
        Nat.rec x0 (fun _ acc => ieeeRne p (acc * aMax p)) r =
          if r = 0 then floatVal p k 0 else floatVal p (k - 1) (2 ^ p - r) := by
  intro x0 hx0 r hr
  induction r with
  | zero =>
    simp [hx0]
    rfl
  | succ j ih =>
    have hj : j < 2 ^ p := by omega
    have hprev := ih hj
    change ieeeRne p ((Nat.rec x0 (fun _ acc => ieeeRne p (acc * aMax p)) j) * aMax p) =
      if j + 1 = 0 then floatVal p k 0 else floatVal p (k - 1) (2 ^ p - (j + 1))
    rw [hprev]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
    cases j with
    | zero =>
      simp only [↓reduceIte, Nat.zero_add]
      exact floatVal_mul_aMax_zero p k
    | succ j' =>
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
      have hpos : 0 < 2 ^ p - (j' + 1) := by omega
      have hlt : 2 ^ p - (j' + 1) < 2 ^ p := by omega
      have hstep := floatVal_mul_aMax_pos p (k - 1) (2 ^ p - (j' + 1)) hpos hlt
      have hsub : 2 ^ p - (j' + 1) - 1 = 2 ^ p - (j' + 1 + 1) := by omega
      rw [hsub] at hstep
      exact hstep

theorem seqPow_eq_rec (p n : Nat) :
    seqPow p n = Nat.rec (1 : Rat) (fun _ acc => ieeeRne p (acc * aMax p)) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [seqPow, ih]

theorem seqPow_add_step (p a b : Nat) :
    seqPow p (a + b) = Nat.rec (seqPow p a) (fun _ acc => ieeeRne p (acc * aMax p)) b := by
  induction b with
  | zero => rfl
  | succ k ih =>
    rw [Nat.add_succ]
    change ieeeRne p (seqPow p (a + k) * aMax p) =
      ieeeRne p ((Nat.rec (seqPow p a) (fun _ acc => ieeeRne p (acc * aMax p)) k) * aMax p)
    rw [ih]

theorem seqPow_add_pow2 (p : Nat) (k : Int) (a : Nat) (ha : seqPow p a = zpow2 k) :
    seqPow p (a + 2 ^ p) = zpow2 (k - 1) := by
  have h1 : 1 ≤ 2 ^ p := nat_two_pow_pos p
  have hsplit : a + 2 ^ p = (a + (2 ^ p - 1)) + 1 := by omega
  rw [hsplit]
  change ieeeRne p (seqPow p (a + (2 ^ p - 1)) * aMax p) = zpow2 (k - 1)
  rw [seqPow_add_step]
  have hrec := seqPow_binade_step p k (seqPow p a) (by rw [ha, floatVal_zero]) (2 ^ p - 1) (by omega)
  rw [hrec]
  by_cases h0 : 2 ^ p - 1 = 0
  · -- Only happens if p = 0; still holds!
    simp only [h0, ↓reduceIte]
    rw [floatVal_mul_aMax_zero, h0, floatVal_zero]
  · simp only [h0, ↓reduceIte]
    have hsub1 : 2 ^ p - (2 ^ p - 1) = 1 := by omega
    rw [hsub1]
    have hlt : 1 < 2 ^ p := by omega
    have hstep := floatVal_mul_aMax_pos p (k - 1) 1 (by decide) hlt
    rw [hstep]
    simp only [Nat.sub_self, floatVal_zero]

theorem seqPow_mul_pow2 (p m : Nat) :
    seqPow p (m * 2 ^ p) = zpow2 (-(m : Int)) := by
  induction m with
  | zero =>
    simp [seqPow, zpow2_zero]
  | succ k ih =>
    have hmul : (k + 1) * 2 ^ p = k * 2 ^ p + 2 ^ p := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hmul]
    have hstep := seqPow_add_pow2 p (-(k : Int)) (k * 2 ^ p) ih
    have hexp : -(k : Int) - 1 = -((k + 1 : Nat) : Int) := by omega
    rw [hexp] at hstep
    exact hstep

/-- Headline Theorem 2 (`one_ulp_per_step_sequential_collapse`). -/
theorem one_ulp_per_step_sequential_collapse :
    (∀ (p : Nat) (k : Int) (m : Nat), 0 < m → m < 2 ^ p →
      ieeeRne p (floatVal p k m * aMax p) = floatVal p k (m - 1)) ∧
    (∀ (p : Nat) (k : Int),
      ieeeRne p (floatVal p k 0 * aMax p) = floatVal p (k - 1) (2 ^ p - 1)) ∧
    (∀ (p m : Nat), 1 ≤ p → seqPow p (m * 2 ^ p) = zpow2 (-(m : Int))) ∧
    (∀ p : Nat, 1 ≤ p → seqPow p (2 ^ p) = 1 / 2) ∧
    (seqPow 7 128 = 1 / 2 ∧ seqPow 7 4096 = zpow2 (-32)) := by
  refine ⟨fun p k m hm0 hm => floatVal_mul_aMax_pos p k m hm0 hm,
    fun p k => floatVal_mul_aMax_zero p k,
    fun p m _ => seqPow_mul_pow2 p m,
    fun p _ => ?_, ?_⟩
  · have h := seqPow_mul_pow2 p 1
    simp only [Nat.one_mul] at h
    rw [h, show -(1 : Nat) = (-1 : Int) from rfl, zpow2_neg_one]
  · constructor
    · have h := seqPow_mul_pow2 7 1
      change seqPow 7 (1 * 2 ^ 7) = 1 / 2
      rw [h, show -(1 : Nat) = (-1 : Int) from rfl, zpow2_neg_one]
    · have h := seqPow_mul_pow2 7 32
      exact h

end SsmDecayCollapse
