/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VlmTomeCumulant.RatOrder

/-!
# Pillar 3: ViT Front-Loaded Dominance over `Constant-r` & Late-Loaded `1.5×` FLOP Ceiling

Proves Theorems 5 (`vit_front_loaded_dominates_constant_r_schedule`) and 6
(`late_loaded_merging_flop_infeasibility_ceiling`) purely over `Init`.
-/

namespace VlmTomeCumulant

/-! ### Prefix-Sum and Shift-Schedule Helpers -/

theorem finSum_single {n : Nat} (j : Fin n) (c : Rat) :
    finSum (fun i : Fin n => if i = j then c else 0) = c := by
  unfold finSum
  induction n with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    simp only [finSumAux]
    by_cases hlast : j.val = k
    · have hj : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hlast
      subst hj
      have hzero : finSumAux k (fun i : Fin k =>
          if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (k + 1)) = ⟨k, Nat.lt_succ_self k⟩ then c else 0) = 0 := by
        rw [finSumAux_congr (g := fun _ => (0 : Rat))]
        · exact finSum_zero k
        · intro i
          have hne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (k + 1)) ≠ ⟨k, Nat.lt_succ_self k⟩ := by
            intro heq
            have : i.val = k := congrArg (fun x : Fin (k + 1) => x.val) heq
            omega
          simp [hne]
      rw [hzero]; simp; grind
    · have hlt : j.val < k := by omega
      have hne : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ≠ j := by
        intro heq
        have : k = j.val := congrArg (fun x : Fin (k + 1) => x.val) heq
        omega
      simp only [hne, ite_false, Rat.add_zero]
      have hcongr : finSumAux k (fun i : Fin k =>
          if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (k + 1)) = j then c else 0) =
          finSumAux k (fun i : Fin k => if i = ⟨j.val, hlt⟩ then c else 0) := by
        apply finSumAux_congr; intro i
        have hiff : ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (k + 1)) = j) ↔ (i = ⟨j.val, hlt⟩) := by
          constructor
          · intro h; exact Fin.ext (congrArg (fun x : Fin (k + 1) => x.val) h)
          · intro h; exact Fin.ext (congrArg (fun x : Fin k => x.val) h)
        by_cases hi : i = ⟨j.val, hlt⟩
        · simp [hi]
        · have hi' : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (k + 1)) ≠ j := fun h => hi (hiff.mp h)
          simp only [hi, hi', ite_false]
      rw [hcongr]
      exact ih ⟨j.val, hlt⟩

theorem prefixSum_le_finSumNat {L : Nat} (r : Fin L → Nat) (k : Nat) :
    prefixSum r k ≤ finSumNat r := by
  unfold prefixSum
  apply finSumNat_le_finSumNat
  intro l
  split <;> omega

theorem prefixSum_last {L : Nat} (_hL : 1 ≤ L) (r : Fin L → Nat) :
    prefixSum r (L - 1) = finSumNat r := by
  unfold prefixSum
  apply finSumNat_congr
  intro l
  have hle : l.val ≤ L - 1 := by have := l.isLt; omega
  simp [hle]

theorem finSumNat_shiftSchedule {L : Nat} (r : Fin L → Nat) (i j : Fin L) (Δ : Nat)
    (hij : i ≠ j) (hΔ : Δ ≤ r j) :
    finSumNat (shiftSchedule r i j Δ) = finSumNat r := by
  have h1 : finSumNat (shiftSchedule r i j Δ) + Δ = finSumNat r + Δ := by
    calc finSumNat (shiftSchedule r i j Δ) + Δ
        = finSumNat (shiftSchedule r i j Δ) + finSumNat (fun l : Fin L => if l = j then Δ else 0) := by
            rw [finSumNat_single j Δ]
      _ = finSumNat (fun l : Fin L => shiftSchedule r i j Δ l + (if l = j then Δ else 0)) :=
            (finSumNat_add _ _).symm
      _ = finSumNat (fun l : Fin L => r l + (if l = i then Δ else 0)) := by
            apply finSumNat_congr; intro l
            unfold shiftSchedule
            by_cases hli : l = i
            · subst hli; simp [hij]
            · by_cases hlj : l = j
              · subst hlj; simp only [hli, ite_false, ite_true]; omega
              · simp [hli, hlj]
      _ = finSumNat r + finSumNat (fun l : Fin L => if l = i then Δ else 0) :=
            finSumNat_add _ _
      _ = finSumNat r + Δ := by rw [finSumNat_single i Δ]
  omega

theorem prefixSum_shiftSchedule {L : Nat} (r : Fin L → Nat) (i j : Fin L) (Δ : Nat)
    (hij : i.val < j.val) (hΔ : Δ ≤ r j) (k : Nat) :
    prefixSum (shiftSchedule r i j Δ) k =
      if i.val ≤ k ∧ k < j.val then prefixSum r k + Δ else prefixSum r k := by
  have hne : i ≠ j := fun h => by have := congrArg Fin.val h; omega
  unfold prefixSum
  by_cases hmid : i.val ≤ k ∧ k < j.val
  · simp only [hmid, and_self, ite_true]
    calc finSumNat (fun l : Fin L => if l.val ≤ k then shiftSchedule r i j Δ l else 0)
        = finSumNat (fun l : Fin L => (if l.val ≤ k then r l else 0) + (if l = i then Δ else 0)) := by
            apply finSumNat_congr; intro l
            unfold shiftSchedule
            by_cases hli : l = i
            · subst hli; simp [hmid.1]
            · by_cases hlj : l = j
              · subst hlj
                have hnot : ¬ (l.val ≤ k) := by omega
                simp [hli, hnot]
              · simp [hli, hlj]
      _ = finSumNat (fun l : Fin L => if l.val ≤ k then r l else 0) +
          finSumNat (fun l : Fin L => if l = i then Δ else 0) :=
            finSumNat_add _ _
      _ = finSumNat (fun l : Fin L => if l.val ≤ k then r l else 0) + Δ := by
            rw [finSumNat_single i Δ]
  · simp only [hmid, ite_false]
    by_cases hlt : k < i.val
    · apply finSumNat_congr; intro l
      unfold shiftSchedule
      by_cases hlk : l.val ≤ k
      · have hli : l ≠ i := fun h => by have := congrArg Fin.val h; omega
        have hlj : l ≠ j := fun h => by have := congrArg Fin.val h; omega
        simp [hlk, hli, hlj]
      · simp [hlk]
    · have hjle : j.val ≤ k := by omega
      have hile : i.val ≤ k := by omega
      have hEq :
          finSumNat (fun l : Fin L => if l.val ≤ k then shiftSchedule r i j Δ l else 0) + Δ =
          finSumNat (fun l : Fin L => if l.val ≤ k then r l else 0) + Δ := by
        calc finSumNat (fun l : Fin L => if l.val ≤ k then shiftSchedule r i j Δ l else 0) + Δ
            = finSumNat (fun l : Fin L => if l.val ≤ k then shiftSchedule r i j Δ l else 0) +
              finSumNat (fun l : Fin L => if l = j then Δ else 0) := by
                rw [finSumNat_single j Δ]
          _ = finSumNat (fun l : Fin L =>
                (if l.val ≤ k then shiftSchedule r i j Δ l else 0) + (if l = j then Δ else 0)) :=
                (finSumNat_add _ _).symm
          _ = finSumNat (fun l : Fin L =>
                (if l.val ≤ k then r l else 0) + (if l = i then Δ else 0)) := by
                apply finSumNat_congr; intro l
                unfold shiftSchedule
                by_cases hli : l = i
                · subst hli; simp [hile, hne]
                · by_cases hlj : l = j
                  · subst hlj
                    simp only [hjle, hli, ite_false, ite_true]
                    omega
                  · simp [hli, hlj]
          _ = finSumNat (fun l : Fin L => if l.val ≤ k then r l else 0) +
              finSumNat (fun l : Fin L => if l = i then Δ else 0) :=
                finSumNat_add _ _
          _ = finSumNat (fun l : Fin L => if l.val ≤ k then r l else 0) + Δ := by
                rw [finSumNat_single i Δ]
      omega

theorem scheduleDrift_shiftSchedule {L : Nat} (w : Fin L → Rat) (r : Fin L → Nat)
    (i j : Fin L) (Δ : Nat) (hij : i ≠ j) (hΔ : Δ ≤ r j) :
    scheduleDrift w (shiftSchedule r i j Δ) = scheduleDrift w r - (Δ : Rat) * (w j - w i) := by
  have hdiff : scheduleDrift w (shiftSchedule r i j Δ) - scheduleDrift w r =
      finSum (fun l : Fin L => if l = i then w i * (Δ : Rat) else 0) -
      finSum (fun l : Fin L => if l = j then w j * (Δ : Rat) else 0) := by
    unfold scheduleDrift
    rw [← finSum_sub, ← finSum_sub]
    apply finSum_congr
    intro l
    unfold shiftSchedule
    by_cases hli : l = i
    · subst hli
      simp only [ite_true, hij, ite_false]
      rw [rat_natCast_add]; grind
    · by_cases hlj : l = j
      · subst hlj
        simp only [hli, ite_false, ite_true]
        have hadd : r l - Δ + Δ = r l := by omega
        have hcast : ((r l - Δ : Nat) : Rat) + (Δ : Rat) = (r l : Rat) := by
          rw [← rat_natCast_add, hadd]
        grind
      · simp [hli, hlj]; grind
  rw [finSum_single i (w i * (Δ : Rat)), finSum_single j (w j * (Δ : Rat))] at hdiff
  grind

/-! ### Exact Discrete Summation by Parts (Abel Summation) -/

theorem prefixSum_succ_step {L : Nat} (r : Fin (L + 1) → Nat) (k : Nat) (hk : k < L) :
    prefixSum r k = prefixSum (fun l : Fin L => r ⟨l.val, Nat.lt_succ_of_lt l.isLt⟩) k := by
  unfold prefixSum finSumNat
  simp only [finSumNatAux]
  have hnot : ¬ (L ≤ k) := by omega
  simp [hnot]

theorem abel_summation_drift : ∀ (L : Nat) (hL : 1 ≤ L) (w : Fin L → Rat) (r : Fin L → Nat),
    scheduleDrift w r =
      w ⟨L - 1, by omega⟩ * (finSumNat r : Rat) -
      finSum (fun k : Fin (L - 1) =>
        (w ⟨k.val + 1, by omega⟩ - w ⟨k.val, by omega⟩) * (prefixSum r k.val : Rat))
  | 0, hL, _, _ => by omega
  | 1, _, w, r => by
    unfold scheduleDrift finSum finSumNat
    simp [finSumAux, finSumNatAux]; grind
  | L + 2, _, w, r => by
    let w' : Fin (L + 1) → Rat := fun l => w ⟨l.val, Nat.lt_succ_of_lt l.isLt⟩
    let r' : Fin (L + 1) → Nat := fun l => r ⟨l.val, Nat.lt_succ_of_lt l.isLt⟩
    have hih := abel_summation_drift (L + 1) (by omega) w' r'
    have hsplitDrift : scheduleDrift w r = scheduleDrift w' r' + w ⟨L + 1, Nat.lt_succ_self _⟩ * (r ⟨L + 1, Nat.lt_succ_self _⟩ : Rat) := by
      unfold scheduleDrift finSum
      simp only [finSumAux]
      rfl
    have hsplitSum : finSumNat r = finSumNat r' + r ⟨L + 1, Nat.lt_succ_self _⟩ := by
      unfold finSumNat
      simp only [finSumNatAux]
      rfl
    have hsplitAbel :
        finSum (fun k : Fin (L + 1) =>
          (w ⟨k.val + 1, by omega⟩ - w ⟨k.val, by omega⟩) * (prefixSum r k.val : Rat)) =
        finSum (fun k : Fin L =>
          (w' ⟨k.val + 1, by omega⟩ - w' ⟨k.val, by omega⟩) * (prefixSum r' k.val : Rat)) +
        (w ⟨L + 1, by omega⟩ - w ⟨L, by omega⟩) * (prefixSum r L : Rat) := by
      unfold finSum
      simp only [finSumAux]
      congr 1
      apply finSumAux_congr
      intro k
      have hk : k.val < L + 1 := by omega
      rw [prefixSum_succ_step r k.val hk]
    have hprefL : prefixSum r L = finSumNat r' := by
      rw [prefixSum_succ_step r L (by omega)]
      exact prefixSum_last (by omega) r'
    have hcastSum : ((finSumNat r : Nat) : Rat) = (finSumNat r' : Rat) + (r ⟨L + 1, Nat.lt_succ_self _⟩ : Rat) := by
      rw [hsplitSum, rat_natCast_add]
    have hgoal : scheduleDrift w r =
        w ⟨L + 1, by omega⟩ * (finSumNat r : Rat) -
        finSum (fun k : Fin (L + 1) =>
          (w ⟨k.val + 1, by omega⟩ - w ⟨k.val, by omega⟩) * (prefixSum r k.val : Rat)) := by
      simp only [Nat.add_sub_cancel] at hih
      rw [hsplitDrift, hih, hsplitAbel, hprefL, hcastSum]
      have halg : ∀ (a b c d S : Rat), (a * b - S) + c * d = c * (b + d) - (S + (c - a) * b) := by
        intro a b c d S; grind
      exact halg (w ⟨L, by omega⟩) (finSumNat r' : Rat) (w ⟨L + 1, by omega⟩)
        (r ⟨L + 1, Nat.lt_succ_self _⟩ : Rat)
        (finSum (fun k : Fin L => (w' ⟨k.val + 1, by omega⟩ - w' ⟨k.val, by omega⟩) * (prefixSum r' k.val : Rat)))
    exact hgoal

/-! ### Theorem 5: Front-Loaded Schedules Strictly Dominate `Constant-r` -/

theorem nat_sq_lt_sq_of_lt {a b : Nat} (h : a < b) : a * a < b * b :=
  Nat.mul_lt_mul_of_lt_of_lt h h

theorem nat_sq_le_sq_of_le {a b : Nat} (h : a ≤ b) : a * a ≤ b * b :=
  Nat.mul_le_mul h h

/-- Headline Theorem 5 (`vit_front_loaded_dominates_constant_r_schedule`). -/
theorem vit_front_loaded_dominates_constant_r_schedule :
    (∀ (L N0 c : Nat) (r : Fin L → Nat) (w : Fin L → Rat) (i j : Fin L) (Δ : Nat),
      i.val < j.val → 0 < Δ → Δ ≤ r j → finSumNat r ≤ N0 →
      let r' := shiftSchedule r i j Δ
      finSumNat r' = finSumNat r ∧
      attnFlops N0 r' < attnFlops N0 r ∧
      vitFlops N0 c r' < vitFlops N0 c r ∧
      scheduleDrift w r' = scheduleDrift w r - (Δ : Rat) * (w j - w i) ∧
      (w i < w j → scheduleDrift w r' < scheduleDrift w r)) ∧
    (∀ (L N0 c R : Nat) (rFront : Fin L → Nat) (w : Fin L → Rat),
      2 ≤ L → L * R ≤ N0 →
      let rConst : Fin L → Nat := fun _ => R
      finSumNat rFront = finSumNat rConst →
      (∀ k : Fin (L - 1), prefixSum rConst k.val ≤ prefixSum rFront k.val) →
      (∃ k : Fin (L - 1), prefixSum rConst k.val < prefixSum rFront k.val) →
      attnFlops N0 rFront < attnFlops N0 rConst ∧
      vitFlops N0 c rFront < vitFlops N0 c rConst ∧
      ((∀ k : Fin (L - 1), w ⟨k.val, by omega⟩ < w ⟨k.val + 1, by omega⟩) →
        scheduleDrift w rFront < scheduleDrift w rConst)) ∧
    (let rConst24 : Fin 24 → Nat := fun _ => 32
     let rFront24 : Fin 24 → Nat := fun l => if l.val < 12 then 64 else 0
     finSumNat rFront24 = finSumNat rConst24 ∧
     attnFlops 1024 rFront24 < attnFlops 1024 rConst24 ∧
     vitFlops 1024 6144 rFront24 < vitFlops 1024 6144 rConst24) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L N0 c r w i j Δ hij hΔpos hΔle htot r'
    have hne : i ≠ j := fun h => by have := congrArg Fin.val h; omega
    have hsum : finSumNat r' = finSumNat r := finSumNat_shiftSchedule r i j Δ hne hΔle
    have hrem_le : ∀ l : Fin L, remTokens N0 r' l ≤ remTokens N0 r l := by
      intro l
      unfold remTokens
      rw [prefixSum_shiftSchedule r i j Δ hij hΔle l.val]
      split <;> omega
    have hrem_lt_i : remTokens N0 r' i < remTokens N0 r i := by
      unfold remTokens
      rw [prefixSum_shiftSchedule r i j Δ hij hΔle i.val]
      have hmid : i.val ≤ i.val ∧ i.val < j.val := ⟨Nat.le_refl _, hij⟩
      simp only [hmid, and_self, ite_true]
      have hleTot : prefixSum r i.val + Δ ≤ N0 := by
        have h1 : prefixSum r i.val + r j ≤ finSumNat r := by
          have hadd : prefixSum r i.val + finSumNat (fun l : Fin L => if l = j then r j else 0) ≤ finSumNat r := by
            unfold prefixSum
            rw [← finSumNat_add]
            apply finSumNat_le_finSumNat
            intro l
            by_cases hlj : l = j
            · subst hlj
              have hnot : ¬ (l.val ≤ i.val) := by omega
              simp [hnot]
            · simp [hlj]; split <;> omega
          rw [finSumNat_single j (r j)] at hadd
          exact hadd
        omega
      omega
    have hattn : attnFlops N0 r' < attnFlops N0 r := by
      unfold attnFlops
      apply finSumNat_lt_finSumNat_of_le_of_exists_lt
      · intro l; exact nat_sq_le_sq_of_le (hrem_le l)
      · exact ⟨i, nat_sq_lt_sq_of_lt hrem_lt_i⟩
    have hvit : vitFlops N0 c r' < vitFlops N0 c r := by
      unfold vitFlops
      apply finSumNat_lt_finSumNat_of_le_of_exists_lt
      · intro l
        exact Nat.add_le_add (nat_sq_le_sq_of_le (hrem_le l)) (Nat.mul_le_mul_left c (hrem_le l))
      · refine ⟨i, ?_⟩
        have hsq := nat_sq_lt_sq_of_lt hrem_lt_i
        have hlin := Nat.mul_le_mul_left c (Nat.le_of_lt hrem_lt_i)
        omega
    have hdrift := scheduleDrift_shiftSchedule w r i j Δ hne hΔle
    have hdrift_lt : w i < w j → scheduleDrift w r' < scheduleDrift w r := by
      intro hwij
      rw [hdrift]
      have hΔr : (0 : Rat) < (Δ : Rat) := rat_natCast_pos hΔpos
      have hdiff : (0 : Rat) < w j - w i := rat_sub_pos hwij
      have hprod : (0 : Rat) < (Δ : Rat) * (w j - w i) := rat_mul_pos hΔr hdiff
      apply rat_lt_of_sub_pos
      have : scheduleDrift w r - (scheduleDrift w r - (Δ : Rat) * (w j - w i)) =
          (Δ : Rat) * (w j - w i) := by grind
      rw [this]; exact hprod
    exact ⟨hsum, hattn, hvit, hdrift, hdrift_lt⟩
  · intro L N0 c R rFront w hL hLR rConst htot hpref_le ⟨k0, hk0⟩
    have hconstTot : finSumNat rConst = L * R := finSumNat_const L R
    have hfrontTot_le : finSumNat rFront ≤ N0 := by omega
    have hpref_all_le : ∀ l : Fin L, prefixSum rConst l.val ≤ prefixSum rFront l.val := by
      intro l
      by_cases hlast : l.val = L - 1
      · rw [hlast, prefixSum_last (by omega) rConst, prefixSum_last (by omega) rFront, htot]
        exact Nat.le_refl _
      · have hlt : l.val < L - 1 := by have := l.isLt; omega
        exact hpref_le ⟨l.val, hlt⟩
    have hrem_le : ∀ l : Fin L, remTokens N0 rFront l ≤ remTokens N0 rConst l := by
      intro l
      unfold remTokens
      have := hpref_all_le l
      omega
    let l0 : Fin L := ⟨k0.val, by omega⟩
    have hrem_lt : remTokens N0 rFront l0 < remTokens N0 rConst l0 := by
      unfold remTokens
      have hleN0 : prefixSum rFront k0.val ≤ N0 :=
        Nat.le_trans (prefixSum_le_finSumNat rFront k0.val) hfrontTot_le
      change N0 - prefixSum rFront k0.val < N0 - prefixSum rConst k0.val
      omega
    have hattn : attnFlops N0 rFront < attnFlops N0 rConst := by
      unfold attnFlops
      apply finSumNat_lt_finSumNat_of_le_of_exists_lt
      · intro l; exact nat_sq_le_sq_of_le (hrem_le l)
      · exact ⟨l0, nat_sq_lt_sq_of_lt hrem_lt⟩
    have hvit : vitFlops N0 c rFront < vitFlops N0 c rConst := by
      unfold vitFlops
      apply finSumNat_lt_finSumNat_of_le_of_exists_lt
      · intro l
        exact Nat.add_le_add (nat_sq_le_sq_of_le (hrem_le l)) (Nat.mul_le_mul_left c (hrem_le l))
      · refine ⟨l0, ?_⟩
        have hsq := nat_sq_lt_sq_of_lt hrem_lt
        have hlin := Nat.mul_le_mul_left c (Nat.le_of_lt hrem_lt)
        omega
    have hdrift : (∀ k : Fin (L - 1), w ⟨k.val, by omega⟩ < w ⟨k.val + 1, by omega⟩) →
        scheduleDrift w rFront < scheduleDrift w rConst := by
      intro hw_inc
      rw [abel_summation_drift L (by omega) w rFront, abel_summation_drift L (by omega) w rConst, htot]
      apply rat_lt_of_sub_pos
      have hsub :
          (w ⟨L - 1, by omega⟩ * (finSumNat rConst : Rat) -
            finSum (fun k : Fin (L - 1) =>
              (w ⟨k.val + 1, by omega⟩ - w ⟨k.val, by omega⟩) * (prefixSum rConst k.val : Rat))) -
          (w ⟨L - 1, by omega⟩ * (finSumNat rConst : Rat) -
            finSum (fun k : Fin (L - 1) =>
              (w ⟨k.val + 1, by omega⟩ - w ⟨k.val, by omega⟩) * (prefixSum rFront k.val : Rat))) =
          finSum (fun k : Fin (L - 1) =>
            (w ⟨k.val + 1, by omega⟩ - w ⟨k.val, by omega⟩) * (prefixSum rFront k.val : Rat)) -
          finSum (fun k : Fin (L - 1) =>
            (w ⟨k.val + 1, by omega⟩ - w ⟨k.val, by omega⟩) * (prefixSum rConst k.val : Rat)) := by
        grind
      rw [hsub]
      apply rat_sub_pos
      apply finSum_lt_finSum_of_le_of_exists_lt
      · intro k
        have hdw : (0 : Rat) ≤ w ⟨k.val + 1, by omega⟩ - w ⟨k.val, by omega⟩ :=
          rat_sub_nonneg (Rat.le_of_lt (hw_inc k))
        exact rat_mul_le_mul_of_nonneg_left (rat_natCast_le (hpref_le k)) hdw
      · refine ⟨k0, ?_⟩
        have hdw : (0 : Rat) < w ⟨k0.val + 1, by omega⟩ - w ⟨k0.val, by omega⟩ :=
          rat_sub_pos (hw_inc k0)
        exact rat_mul_lt_mul_of_pos_left (rat_natCast_lt hk0) hdw
    exact ⟨hattn, hvit, hdrift⟩
  · decide

/-! ### Theorem 6: Late-Loaded Merging `1.5×` (`3/2`) FLOP Infeasibility Ceiling -/

theorem late_loaded_remTokens_eq_N0 {L k N0 : Nat} (r : Fin L → Nat)
    (hzero : ∀ l : Fin L, l.val < k → r l = 0) (l : Fin L) (hl : l.val < k) :
    remTokens N0 r l = N0 := by
  unfold remTokens prefixSum
  have hp0 : finSumNat (fun j : Fin L => if j.val ≤ l.val then r j else 0) = 0 := by
    rw [finSumNat_congr (g := fun _ => 0)]
    · exact finSumNat_zero L
    · intro j
      by_cases hjl : j.val ≤ l.val
      · have hjk : j.val < k := by omega
        simp [hjl, hzero j hjk]
      · simp [hjl]
  rw [hp0]; omega

theorem finSumNat_ge_prefix_const {L k c : Nat} (hk : k ≤ L) (f : Fin L → Nat)
    (hconst : ∀ l : Fin L, l.val < k → f l = c) :
    k * c ≤ finSumNat f ∧ ((∃ l : Fin L, k ≤ l.val ∧ 1 ≤ f l) → k * c < finSumNat f) := by
  have hL : L = k + (L - k) := by omega
  have hcast : ∀ (n m : Nat) (h : n = m) (g : Fin n → Nat),
      finSumNat g = finSumNat (fun i : Fin m => g ⟨i.val, h ▸ i.isLt⟩) := by
    intro n m h g; subst h; rfl
  have hsplit : finSumNat f =
      k * c + finSumNat (fun j : Fin (L - k) => f ⟨k + j.val, by omega⟩) := by
    rw [hcast L (k + (L - k)) hL f, finSumNat_split]
    congr 1
    rw [finSumNat_congr (g := fun _ : Fin k => c)]
    · exact finSumNat_const k c
    · intro i; exact hconst ⟨i.val, by omega⟩ i.isLt
  constructor
  · rw [hsplit]; omega
  · intro ⟨l0, hl0k, hl0pos⟩
    rw [hsplit]
    have htail_pos : 0 < finSumNat (fun j : Fin (L - k) => f ⟨k + j.val, by omega⟩) := by
      have hge := finSumNat_lt_finSumNat_of_le_of_exists_lt
        (f := fun _ : Fin (L - k) => 0)
        (g := fun j : Fin (L - k) => f ⟨k + j.val, by omega⟩)
        (fun _ => Nat.zero_le _)
        ⟨⟨l0.val - k, by omega⟩, by
          have heq : (⟨k + (l0.val - k), by omega⟩ : Fin L) = l0 := by
            apply Fin.ext; dsimp; omega
          rw [heq]; omega⟩
      rw [finSumNat_zero] at hge
      exact hge
    omega

/-- Headline Theorem 6 (`late_loaded_merging_flop_infeasibility_ceiling`). -/
theorem late_loaded_merging_flop_infeasibility_ceiling :
    (∀ (L k N0 c : Nat) (r : Fin L → Nat),
      k ≤ L → 1 ≤ k → 1 ≤ N0 → 2 * L ≤ 3 * k →
      (∀ l : Fin L, l.val < k → r l = 0) →
      2 * L * (N0 * N0) ≤ 3 * attnFlops N0 r ∧
      ((L * (N0 * N0) : Nat) : Rat) / (attnFlops N0 r : Rat) ≤ 3 / 2 ∧
      2 * L * (N0 * N0 + c * N0) ≤ 3 * vitFlops N0 c r ∧
      ((L * (N0 * N0 + c * N0) : Nat) : Rat) / (vitFlops N0 c r : Rat) ≤ 3 / 2 ∧
      ((∃ l : Fin L, k ≤ l.val ∧ 1 ≤ remTokens N0 r l) →
        2 * L * (N0 * N0) < 3 * attnFlops N0 r ∧
        ((L * (N0 * N0) : Nat) : Rat) / (attnFlops N0 r : Rat) < 3 / 2 ∧
        2 * L * (N0 * N0 + c * N0) < 3 * vitFlops N0 c r ∧
        ((L * (N0 * N0 + c * N0) : Nat) : Rat) / (vitFlops N0 c r : Rat) < 3 / 2)) ∧
    ((3 / 2 : Rat) < 2 ∧ (3 / 2 : Rat) < 4 ∧ (3 / 2 : Rat) < 8) ∧
    (∀ (r : Fin 24 → Nat),
      (∀ l : Fin 24, l.val < 16 → r l = 0) →
      (∃ l : Fin 24, 16 ≤ l.val ∧ 1 ≤ remTokens 1024 r l) →
      ((24 * (1024 * 1024) : Nat) : Rat) / (attnFlops 1024 r : Rat) < 3 / 2 ∧
      ((24 * (1024 * 1024 + 6144 * 1024) : Nat) : Rat) / (vitFlops 1024 6144 r : Rat) < 3 / 2) := by
  have hmain :
      ∀ (L k N0 c : Nat) (r : Fin L → Nat),
        k ≤ L → 1 ≤ k → 1 ≤ N0 → 2 * L ≤ 3 * k →
        (∀ l : Fin L, l.val < k → r l = 0) →
        2 * L * (N0 * N0) ≤ 3 * attnFlops N0 r ∧
        ((L * (N0 * N0) : Nat) : Rat) / (attnFlops N0 r : Rat) ≤ 3 / 2 ∧
        2 * L * (N0 * N0 + c * N0) ≤ 3 * vitFlops N0 c r ∧
        ((L * (N0 * N0 + c * N0) : Nat) : Rat) / (vitFlops N0 c r : Rat) ≤ 3 / 2 ∧
        ((∃ l : Fin L, k ≤ l.val ∧ 1 ≤ remTokens N0 r l) →
          2 * L * (N0 * N0) < 3 * attnFlops N0 r ∧
          ((L * (N0 * N0) : Nat) : Rat) / (attnFlops N0 r : Rat) < 3 / 2 ∧
          2 * L * (N0 * N0 + c * N0) < 3 * vitFlops N0 c r ∧
          ((L * (N0 * N0 + c * N0) : Nat) : Rat) / (vitFlops N0 c r : Rat) < 3 / 2) := by
    intro L k N0 c r hkL hk1 hN0 h2L3k hzero
    have hattn_pair := finSumNat_ge_prefix_const hkL
      (fun l : Fin L => remTokens N0 r l * remTokens N0 r l)
      (fun l hl => by rw [late_loaded_remTokens_eq_N0 r hzero l hl])
    have hvit_pair := finSumNat_ge_prefix_const hkL
      (fun l : Fin L => remTokens N0 r l * remTokens N0 r l + c * remTokens N0 r l)
      (fun l hl => by rw [late_loaded_remTokens_eq_N0 r hzero l hl])
    have hattn_ge : k * (N0 * N0) ≤ attnFlops N0 r := hattn_pair.1
    have hvit_ge : k * (N0 * N0 + c * N0) ≤ vitFlops N0 c r := hvit_pair.1
    have hattn_pos : 0 < attnFlops N0 r := by
      have : 1 ≤ k * (N0 * N0) := Nat.mul_pos hk1 (Nat.mul_pos hN0 hN0)
      omega
    have hvit_pos : 0 < vitFlops N0 c r := by
      have : 1 ≤ k * (N0 * N0 + c * N0) := Nat.mul_pos hk1 (by
        have := Nat.mul_pos hN0 hN0; omega)
      omega
    have hattn_3 : 2 * L * (N0 * N0) ≤ 3 * attnFlops N0 r := by
      have h1 : 2 * L * (N0 * N0) ≤ 3 * k * (N0 * N0) := Nat.mul_le_mul_right (N0 * N0) h2L3k
      have h2 : 3 * (k * (N0 * N0)) ≤ 3 * attnFlops N0 r := Nat.mul_le_mul_left 3 hattn_ge
      rw [Nat.mul_assoc 3 k] at h1
      exact Nat.le_trans h1 h2
    have hvit_3 : 2 * L * (N0 * N0 + c * N0) ≤ 3 * vitFlops N0 c r := by
      have h1 : 2 * L * (N0 * N0 + c * N0) ≤ 3 * k * (N0 * N0 + c * N0) :=
        Nat.mul_le_mul_right (N0 * N0 + c * N0) h2L3k
      have h2 : 3 * (k * (N0 * N0 + c * N0)) ≤ 3 * vitFlops N0 c r := Nat.mul_le_mul_left 3 hvit_ge
      rw [Nat.mul_assoc 3 k] at h1
      exact Nat.le_trans h1 h2
    have hrat_le : ∀ (a b : Nat), 0 < b → a * 2 ≤ 3 * b → (a : Rat) / (b : Rat) ≤ 3 / 2 := by
      intro a b hb hle
      exact rat_div_le_div_of_nat (a := a) (b := b) (c := 3) (d := 2) hb (by omega) hle
    have hrat_lt : ∀ (a b : Nat), 0 < b → a * 2 < 3 * b → (a : Rat) / (b : Rat) < 3 / 2 := by
      intro a b hb hlt
      exact rat_div_lt_div_of_nat (a := a) (b := b) (c := 3) (d := 2) hb (by omega) hlt
    have hattn_3_comm : L * (N0 * N0) * 2 ≤ 3 * attnFlops N0 r := by
      have heq : L * (N0 * N0) * 2 = 2 * L * (N0 * N0) := by
        rw [Nat.mul_comm (L * (N0 * N0)) 2, ← Nat.mul_assoc]
      rw [heq]; exact hattn_3
    have hvit_3_comm : L * (N0 * N0 + c * N0) * 2 ≤ 3 * vitFlops N0 c r := by
      have heq : L * (N0 * N0 + c * N0) * 2 = 2 * L * (N0 * N0 + c * N0) := by
        rw [Nat.mul_comm (L * (N0 * N0 + c * N0)) 2, ← Nat.mul_assoc]
      rw [heq]; exact hvit_3
    refine ⟨hattn_3, hrat_le _ _ hattn_pos hattn_3_comm, hvit_3, hrat_le _ _ hvit_pos hvit_3_comm, ?_⟩
    intro ⟨l0, hl0k, hl0rem⟩
    have hattn_lt : k * (N0 * N0) < attnFlops N0 r :=
      hattn_pair.2 ⟨l0, hl0k, Nat.mul_pos hl0rem hl0rem⟩
    have hvit_lt : k * (N0 * N0 + c * N0) < vitFlops N0 c r :=
      hvit_pair.2 ⟨l0, hl0k, by have := Nat.mul_pos hl0rem hl0rem; omega⟩
    have hattn_3lt : 2 * L * (N0 * N0) < 3 * attnFlops N0 r := by
      have h1 : 2 * L * (N0 * N0) ≤ 3 * k * (N0 * N0) := Nat.mul_le_mul_right (N0 * N0) h2L3k
      have h2 : 3 * (k * (N0 * N0)) < 3 * attnFlops N0 r := Nat.mul_lt_mul_of_pos_left hattn_lt (by omega)
      rw [Nat.mul_assoc 3 k] at h1
      exact Nat.lt_of_le_of_lt h1 h2
    have hvit_3lt : 2 * L * (N0 * N0 + c * N0) < 3 * vitFlops N0 c r := by
      have h1 : 2 * L * (N0 * N0 + c * N0) ≤ 3 * k * (N0 * N0 + c * N0) :=
        Nat.mul_le_mul_right (N0 * N0 + c * N0) h2L3k
      have h2 : 3 * (k * (N0 * N0 + c * N0)) < 3 * vitFlops N0 c r := Nat.mul_lt_mul_of_pos_left hvit_lt (by omega)
      rw [Nat.mul_assoc 3 k] at h1
      exact Nat.lt_of_le_of_lt h1 h2
    have hattn_3lt_comm : L * (N0 * N0) * 2 < 3 * attnFlops N0 r := by
      have heq : L * (N0 * N0) * 2 = 2 * L * (N0 * N0) := by
        rw [Nat.mul_comm (L * (N0 * N0)) 2, ← Nat.mul_assoc]
      rw [heq]; exact hattn_3lt
    have hvit_3lt_comm : L * (N0 * N0 + c * N0) * 2 < 3 * vitFlops N0 c r := by
      have heq : L * (N0 * N0 + c * N0) * 2 = 2 * L * (N0 * N0 + c * N0) := by
        rw [Nat.mul_comm (L * (N0 * N0 + c * N0)) 2, ← Nat.mul_assoc]
      rw [heq]; exact hvit_3lt
    exact ⟨hattn_3lt, hrat_lt _ _ hattn_pos hattn_3lt_comm, hvit_3lt, hrat_lt _ _ hvit_pos hvit_3lt_comm⟩
  refine ⟨hmain, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · have h := rat_div_lt_div_of_nat (a := 3) (b := 2) (c := 2) (d := 1) (by omega) (by omega) (by omega)
      have h2 : ((2 : Nat) : Rat) / ((1 : Nat) : Rat) = 2 := by grind
      rw [h2] at h; exact h
    · have h := rat_div_lt_div_of_nat (a := 3) (b := 2) (c := 4) (d := 1) (by omega) (by omega) (by omega)
      have h4 : ((4 : Nat) : Rat) / ((1 : Nat) : Rat) = 4 := by grind
      rw [h4] at h; exact h
    · have h := rat_div_lt_div_of_nat (a := 3) (b := 2) (c := 8) (d := 1) (by omega) (by omega) (by omega)
      have h8 : ((8 : Nat) : Rat) / ((1 : Nat) : Rat) = 8 := by grind
      rw [h8] at h; exact h
  · intro r hzero hex
    have h24 := (hmain 24 16 1024 6144 r (by omega) (by omega) (by omega) (by omega) hzero).2.2.2.2 hex
    exact ⟨h24.2.1, h24.2.2.2⟩

end VlmTomeCumulant
