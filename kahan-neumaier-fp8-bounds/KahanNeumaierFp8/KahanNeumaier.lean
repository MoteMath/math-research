/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KahanNeumaierFp8.RneFreeze

/-!
# The Dual Kahan-vs-Neumaier Separation Theorem

Proves:
- Theorem 2 (`kahan_late_dipole_spike_total_erasure_vs_neumaier`):
  On late dipole spike streams `[1, ..., 1, +S, -S, 1, ..., 1]`, Kahan suffers 100%
  erasure of all pre-spike microbatches while Neumaier achieves 100% exact recovery.
- Theorem 3 (`neumaier_self_swamping_ceiling_beats_by_kahan`):
  On constant sub-ULP increments, Neumaier's compensation register `c` self-swamps at
  the exact ceiling `M_{Neumaier,max}(P) = 2^{P+2}` (`16` E5M2, `32` E4M3, `512` BF16,
  `4096` FP16), while Kahan's per-step fold-back continues accumulating accurately
  past the ceiling (including `FP8-E5M2` at `M = 64`: Neumaier = `16`, Kahan = `64`).
-/

namespace KahanNeumaierFp8

theorem flRNE_exact_of_le_pow {P n : Nat} (h : n ≤ 2 ^ (P + 1)) :
    flRNE P (n : Int) = (n : Int) := by
  rw [flRNE_natCast, flRNENat_exact_of_le_pow h]

theorem flRNE_exact_one (P : Nat) : flRNE P 1 = 1 := by
  have h1 : (1 : Int) = ((1 : Nat) : Int) := rfl
  rw [h1, flRNE_natCast]
  have hle : 1 ≤ 2 ^ (P + 1) := by have := pow2_pos (P + 1); omega
  rw [flRNENat_exact_of_le_pow hle]

theorem flRNE_exact_neg_one (P : Nat) : flRNE P (-1) = -1 := by
  rw [flRNE_neg, flRNE_exact_one]

theorem kahan_foldl_ones_exact {P m : Nat} (hm : m ≤ 2 ^ (P + 1)) :
    (List.replicate m (1 : Int)).foldl (kahanStep P) (0, 0) = ((m : Int), 0) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have hk : k ≤ 2 ^ (P + 1) := by omega
    have hrep : List.replicate (k + 1) (1 : Int) = List.replicate k 1 ++ [1] :=
      List.replicate_succ'
    rw [hrep, List.foldl_append, ih hk]
    simp only [List.foldl_cons, List.foldl_nil, kahanStep, rneSub, rneAdd]
    have h1 : (1 : Int) - 0 = 1 := by omega
    have h2 : (k : Int) + 1 = ((k + 1 : Nat) : Int) := by omega
    have h3 : ((k + 1 : Nat) : Int) - (k : Int) = 1 := by omega
    have h4 : (1 : Int) - 1 = 0 := by omega
    rw [h1, flRNE_exact_one, h2, flRNE_exact_of_le_pow hm, h3, flRNE_exact_one, h4, flRNE_zero]

theorem neumaier_foldl_ones_exact {P m : Nat} (hm : m ≤ 2 ^ (P + 1)) :
    (List.replicate m (1 : Int)).foldl (neumaierStep P) (0, 0) = ((m : Int), 0) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have hk : k ≤ 2 ^ (P + 1) := by omega
    have hrep : List.replicate (k + 1) (1 : Int) = List.replicate k 1 ++ [1] :=
      List.replicate_succ'
    rw [hrep, List.foldl_append, ih hk]
    simp only [List.foldl_cons, List.foldl_nil, neumaierStep, rneSub, rneAdd]
    have hsum : (k : Int) + 1 = ((k + 1 : Nat) : Int) := by omega
    rw [hsum, flRNE_exact_of_le_pow hm]
    cases k with
    | zero =>
      have hfalse : ¬ (((0 : Nat) : Int).natAbs ≥ (1 : Int).natAbs) := by decide
      simp only [hfalse, ↓reduceIte]
      have h0 : (1 : Int) - ((1 : Nat) : Int) = 0 := by omega
      have h00 : (0 : Int) + ((0 : Nat) : Int) = 0 := by omega
      have h000 : (0 : Int) + 0 = 0 := by omega
      rw [h0, flRNE_zero, h00, flRNE_zero, h000, flRNE_zero]
    | succ k' =>
      have hge : (((k' + 1 : Nat) : Int).natAbs ≥ (1 : Int).natAbs) := by omega
      simp only [hge, ↓reduceIte]
      have hsub : ((k' + 1 : Nat) : Int) - ((k' + 2 : Nat) : Int) = -1 := by omega
      have hadd : (-1 : Int) + 1 = 0 := by omega
      have h00 : (0 : Int) + 0 = 0 := by omega
      rw [hsub, flRNE_exact_neg_one, hadd, flRNE_zero, h00, flRNE_zero]

theorem neumaier_foldl_ones_from_c {P m c : Nat} (hm : m ≤ 2 ^ (P + 1)) (hc : c ≤ 2 ^ (P + 1)) :
    (List.replicate m (1 : Int)).foldl (neumaierStep P) (0, (c : Int)) =
      ((m : Int), (c : Int)) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have hk : k ≤ 2 ^ (P + 1) := by omega
    have hrep : List.replicate (k + 1) (1 : Int) = List.replicate k 1 ++ [1] :=
      List.replicate_succ'
    rw [hrep, List.foldl_append, ih hk]
    simp only [List.foldl_cons, List.foldl_nil, neumaierStep, rneSub, rneAdd]
    have hsum : (k : Int) + 1 = ((k + 1 : Nat) : Int) := by omega
    rw [hsum, flRNE_exact_of_le_pow hm]
    cases k with
    | zero =>
      have hfalse : ¬ (((0 : Nat) : Int).natAbs ≥ (1 : Int).natAbs) := by decide
      simp only [hfalse, ↓reduceIte]
      have h0 : (1 : Int) - ((1 : Nat) : Int) = 0 := by omega
      have h00 : (0 : Int) + ((0 : Nat) : Int) = 0 := by omega
      have hc0 : (c : Int) + 0 = (c : Int) := by omega
      rw [h0, flRNE_zero, h00, flRNE_zero, hc0, flRNE_exact_of_le_pow hc]
    | succ k' =>
      have hge : (((k' + 1 : Nat) : Int).natAbs ≥ (1 : Int).natAbs) := by omega
      simp only [hge, ↓reduceIte]
      have hsub : ((k' + 1 : Nat) : Int) - ((k' + 2 : Nat) : Int) = -1 := by omega
      have hadd : (-1 : Int) + 1 = 0 := by omega
      have hc0 : (c : Int) + 0 = (c : Int) := by omega
      rw [hsub, flRNE_exact_neg_one, hadd, flRNE_zero, hc0, flRNE_exact_of_le_pow hc]

theorem kahan_dipole_exact {P mPre mPost e : Nat}
    (hP : 1 ≤ P) (hmPre1 : 1 ≤ mPre) (hmPre2 : mPre ≤ 2 ^ (P + 1))
    (hmPost : mPost ≤ 2 ^ (P + 1))
    (hS : 2 ^ (P + 2) * mPre ≤ 2 ^ e) :
    kahanSum P (dipoleStream mPre mPost ((2 ^ e : Nat) : Int)) = (mPost : Int) := by
  have he_ge : P + 2 ≤ e := by
    apply Nat.le_of_not_lt
    intro h1
    have h2 : 2 ^ e < 2 ^ (P + 2) := Nat.pow_lt_pow_right (by decide) h1
    have h3 : 2 ^ (P + 2) ≤ 2 ^ (P + 2) * mPre := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hm_le_quarter : mPre ≤ 2 ^ (e - P - 2) := by
    have hpow : 2 ^ e = 2 ^ (P + 2) * 2 ^ (e - P - 2) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hpow] at hS
    exact Nat.le_of_mul_le_mul_left hS (pow2_pos (P + 2))
  have hm_le_half : mPre ≤ 2 ^ (e - P - 1) := by
    have hle : 2 ^ (e - P - 2) ≤ 2 ^ (e - P - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  unfold kahanSum kahanRun dipoleStream
  rw [List.foldl_append, List.foldl_append, kahan_foldl_ones_exact hmPre2]
  simp only [List.foldl_cons, List.foldl_nil, kahanStep, rneSub, rneAdd]
  have hS0 : ((2 ^ e : Nat) : Int) - 0 = ((2 ^ e : Nat) : Int) := by omega
  have hflS : flRNE P ((2 ^ e : Nat) : Int) = ((2 ^ e : Nat) : Int) := by
    rw [flRNE_natCast, flRNENat_exact_pow2]
  have hSm : (mPre : Int) + ((2 ^ e : Nat) : Int) = ((2 ^ e + mPre : Nat) : Int) := by omega
  have hflAdd : flRNE P ((2 ^ e + mPre : Nat) : Int) = ((2 ^ e : Nat) : Int) := by
    rw [flRNE_natCast, flRNENat_pow2_add_of_le_half hP (by omega) hm_le_half]
  have hm_le_S : mPre ≤ 2 ^ e := by
    have : 2 ^ (e - P - 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hSsub : ((2 ^ e : Nat) : Int) - (mPre : Int) = ((2 ^ e - mPre : Nat) : Int) := by omega
  have hflSub : flRNE P ((2 ^ e - mPre : Nat) : Int) = ((2 ^ e : Nat) : Int) := by
    rw [flRNE_natCast, flRNENat_pow2_sub_of_le_quarter he_ge hm_le_quarter]
  have hSS : ((2 ^ e : Nat) : Int) - ((2 ^ e : Nat) : Int) = 0 := by omega
  have hnegS0 : -((2 ^ e : Nat) : Int) - 0 = -((2 ^ e : Nat) : Int) := by omega
  have hflNegS : flRNE P (-((2 ^ e : Nat) : Int)) = -((2 ^ e : Nat) : Int) := by
    rw [flRNE_neg, hflS]
  have hSnegS : ((2 ^ e : Nat) : Int) + -((2 ^ e : Nat) : Int) = 0 := by omega
  have h0S : (0 : Int) - ((2 ^ e : Nat) : Int) = -((2 ^ e : Nat) : Int) := by omega
  have hnegSS : -((2 ^ e : Nat) : Int) - -((2 ^ e : Nat) : Int) = 0 := by omega
  rw [hS0, hflS, hSm, hflAdd, hSsub, hflSub, hSS, flRNE_zero,
      hnegS0, hflNegS, hSnegS, flRNE_zero, h0S, hflNegS, hnegSS, flRNE_zero]
  rw [kahan_foldl_ones_exact hmPost]

theorem neumaier_dipole_exact {P mPre mPost e : Nat}
    (hP : 1 ≤ P) (hmPre1 : 1 ≤ mPre) (hmSum : mPre + mPost ≤ 2 ^ (P + 1))
    (hS : 2 ^ (P + 2) * mPre ≤ 2 ^ e) :
    neumaierSum P (dipoleStream mPre mPost ((2 ^ e : Nat) : Int)) = ((mPre + mPost : Nat) : Int) := by
  have hmPre2 : mPre ≤ 2 ^ (P + 1) := by omega
  have hmPost : mPost ≤ 2 ^ (P + 1) := by omega
  have he_ge : P + 2 ≤ e := by
    apply Nat.le_of_not_lt
    intro h1
    have h2 : 2 ^ e < 2 ^ (P + 2) := Nat.pow_lt_pow_right (by decide) h1
    have h3 : 2 ^ (P + 2) ≤ 2 ^ (P + 2) * mPre := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hm_le_quarter : mPre ≤ 2 ^ (e - P - 2) := by
    have hpow : 2 ^ e = 2 ^ (P + 2) * 2 ^ (e - P - 2) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hpow] at hS
    exact Nat.le_of_mul_le_mul_left hS (pow2_pos (P + 2))
  have hm_le_half : mPre ≤ 2 ^ (e - P - 1) := by
    have hle : 2 ^ (e - P - 2) ≤ 2 ^ (e - P - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hm_lt_S : mPre < 2 ^ e := by
    have h2 : 4 ≤ 2 ^ (P + 2) := by
      have : 2 ^ 2 ≤ 2 ^ (P + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using this
    have h4 : 4 * mPre ≤ 2 ^ (P + 2) * mPre := Nat.mul_le_mul_right mPre h2
    omega
  unfold neumaierSum neumaierRun dipoleStream
  rw [List.foldl_append, List.foldl_append, neumaier_foldl_ones_exact hmPre2]
  simp only [List.foldl_cons, List.foldl_nil, neumaierStep, rneSub, rneAdd]
  have hSm : (mPre : Int) + ((2 ^ e : Nat) : Int) = ((2 ^ e + mPre : Nat) : Int) := by omega
  have hflAdd : flRNE P ((2 ^ e + mPre : Nat) : Int) = ((2 ^ e : Nat) : Int) := by
    rw [flRNE_natCast, flRNENat_pow2_add_of_le_half hP (by omega) hm_le_half]
  have hnotge : ¬ ((mPre : Int).natAbs ≥ ((2 ^ e : Nat) : Int).natAbs) := by omega
  have hSS : ((2 ^ e : Nat) : Int) - ((2 ^ e : Nat) : Int) = 0 := by omega
  have h0m : (0 : Int) + (mPre : Int) = (mPre : Int) := by omega
  have hflm : flRNE P (mPre : Int) = (mPre : Int) := flRNE_exact_of_le_pow hmPre2
  have hSnegS : ((2 ^ e : Nat) : Int) + -((2 ^ e : Nat) : Int) = 0 := by omega
  have hgeS : (((2 ^ e : Nat) : Int).natAbs ≥ (-((2 ^ e : Nat) : Int)).natAbs) := by omega
  have hS0 : ((2 ^ e : Nat) : Int) - 0 = ((2 ^ e : Nat) : Int) := by omega
  have hflS : flRNE P ((2 ^ e : Nat) : Int) = ((2 ^ e : Nat) : Int) := by
    rw [flRNE_natCast, flRNENat_exact_pow2]
  have hm0 : (mPre : Int) + 0 = (mPre : Int) := by omega
  rw [hSm, hflAdd]
  simp only [hnotge, ↓reduceIte]
  rw [hSS, flRNE_zero, h0m, hflm, h0m, hflm, hSnegS, flRNE_zero]
  simp only [hgeS, ↓reduceIte]
  rw [hS0, hflS, hSnegS, flRNE_zero, hm0, hflm]
  rw [neumaier_foldl_ones_from_c hmPost hmPre2]
  have hfinal : (mPost : Int) + (mPre : Int) = ((mPre + mPost : Nat) : Int) := by omega
  rw [hfinal, flRNE_exact_of_le_pow hmSum]

/-- Headline Theorem 2 (`kahan_late_dipole_spike_total_erasure_vs_neumaier`):
    First half of the Dual Kahan-vs-Neumaier Separation Theorem. -/
theorem kahan_late_dipole_spike_total_erasure_vs_neumaier :
    (∀ (P mPre mPost e : Nat),
      1 ≤ P → 1 ≤ mPre → mPre + mPost ≤ 2 ^ (P + 1) → 2 ^ (P + 2) * mPre ≤ 2 ^ e →
      kahanSum P (dipoleStream mPre mPost ((2 ^ e : Nat) : Int)) = (mPost : Int) ∧
      neumaierSum P (dipoleStream mPre mPost ((2 ^ e : Nat) : Int)) = ((mPre + mPost : Nat) : Int)) ∧
    (∀ (P m e : Nat),
      1 ≤ P → 1 ≤ m → m ≤ 2 ^ (P + 1) → 2 ^ (P + 2) * m ≤ 2 ^ e →
      kahanSum P (dipoleStream m 0 ((2 ^ e : Nat) : Int)) = 0 ∧
      neumaierSum P (dipoleStream m 0 ((2 ^ e : Nat) : Int)) = (m : Int)) ∧
    (kahanSum 7 (dipoleStream 254 0 ((2 ^ 17 : Nat) : Int)) = 0 ∧
     neumaierSum 7 (dipoleStream 254 0 ((2 ^ 17 : Nat) : Int)) = 254) ∧
    (kahanSum 10 (dipoleStream 254 0 ((2 ^ 20 : Nat) : Int)) = 0 ∧
     neumaierSum 10 (dipoleStream 254 0 ((2 ^ 20 : Nat) : Int)) = 254) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P mPre mPost e hP hmPre1 hmSum hS
    exact ⟨kahan_dipole_exact hP hmPre1 (by omega) (by omega) hS,
           neumaier_dipole_exact hP hmPre1 hmSum hS⟩
  · intro P m e hP hm1 hm2 hS
    have h := kahan_dipole_exact (P := P) (mPre := m) (mPost := 0) (e := e)
      hP hm1 hm2 (by omega) hS
    have h2 := neumaier_dipole_exact (P := P) (mPre := m) (mPost := 0) (e := e)
      hP hm1 (by omega) hS
    simpa using And.intro h h2
  · exact ⟨kahan_dipole_exact (P := 7) (mPre := 254) (mPost := 0) (e := 17)
            (by omega) (by omega) (by decide) (by omega) (by decide),
           neumaier_dipole_exact (P := 7) (mPre := 254) (mPost := 0) (e := 17)
            (by omega) (by omega) (by decide) (by decide)⟩
  · exact ⟨kahan_dipole_exact (P := 10) (mPre := 254) (mPost := 0) (e := 20)
            (by omega) (by omega) (by decide) (by omega) (by decide),
           neumaier_dipole_exact (P := 10) (mPre := 254) (mPost := 0) (e := 20)
            (by omega) (by omega) (by decide) (by decide)⟩

/-! ### Second Half of Dual Separation: Neumaier Self-Swamping Ceiling vs Kahan Fold-Back -/

theorem neumaier_foldl_ones_phase2 {P j : Nat} (hP : 1 ≤ P) (hj : j ≤ 2 ^ (P + 1)) :
    (List.replicate (2 ^ (P + 1) + j) (1 : Int)).foldl (neumaierStep P) (0, 0) =
      (((2 ^ (P + 1) : Nat) : Int), (j : Int)) := by
  induction j with
  | zero =>
    simpa using neumaier_foldl_ones_exact (P := P) (m := 2 ^ (P + 1)) (Nat.le_refl _)
  | succ k ih =>
    have hk : k ≤ 2 ^ (P + 1) := by omega
    have hrep : List.replicate (2 ^ (P + 1) + (k + 1)) (1 : Int) =
        List.replicate (2 ^ (P + 1) + k) 1 ++ [1] := by
      have h1 : 2 ^ (P + 1) + (k + 1) = (2 ^ (P + 1) + k) + 1 := by omega
      rw [h1]
      exact List.replicate_succ'
    rw [hrep, List.foldl_append, ih hk]
    simp only [List.foldl_cons, List.foldl_nil, neumaierStep, rneSub, rneAdd]
    have hfreeze : flRNE P (((2 ^ (P + 1) : Nat) : Int) + 1) = ((2 ^ (P + 1) : Nat) : Int) :=
      flRNE_freeze_at_min hP
    have hge : (((2 ^ (P + 1) : Nat) : Int).natAbs ≥ (1 : Int).natAbs) := by
      have := pow2_pos (P + 1); omega
    rw [hfreeze]
    simp only [hge, ↓reduceIte]
    have hss : ((2 ^ (P + 1) : Nat) : Int) - ((2 ^ (P + 1) : Nat) : Int) = 0 := by omega
    have h01 : (0 : Int) + 1 = 1 := by omega
    have hk1 : (k : Int) + 1 = ((k + 1 : Nat) : Int) := by omega
    rw [hss, flRNE_zero, h01, flRNE_exact_one, hk1, flRNE_exact_of_le_pow hj]

theorem neumaier_stalls_past_ceiling {P M : Nat} (hP : 1 ≤ P) (hM : neumaierCeiling P ≤ M) :
    neumaierRun P (List.replicate M 1) =
      (((2 ^ (P + 1) : Nat) : Int), ((2 ^ (P + 1) : Nat) : Int)) := by
  have hceil : neumaierCeiling P = 2 ^ (P + 1) + 2 ^ (P + 1) := by
    unfold neumaierCeiling; rw [Nat.pow_succ]; omega
  obtain ⟨d, hd⟩ : ∃ d, M = 2 ^ (P + 1) + 2 ^ (P + 1) + d := ⟨M - neumaierCeiling P, by omega⟩
  rw [hd]
  clear hd hM
  induction d with
  | zero =>
    simpa [neumaierRun] using neumaier_foldl_ones_phase2 (P := P) (j := 2 ^ (P + 1)) hP (Nat.le_refl _)
  | succ d ih =>
    unfold neumaierRun
    have hrep : List.replicate (2 ^ (P + 1) + 2 ^ (P + 1) + (d + 1)) (1 : Int) =
        List.replicate (2 ^ (P + 1) + 2 ^ (P + 1) + d) 1 ++ [1] := by
      have h1 : 2 ^ (P + 1) + 2 ^ (P + 1) + (d + 1) =
          (2 ^ (P + 1) + 2 ^ (P + 1) + d) + 1 := by omega
      rw [h1]
      exact List.replicate_succ'
    rw [hrep, List.foldl_append]
    unfold neumaierRun at ih
    rw [ih]
    simp only [List.foldl_cons, List.foldl_nil, neumaierStep, rneSub, rneAdd]
    have hfreeze : flRNE P (((2 ^ (P + 1) : Nat) : Int) + 1) = ((2 ^ (P + 1) : Nat) : Int) :=
      flRNE_freeze_at_min hP
    have hge : (((2 ^ (P + 1) : Nat) : Int).natAbs ≥ (1 : Int).natAbs) := by
      have := pow2_pos (P + 1); omega
    rw [hfreeze]
    simp only [hge, ↓reduceIte]
    have hss : ((2 ^ (P + 1) : Nat) : Int) - ((2 ^ (P + 1) : Nat) : Int) = 0 := by omega
    have h01 : (0 : Int) + 1 = 1 := by omega
    rw [hss, flRNE_zero, h01, flRNE_exact_one, hfreeze]

theorem neumaierSum_stalls_past_ceiling {P M : Nat} (hP : 1 ≤ P) (hM : neumaierCeiling P ≤ M) :
    neumaierSum P (List.replicate M 1) = (neumaierCeiling P : Int) := by
  unfold neumaierSum
  rw [neumaier_stalls_past_ceiling hP hM]
  dsimp only
  unfold rneAdd neumaierCeiling
  have hsum : ((2 ^ (P + 1) : Nat) : Int) + ((2 ^ (P + 1) : Nat) : Int) =
      ((2 ^ (P + 2) : Nat) : Int) := by
    rw [← Int.natCast_add]
    congr 1
    have hpow : 2 ^ (P + 2) = 2 ^ (P + 1) * 2 := Nat.pow_succ 2 (P + 1)
    omega
  rw [hsum, flRNE_natCast, flRNENat_exact_pow2]

/-- Exact rounding of an odd integer `2 * k + 1` in `[2^{P+1}, 2^{P+2})`:
    rounds to `2 * k` when `k` is even and to `2 * k + 2` when `k` is odd. -/
theorem flRNENat_odd_in_binade {P k : Nat} (h1 : 2 ^ P ≤ k) (h2 : k < 2 ^ (P + 1)) :
    flRNENat P (2 * k + 1) = if k % 2 = 0 then 2 * k else 2 * k + 2 := by
  have hb1 : 2 ^ (P + 1) ≤ 2 * k + 1 := by rw [Nat.pow_succ]; omega
  have hb2 : 2 * k + 1 < 2 ^ (P + 2) := by
    have : 2 ^ (P + 2) = 2 * 2 ^ (P + 1) := by rw [Nat.pow_succ]; omega
    omega
  have hlog : Nat.log2 (2 * k + 1) = P + 1 := nat_log2_eq_of_bounds hb1 hb2
  have hn : 2 * k + 1 ≠ 0 := by omega
  unfold flRNENat
  simp only [hn, ↓reduceIte, hlog]
  have hnot : ¬ (P + 1 ≤ P) := by omega
  have hsub1 : P + 1 - P = 1 := by omega
  simp only [hnot, ↓reduceIte, hsub1, Nat.pow_one]
  have hdiv : (2 * k + 1) / 2 = k := by omega
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  have hpow0 : 2 ^ (1 - 1) = 1 := by decide
  simp only [hdiv, hmod, hpow0]
  have hnlt : ¬ (1 < 1) := by omega
  simp only [hnlt, ↓reduceIte]
  split
  · omega
  · omega

/-- Every 2 steps of `1` in `[2^{P+1}, 2^{P+2})`, Kahan advances by exactly `2` with `c = 0`. -/
theorem kahan_two_ones_binade {P k : Nat} (hP : 1 ≤ P) (hk : k < 2 ^ P) :
    kahanStep P (kahanStep P (((2 ^ (P + 1) + 2 * k : Nat) : Int), 0) 1) 1 =
      (((2 ^ (P + 1) + 2 * k + 2 : Nat) : Int), 0) := by
  let q := 2 ^ P + k
  have hq1 : 2 ^ P ≤ q := by omega
  have hq2 : q < 2 ^ (P + 1) := by rw [Nat.pow_succ]; omega
  have h2q : 2 ^ (P + 1) + 2 * k = 2 * q := by
    show 2 ^ (P + 1) + 2 * k = 2 * (2 ^ P + k)
    rw [Nat.pow_succ]; omega
  have h2_le : 2 ≤ 2 ^ (P + 1) := by
    have : 2 ^ 1 ≤ 2 ^ (P + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hfl2 : flRNE P 2 = 2 := by
    have h2 : (2 : Int) = ((2 : Nat) : Int) := rfl
    rw [h2]; exact flRNE_exact_of_le_pow h2_le
  have hfl2q2 : flRNE P ((2 * q + 2 : Nat) : Int) = ((2 * q + 2 : Nat) : Int) := by
    rw [flRNE_natCast]
    by_cases htop : q + 1 = 2 ^ (P + 1)
    · have : 2 * q + 2 = 2 ^ (P + 2) := by rw [Nat.pow_succ]; omega
      rw [this, flRNENat_exact_pow2]
    · have : 2 * q + 2 = 2 * (q + 1) := by omega
      rw [this, flRNENat_even_in_binade (by omega) (by omega)]
  simp only [kahanStep, rneSub, rneAdd]
  have h10 : (1 : Int) - 0 = 1 := by omega
  rw [h10, flRNE_exact_one]
  have hsum1 : ((2 ^ (P + 1) + 2 * k : Nat) : Int) + 1 = ((2 * q + 1 : Nat) : Int) := by omega
  rw [hsum1, flRNE_natCast, flRNENat_odd_in_binade hq1 hq2]
  by_cases heven : q % 2 = 0
  · simp only [heven, ↓reduceIte]
    have hss : ((2 * q : Nat) : Int) - ((2 ^ (P + 1) + 2 * k : Nat) : Int) = 0 := by omega
    have h01 : (0 : Int) - 1 = -1 := by omega
    have h1m1 : (1 : Int) - (-1) = 2 := by omega
    have hsum2 : ((2 * q : Nat) : Int) + 2 = ((2 * q + 2 : Nat) : Int) := by omega
    have hdiff2 : ((2 * q + 2 : Nat) : Int) - ((2 * q : Nat) : Int) = 2 := by omega
    have h22 : (2 : Int) - 2 = 0 := by omega
    rw [hss, flRNE_zero, h01, flRNE_exact_neg_one, h1m1, hfl2,
        hsum2, hfl2q2, hdiff2, hfl2, h22, flRNE_zero]
    have hgoal : ((2 * q + 2 : Nat) : Int) = ((2 ^ (P + 1) + 2 * k + 2 : Nat) : Int) := by omega
    rw [hgoal]
  · simp only [heven, ↓reduceIte]
    have hdiff1 : ((2 * q + 2 : Nat) : Int) - ((2 ^ (P + 1) + 2 * k : Nat) : Int) = 2 := by omega
    have h21 : (2 : Int) - 1 = 1 := by omega
    have h11 : (1 : Int) - 1 = 0 := by omega
    have hsum2 : ((2 * q + 2 : Nat) : Int) + 0 = ((2 * q + 2 : Nat) : Int) := by omega
    have hss2 : ((2 * q + 2 : Nat) : Int) - ((2 * q + 2 : Nat) : Int) = 0 := by omega
    have h00 : (0 : Int) - 0 = 0 := by omega
    rw [hdiff1, hfl2, h21, flRNE_exact_one, h11, flRNE_zero,
        hsum2, hfl2q2, hss2, flRNE_zero, h00, flRNE_zero]
    have hgoal : ((2 * q + 2 : Nat) : Int) = ((2 ^ (P + 1) + 2 * k + 2 : Nat) : Int) := by omega
    rw [hgoal]

theorem replicate_add {α : Type} (m n : Nat) (a : α) :
    List.replicate (m + n) a = List.replicate m a ++ List.replicate n a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, List.cons_append, ih]

theorem kahan_reaches_ceiling {P k : Nat} (hP : 1 ≤ P) (hk : k ≤ 2 ^ P) :
    (List.replicate (2 ^ (P + 1) + 2 * k) (1 : Int)).foldl (kahanStep P) (0, 0) =
      (((2 ^ (P + 1) + 2 * k : Nat) : Int), 0) := by
  induction k with
  | zero =>
    simpa using kahan_foldl_ones_exact (P := P) (m := 2 ^ (P + 1)) (Nat.le_refl _)
  | succ k ih =>
    have hrep : List.replicate (2 ^ (P + 1) + 2 * (k + 1)) (1 : Int) =
        List.replicate (2 ^ (P + 1) + 2 * k) 1 ++ [1, 1] := by
      have h1 : 2 ^ (P + 1) + 2 * (k + 1) = (2 ^ (P + 1) + 2 * k) + 2 := by omega
      rw [h1, replicate_add]
      rfl
    rw [hrep, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    have hstep := kahan_two_ones_binade (P := P) (k := k) hP (by omega)
    simpa [Nat.mul_add, Nat.add_assoc] using hstep

/-- Exact 4-step Kahan advance past `2^{P+2}`: `(2^{P+2}, 0) → (2^{P+2} + 4, 0)`. -/
theorem kahan_four_ones_past_ceiling {P : Nat} (hP : 1 ≤ P) :
    kahanSum P (List.replicate (neumaierCeiling P + 4) 1) =
      ((neumaierCeiling P + 4 : Nat) : Int) := by
  have hceil : neumaierCeiling P = 2 ^ (P + 1) + 2 * 2 ^ P := by
    unfold neumaierCeiling; rw [Nat.pow_succ, Nat.pow_succ]; omega
  have hrep : List.replicate (neumaierCeiling P + 4) (1 : Int) =
      List.replicate (2 ^ (P + 1) + 2 * 2 ^ P) 1 ++ [1, 1, 1, 1] := by
    rw [hceil, replicate_add]
    rfl
  unfold kahanSum kahanRun
  rw [hrep, List.foldl_append, kahan_reaches_ceiling hP (Nat.le_refl _)]
  have hstart : 2 ^ (P + 1) + 2 * 2 ^ P = 2 ^ (P + 2) := by
    rw [Nat.pow_succ, Nat.pow_succ]; omega
  rw [hstart]
  have h4_le : 4 ≤ 2 ^ (P + 1) := by
    have : 2 ^ 2 ≤ 2 ^ (P + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hfl2 : flRNE P 2 = 2 := by
    have h2 : (2 : Int) = ((2 : Nat) : Int) := rfl
    rw [h2]; exact flRNE_exact_of_le_pow (by omega)
  have hfl3 : flRNE P 3 = 3 := by
    have h3 : (3 : Int) = ((3 : Nat) : Int) := rfl
    rw [h3]; exact flRNE_exact_of_le_pow (by omega)
  have hfl4 : flRNE P 4 = 4 := by
    have h4 : (4 : Int) = ((4 : Nat) : Int) := rfl
    rw [h4]; exact flRNE_exact_of_le_pow h4_le
  have hflNeg2 : flRNE P (-2) = -2 := by rw [flRNE_neg, hfl2]
  have hadd1 : flRNE P (((2 ^ (P + 2) : Nat) : Int) + 1) = ((2 ^ (P + 2) : Nat) : Int) := by
    have h1 : ((2 ^ (P + 2) : Nat) : Int) + 1 = ((2 ^ (P + 2) + 1 : Nat) : Int) := by omega
    rw [h1, flRNE_natCast]
    have h := flRNENat_pow2_add_of_le_half (P := P) (e := P + 2) (m := 1) hP (by omega) (by
      have : P + 2 - P - 1 = 1 := by omega
      rw [this]; decide)
    rw [h]
  have hadd2 : flRNE P (((2 ^ (P + 2) : Nat) : Int) + 2) = ((2 ^ (P + 2) : Nat) : Int) := by
    have h1 : ((2 ^ (P + 2) : Nat) : Int) + 2 = ((2 ^ (P + 2) + 2 : Nat) : Int) := by omega
    rw [h1, flRNE_natCast]
    have h := flRNENat_pow2_add_of_le_half (P := P) (e := P + 2) (m := 2) hP (by omega) (by
      have : P + 2 - P - 1 = 1 := by omega
      rw [this]; decide)
    rw [h]
  have hadd3 : flRNE P (((2 ^ (P + 2) : Nat) : Int) + 3) = ((2 ^ (P + 2) + 4 : Nat) : Int) := by
    have h1 : ((2 ^ (P + 2) : Nat) : Int) + 3 = ((2 ^ (P + 2) + 3 : Nat) : Int) := by omega
    rw [h1, flRNE_natCast]
    have hlo : 2 ^ (P + 2) ≤ 2 ^ (P + 2) + 3 := by omega
    have hhi : 2 ^ (P + 2) + 3 < 2 ^ (P + 3) := by
      have h8 : 8 ≤ 2 ^ (P + 2) := by
        have : 2 ^ 3 ≤ 2 ^ (P + 2) := Nat.pow_le_pow_right (by decide) (by omega)
        simpa using this
      have hpow3 : 2 ^ (P + 3) = 2 ^ (P + 2) * 2 := Nat.pow_succ 2 (P + 2)
      omega
    have hlog : Nat.log2 (2 ^ (P + 2) + 3) = P + 2 := nat_log2_eq_of_bounds hlo hhi
    unfold flRNENat
    have hnz : 2 ^ (P + 2) + 3 ≠ 0 := by omega
    simp only [hnz, ↓reduceIte, hlog]
    have hnot : ¬ (P + 2 ≤ P) := by omega
    have hs1 : P + 2 - P = 2 := by omega
    simp only [hnot, ↓reduceIte, hs1]
    have hpow4 : 2 ^ (P + 2) = 2 ^ P * 4 := by rw [Nat.pow_succ, Nat.pow_succ]; omega
    have hdiv : (2 ^ (P + 2) + 3) / 4 = 2 ^ P := by omega
    have hmod : (2 ^ (P + 2) + 3) % 4 = 3 := by omega
    have hp2 : 2 ^ 2 = 4 := by decide
    have hp1 : 2 ^ (2 - 1) = 2 := by decide
    simp only [hp2, hp1, hdiv, hmod]
    have h3 : ¬ (3 < 2) := by omega
    have h23 : (2 < 3) := by omega
    simp only [h3, h23, ↓reduceIte]
    omega
  have hadd40 : flRNE P (((2 ^ (P + 2) + 4 : Nat) : Int) + 0) = ((2 ^ (P + 2) + 4 : Nat) : Int) := by
    have h1 : ((2 ^ (P + 2) + 4 : Nat) : Int) + 0 = ((2 ^ (P + 2) + 4 : Nat) : Int) := by omega
    rw [h1, flRNE_natCast]
    have hlo : 2 ^ (P + 2) ≤ 2 ^ (P + 2) + 4 := by omega
    have hhi : 2 ^ (P + 2) + 4 < 2 ^ (P + 3) := by
      have h8 : 8 ≤ 2 ^ (P + 2) := by
        have : 2 ^ 3 ≤ 2 ^ (P + 2) := Nat.pow_le_pow_right (by decide) (by omega)
        simpa using this
      have hpow3 : 2 ^ (P + 3) = 2 ^ (P + 2) * 2 := Nat.pow_succ 2 (P + 2)
      omega
    have hlog : Nat.log2 (2 ^ (P + 2) + 4) = P + 2 := nat_log2_eq_of_bounds hlo hhi
    unfold flRNENat
    have hnz : 2 ^ (P + 2) + 4 ≠ 0 := by omega
    simp only [hnz, ↓reduceIte, hlog]
    have hnot : ¬ (P + 2 ≤ P) := by omega
    have hs1 : P + 2 - P = 2 := by omega
    simp only [hnot, ↓reduceIte, hs1]
    have hpow4 : 2 ^ (P + 2) = 2 ^ P * 4 := by rw [Nat.pow_succ, Nat.pow_succ]; omega
    have hdiv : (2 ^ (P + 2) + 4) / 4 = 2 ^ P + 1 := by omega
    have hmod : (2 ^ (P + 2) + 4) % 4 = 0 := by omega
    have hp2 : 2 ^ 2 = 4 := by decide
    have hp1 : 2 ^ (2 - 1) = 2 := by decide
    simp only [hp2, hp1, hdiv, hmod]
    have h02 : (0 < 2) := by omega
    simp only [h02, ↓reduceIte]
    omega
  simp only [List.foldl_cons, List.foldl_nil, kahanStep, rneSub, rneAdd]
  have hs0 : (1 : Int) - 0 = 1 := by omega
  have hss : ((2 ^ (P + 2) : Nat) : Int) - ((2 ^ (P + 2) : Nat) : Int) = 0 := by omega
  have h0m1 : (0 : Int) - 1 = -1 := by omega
  have h1m1 : (1 : Int) - (-1) = 2 := by omega
  have h0m2 : (0 : Int) - 2 = -2 := by omega
  have h1m2 : (1 : Int) - (-2) = 3 := by omega
  have hdiff4 : ((2 ^ (P + 2) + 4 : Nat) : Int) - ((2 ^ (P + 2) : Nat) : Int) = 4 := by omega
  have h4m3 : (4 : Int) - 3 = 1 := by omega
  have h1m1' : (1 : Int) - 1 = 0 := by omega
  rw [hs0, flRNE_exact_one, hadd1, hss, flRNE_zero, h0m1, flRNE_exact_neg_one,
      h1m1, hfl2, hadd2, hss, flRNE_zero, h0m2, hflNeg2,
      h1m2, hfl3, hadd3, hdiff4, hfl4, h4m3, flRNE_exact_one,
      h1m1', flRNE_zero, hadd40]
  simp [neumaierCeiling]

/-- Headline Theorem 3 (`neumaier_self_swamping_ceiling_beats_by_kahan`):
    Second half of the Dual Kahan-vs-Neumaier Separation Theorem. -/
theorem neumaier_self_swamping_ceiling_beats_by_kahan :
    (neumaierCeiling 2 = 16 ∧ neumaierCeiling 3 = 32 ∧
     neumaierCeiling 7 = 512 ∧ neumaierCeiling 10 = 4096) ∧
    (∀ (P M : Nat), 1 ≤ P → neumaierCeiling P ≤ M →
      neumaierSum P (List.replicate M 1) = (neumaierCeiling P : Int)) ∧
    (∀ (P : Nat), 1 ≤ P →
      neumaierSum P (List.replicate (neumaierCeiling P + 4) 1) = (neumaierCeiling P : Int) ∧
      kahanSum P (List.replicate (neumaierCeiling P + 4) 1) = ((neumaierCeiling P + 4 : Nat) : Int) ∧
      neumaierSum P (List.replicate (neumaierCeiling P + 4) 1) <
        kahanSum P (List.replicate (neumaierCeiling P + 4) 1)) ∧
    (neumaierSum 2 (List.replicate 64 1) = 16 ∧
     kahanSum 2 (List.replicate 64 1) = 64) := by
  refine ⟨⟨by decide, by decide, by decide, by decide⟩, ?_, ?_, ?_⟩
  · intro P M hP hM
    exact neumaierSum_stalls_past_ceiling hP hM
  · intro P hP
    have hN := neumaierSum_stalls_past_ceiling (P := P) (M := neumaierCeiling P + 4) hP (by omega)
    have hK := kahan_four_ones_past_ceiling hP
    refine ⟨hN, hK, ?_⟩
    rw [hN, hK]; omega
  · constructor
    · exact neumaierSum_stalls_past_ceiling (P := 2) (M := 64) (by omega) (by decide)
    · have h16 : (List.replicate 16 (1 : Int)).foldl (kahanStep 2) (0, 0) = (16, 0) :=
        kahan_reaches_ceiling (P := 2) (k := 4) (by omega) (by decide)
      have h16b : (List.replicate 16 (1 : Int)).foldl (kahanStep 2) (16, 0) = (32, 0) := by
        decide
      have h16c : (List.replicate 16 (1 : Int)).foldl (kahanStep 2) (32, 0) = (48, 0) := by
        decide
      have h16d : (List.replicate 16 (1 : Int)).foldl (kahanStep 2) (48, 0) = (64, 0) := by
        decide
      unfold kahanSum kahanRun
      have h64 : List.replicate 64 (1 : Int) =
          List.replicate 16 1 ++ List.replicate 16 1 ++ List.replicate 16 1 ++ List.replicate 16 1 := by
        rw [← replicate_add, ← replicate_add, ← replicate_add]
      rw [h64, List.foldl_append, List.foldl_append, List.foldl_append,
          h16, h16b, h16c, h16d]

end KahanNeumaierFp8
