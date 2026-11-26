/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KahanNeumaierFp8.Defs

/-!
# Exact IEEE-754 RNE Freeze Threshold & Early-Spike vs Pairwise-Tree Separation

Proves Theorem 1 (`microbatch_rne_freeze_threshold_exact`) and provides reusable
exact `flRNENat` / `flRNE` lemmas for `KahanNeumaier.lean`.
-/

namespace KahanNeumaierFp8

theorem pow2_pos (k : Nat) : 0 < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => omega

theorem le_pow2 (k : Nat) : k ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hpos := pow2_pos k
    rw [Nat.pow_succ]
    omega

theorem nat_log2_eq_of_bounds {n e : Nat} (h1 : 2 ^ e ≤ n) (h2 : n < 2 ^ (e + 1)) :
    Nat.log2 n = e := by
  have hpos : 0 < 2 ^ e := pow2_pos e
  have hn : n ≠ 0 := by omega
  have hle : e ≤ Nat.log2 n := (Nat.le_log2 hn).mpr h1
  have hlt : Nat.log2 n < e + 1 := (Nat.log2_lt hn).mpr h2
  omega

theorem flRNENat_zero (P : Nat) : flRNENat P 0 = 0 := by
  simp [flRNENat]

theorem flRNE_zero (P : Nat) : flRNE P 0 = 0 := by
  simp [flRNE, flRNENat]

theorem flRNE_natCast (P n : Nat) : flRNE P (n : Int) = (flRNENat P n : Int) := by
  simp [flRNE]

theorem flRNE_ofNat (P n : Nat) : flRNE P (Int.ofNat n) = Int.ofNat (flRNENat P n) := by
  simp [flRNE]

theorem flRNE_neg (P : Nat) (x : Int) : flRNE P (-x) = -flRNE P x := by
  unfold flRNE
  cases x with
  | ofNat n =>
    cases n with
    | zero => simp [flRNENat]
    | succ k =>
      have h1 : ¬ ((0 : Int) ≤ -(Int.ofNat (k + 1))) := by
        rw [Int.ofNat_eq_natCast]; omega
      have h2 : (0 : Int) ≤ Int.ofNat (k + 1) := by
        rw [Int.ofNat_eq_natCast]; omega
      simp only [h1, h2, ↓reduceIte]
      have habs : (-(Int.ofNat (k + 1))).natAbs = (Int.ofNat (k + 1)).natAbs := by
        rw [Int.natAbs_neg]
      rw [habs]
  | negSucc k =>
    have h1 : (0 : Int) ≤ -(Int.negSucc k) := by omega
    have h2 : ¬ ((0 : Int) ≤ Int.negSucc k) := by omega
    simp only [h1, h2, ↓reduceIte]
    have habs : (-(Int.negSucc k)).natAbs = (Int.negSucc k).natAbs := by
      rw [Int.natAbs_neg]
    rw [habs, Int.neg_neg]

theorem flRNENat_exact_of_lt_pow {P n : Nat} (h : n < 2 ^ (P + 1)) : flRNENat P n = n := by
  unfold flRNENat
  split
  · subst_vars; rfl
  · rename_i hn
    have hlt : Nat.log2 n < P + 1 := (Nat.log2_lt hn).mpr h
    have hle : Nat.log2 n ≤ P := by omega
    simp [hle]

theorem flRNENat_exact_pow2 (P e : Nat) : flRNENat P (2 ^ e) = 2 ^ e := by
  unfold flRNENat
  have hpos : 0 < 2 ^ e := pow2_pos e
  have hn : 2 ^ e ≠ 0 := by omega
  have hlog : Nat.log2 (2 ^ e) = e :=
    nat_log2_eq_of_bounds (Nat.le_refl _) (by
      rw [Nat.pow_succ]
      omega)
  simp only [hn, ↓reduceIte, hlog]
  split
  · rfl
  · rename_i hgt
    have hpow : 2 ^ e = 2 ^ P * 2 ^ (e - P) := by
      rw [← Nat.pow_add]
      congr 1; omega
    have hu_pos : 0 < 2 ^ (e - P) := pow2_pos (e - P)
    have hh_pos : 0 < 2 ^ (e - P - 1) := pow2_pos (e - P - 1)
    have hdiv : 2 ^ e / 2 ^ (e - P) = 2 ^ P := by
      rw [hpow, Nat.mul_div_cancel _ hu_pos]
    have hmod : 2 ^ e % 2 ^ (e - P) = 0 := by
      rw [hpow, Nat.mul_mod_left]
    simp only [hdiv, hmod, hh_pos, ↓reduceIte]
    exact hpow.symm

theorem flRNENat_exact_of_le_pow {P n : Nat} (h : n ≤ 2 ^ (P + 1)) : flRNENat P n = n := by
  by_cases hlt : n < 2 ^ (P + 1)
  · exact flRNENat_exact_of_lt_pow hlt
  · have heq : n = 2 ^ (P + 1) := by omega
    rw [heq]
    exact flRNENat_exact_pow2 P (P + 1)

theorem flRNENat_even_in_binade {P k : Nat} (h1 : 2 ^ P ≤ k) (h2 : k < 2 ^ (P + 1)) :
    flRNENat P (2 * k) = 2 * k := by
  have hb1 : 2 ^ (P + 1) ≤ 2 * k := by rw [Nat.pow_succ]; omega
  have hb2 : 2 * k < 2 ^ (P + 2) := by
    have : 2 ^ (P + 2) = 2 * 2 ^ (P + 1) := by rw [Nat.pow_succ]; omega
    omega
  have hlog : Nat.log2 (2 * k) = P + 1 := nat_log2_eq_of_bounds hb1 hb2
  have hn : 2 * k ≠ 0 := by
    have := pow2_pos (P + 1); omega
  unfold flRNENat
  simp only [hn, ↓reduceIte, hlog]
  have hnot : ¬ (P + 1 ≤ P) := by omega
  have hsub1 : P + 1 - P = 1 := by omega
  simp only [hnot, ↓reduceIte, hsub1, Nat.pow_one]
  have hdiv : 2 * k / 2 = k := by omega
  have hmod : 2 * k % 2 = 0 := by omega
  have h0lt : 0 < 2 ^ (1 - 1) := by decide
  simp only [hdiv, hmod, h0lt, ↓reduceIte]
  omega

theorem flRNENat_pow2_add_of_le_half {P e m : Nat} (hP : 1 ≤ P) (he : P < e)
    (hm : m ≤ 2 ^ (e - P - 1)) :
    flRNENat P (2 ^ e + m) = 2 ^ e := by
  have hu_eq : 2 ^ (e - P) = 2 * 2 ^ (e - P - 1) := by
    have h1 : e - P = (e - P - 1) + 1 := by omega
    conv => lhs; rw [h1, Nat.pow_succ]
    omega
  have hpow : 2 ^ e = 2 ^ P * 2 ^ (e - P) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hu_pos : 0 < 2 ^ (e - P) := pow2_pos (e - P)
  have hh_pos : 0 < 2 ^ (e - P - 1) := pow2_pos (e - P - 1)
  have hm_lt_u : m < 2 ^ (e - P) := by omega
  have hm_lt_e : m < 2 ^ e := by
    have : 2 ^ (e - P) ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hlog : Nat.log2 (2 ^ e + m) = e :=
    nat_log2_eq_of_bounds (by omega) (by rw [Nat.pow_succ]; omega)
  have hn : 2 ^ e + m ≠ 0 := by
    have := pow2_pos e; omega
  unfold flRNENat
  simp only [hn, ↓reduceIte, hlog]
  have hnot : ¬ (e ≤ P) := by omega
  simp only [hnot, ↓reduceIte]
  have hdiv : (2 ^ e + m) / 2 ^ (e - P) = 2 ^ P := by
    rw [hpow, Nat.mul_comm (2 ^ P) (2 ^ (e - P)), Nat.mul_add_div hu_pos,
        Nat.div_eq_of_lt hm_lt_u, Nat.add_zero]
  have hmod : (2 ^ e + m) % 2 ^ (e - P) = m := by
    rw [hpow, Nat.mul_comm (2 ^ P) (2 ^ (e - P)), Nat.mul_add_mod,
        Nat.mod_eq_of_lt hm_lt_u]
  simp only [hdiv, hmod]
  by_cases hlt : m < 2 ^ (e - P - 1)
  · simp only [hlt, ↓reduceIte]
    exact hpow.symm
  · have hnotlt : ¬ (2 ^ (e - P - 1) < m) := by omega
    have heven : 2 ^ P % 2 = 0 := by
      have h1 : P = (P - 1) + 1 := by omega
      rw [h1, Nat.pow_succ]
      omega
    simp only [hlt, hnotlt, heven, ↓reduceIte]
    exact hpow.symm

theorem flRNENat_pow2_sub_of_le_quarter {P e m : Nat} (he : P + 2 ≤ e)
    (hm : m ≤ 2 ^ (e - P - 2)) :
    flRNENat P (2 ^ e - m) = 2 ^ e := by
  by_cases hm0 : m = 0
  · subst hm0; simpa using flRNENat_exact_pow2 P e
  · have hpow_e : 2 ^ e = 2 * 2 ^ (e - 1) := by
      have h1 : e = (e - 1) + 1 := by omega
      conv => lhs; rw [h1, Nat.pow_succ]
      omega
    have hu_eq : 2 ^ (e - 1 - P) = 2 * 2 ^ (e - 1 - P - 1) := by
      have h1 : e - 1 - P = (e - 1 - P - 1) + 1 := by omega
      conv => lhs; rw [h1, Nat.pow_succ]
      omega
    have hsub_eq : e - 1 - P - 1 = e - P - 2 := by omega
    have hpow_u : 2 ^ e = 2 ^ (P + 1) * 2 ^ (e - 1 - P) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hu_pos : 0 < 2 ^ (e - 1 - P) := pow2_pos (e - 1 - P)
    have hh_pos : 0 < 2 ^ (e - 1 - P - 1) := pow2_pos (e - 1 - P - 1)
    have hm_le_h : m ≤ 2 ^ (e - 1 - P - 1) := by rw [hsub_eq]; exact hm
    have hm_lt_u : m < 2 ^ (e - 1 - P) := by omega
    have hP1_pos : 0 < 2 ^ (P + 1) := pow2_pos (P + 1)
    have hdecomp : 2 ^ e - m = (2 ^ (P + 1) - 1) * 2 ^ (e - 1 - P) + (2 ^ (e - 1 - P) - m) := by
      have hmul : 2 ^ (P + 1) * 2 ^ (e - 1 - P) =
          (2 ^ (P + 1) - 1) * 2 ^ (e - 1 - P) + 2 ^ (e - 1 - P) := by
        have h1 : 2 ^ (P + 1) = (2 ^ (P + 1) - 1) + 1 := by omega
        conv => lhs; rw [h1, Nat.add_mul, Nat.one_mul]
      omega
    have hm_le_half_e : m ≤ 2 ^ (e - 1) := by
      have : 2 ^ (e - P - 2) ≤ 2 ^ (e - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hlog : Nat.log2 (2 ^ e - m) = e - 1 :=
      nat_log2_eq_of_bounds (by omega) (by
        have h1 : (e - 1) + 1 = e := by omega
        rw [h1]; omega)
    have hn : 2 ^ e - m ≠ 0 := by
      have := pow2_pos (e - 1); omega
    unfold flRNENat
    simp only [hn, ↓reduceIte, hlog]
    have hnot : ¬ (e - 1 ≤ P) := by omega
    simp only [hnot, ↓reduceIte]
    have hrem_lt : 2 ^ (e - 1 - P) - m < 2 ^ (e - 1 - P) := by omega
    have hdiv : (2 ^ e - m) / 2 ^ (e - 1 - P) = 2 ^ (P + 1) - 1 := by
      rw [hdecomp, Nat.mul_comm (2 ^ (P + 1) - 1) (2 ^ (e - 1 - P)),
          Nat.mul_add_div hu_pos, Nat.div_eq_of_lt hrem_lt, Nat.add_zero]
    have hmod : (2 ^ e - m) % 2 ^ (e - 1 - P) = 2 ^ (e - 1 - P) - m := by
      rw [hdecomp, Nat.mul_comm (2 ^ (P + 1) - 1) (2 ^ (e - 1 - P)),
          Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
    simp only [hdiv, hmod]
    have hnot_lt_h : ¬ (2 ^ (e - 1 - P) - m < 2 ^ (e - 1 - P - 1)) := by omega
    have hq_succ : (2 ^ (P + 1) - 1 + 1) * 2 ^ (e - 1 - P) = 2 ^ e := by
      have : 2 ^ (P + 1) - 1 + 1 = 2 ^ (P + 1) := by omega
      rw [this, ← hpow_u]
    simp only [hnot_lt_h, ↓reduceIte]
    by_cases hgt : 2 ^ (e - 1 - P - 1) < 2 ^ (e - 1 - P) - m
    · simp only [hgt, ↓reduceIte]; exact hq_succ
    · have hodd : (2 ^ (P + 1) - 1) % 2 ≠ 0 := by
        have h2 : 2 ^ (P + 1) = 2 * 2 ^ P := by rw [Nat.pow_succ]; omega
        have := pow2_pos P
        omega
      simp only [hgt, hodd, ↓reduceIte]; exact hq_succ

theorem flRNENat_freeze_above_max {P S : Nat} (hS : 2 ^ (P + 2) ≤ S)
    (hRep : flRNENat P S = S) :
    flRNENat P (S + 1) = S := by
  have hSpos : 0 < S := by
    have := pow2_pos (P + 2); omega
  have hSnz : S ≠ 0 := by omega
  generalize he_def : Nat.log2 S = e
  have he_ge : P + 2 ≤ e := by rw [← he_def]; exact (Nat.le_log2 hSnz).mpr hS
  have hS_lo : 2 ^ e ≤ S := by rw [← he_def]; exact (Nat.le_log2 hSnz).mp (Nat.le_refl _)
  have hS_hi : S < 2 ^ (e + 1) := by rw [← he_def]; exact (Nat.log2_lt hSnz).mp (Nat.lt_succ_self _)
  have hnot_le : ¬ (e ≤ P) := by omega
  have hu_ge4 : 4 ≤ 2 ^ (e - P) := by
    have : 2 ^ 2 ≤ 2 ^ (e - P) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hh_ge2 : 2 ≤ 2 ^ (e - P - 1) := by
    have : 2 ^ 1 ≤ 2 ^ (e - P - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hdiv_u : 2 ^ (e - P) ∣ S := by
    have hfl := hRep
    unfold flRNENat at hfl
    simp only [hSnz, ↓reduceIte, he_def, hnot_le] at hfl
    split at hfl
    · exact ⟨S / 2 ^ (e - P), by rw [Nat.mul_comm]; exact hfl.symm⟩
    · split at hfl
      · exact ⟨S / 2 ^ (e - P) + 1, by rw [Nat.mul_comm]; exact hfl.symm⟩
      · split at hfl
        · exact ⟨S / 2 ^ (e - P), by rw [Nat.mul_comm]; exact hfl.symm⟩
        · exact ⟨S / 2 ^ (e - P) + 1, by rw [Nat.mul_comm]; exact hfl.symm⟩
  rcases hdiv_u with ⟨k, hk⟩
  have hu_pos : 0 < 2 ^ (e - P) := by omega
  have hpow_e1 : 2 ^ (e + 1) = 2 ^ (P + 1) * 2 ^ (e - P) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hk_lt : k < 2 ^ (P + 1) := by
    apply Nat.lt_of_not_ge
    intro h1
    have h2 : 2 ^ (P + 1) * 2 ^ (e - P) ≤ k * 2 ^ (e - P) := Nat.mul_le_mul_right _ h1
    rw [← hpow_e1, Nat.mul_comm, ← hk] at h2
    omega
  have hS1_lt : S + 1 < 2 ^ (e + 1) := by
    have h1 : (k + 1) * 2 ^ (e - P) ≤ 2 ^ (P + 1) * 2 ^ (e - P) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [← hpow_e1, Nat.add_mul, Nat.one_mul, Nat.mul_comm k] at h1
    omega
  have hlog1 : Nat.log2 (S + 1) = e := nat_log2_eq_of_bounds (by omega) hS1_lt
  unfold flRNENat
  have hS1nz : S + 1 ≠ 0 := by omega
  simp only [hS1nz, ↓reduceIte, hlog1, hnot_le]
  have hdiv1 : (S + 1) / 2 ^ (e - P) = k := by
    rw [hk, Nat.mul_add_div hu_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hmod1 : (S + 1) % 2 ^ (e - P) = 1 := by
    rw [hk, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hlt1 : 1 < 2 ^ (e - P - 1) := by omega
  simp only [hdiv1, hmod1, hlt1, ↓reduceIte]
  rw [hk, Nat.mul_comm]

theorem flRNE_freeze_at_min {P : Nat} (hP : 1 ≤ P) :
    flRNE P ((rhoFreezeMin P : Int) + 1) = (rhoFreezeMin P : Int) := by
  have h1 : (rhoFreezeMin P : Int) + 1 = ((2 ^ (P + 1) + 1 : Nat) : Int) := by
    unfold rhoFreezeMin; omega
  rw [h1, flRNE_natCast]
  have h2 := flRNENat_pow2_add_of_le_half (P := P) (e := P + 1) (m := 1) hP (by omega) (by
    have : P + 1 - P - 1 = 0 := by omega
    rw [this]; decide)
  rw [h2]; rfl

theorem seqRNE_early_spike_freeze {P m : Nat} (hP : 1 ≤ P) :
    seqRNE P ((rhoFreezeMin P : Int) :: List.replicate m 1) = (rhoFreezeMin P : Int) := by
  unfold seqRNE
  simp only [List.foldl_cons]
  have h0 : rneAdd P 0 (rhoFreezeMin P : Int) = (rhoFreezeMin P : Int) := by
    unfold rneAdd
    simp only [Int.zero_add, rhoFreezeMin]
    rw [flRNE_natCast, flRNENat_exact_pow2]
  rw [h0]
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [List.replicate_succ, List.foldl_cons]
    have hstep : rneAdd P (rhoFreezeMin P : Int) 1 = (rhoFreezeMin P : Int) :=
      flRNE_freeze_at_min hP
    rw [hstep]
    exact ih

theorem pairwiseStep_replicate {α : Type} (op : α → α → α) (x : α) (n : Nat) :
    pairwiseStep op (List.replicate (2 * n) x) = List.replicate n (op x x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n) + 2 := by omega
    rw [h2]
    simp only [List.replicate_succ, pairwiseStep, List.replicate_succ]
    exact congrArg (op x x :: ·) ih

theorem treeReduceAux_pow2_const {P K : Nat} (fuel : Nat) (hfuel : K ≤ fuel)
    (v : Nat) (hv : v = 2 ^ j) :
    treeReduceAux (rneAdd P) 0 fuel (List.replicate (2 ^ K) (v : Int)) =
      ((2 ^ (j + K) : Nat) : Int) := by
  induction K generalizing fuel j v with
  | zero =>
    cases fuel with
    | zero =>
      subst hv
      simp [treeReduceAux, Nat.add_zero]
    | succ fuel' =>
      subst hv
      simp [treeReduceAux, Nat.add_zero]
  | succ K ih =>
    cases fuel with
    | zero => omega
    | succ fuel' =>
      have hlen : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [Nat.pow_succ]; omega
      have hge2 : 2 ≤ 2 ^ (K + 1) := by
        have := pow2_pos K; omega
      have hcons : ∃ a b rest, List.replicate (2 ^ (K + 1)) (v : Int) = a :: b :: rest := by
        cases h : 2 ^ (K + 1) with
        | zero => omega
        | succ n =>
          cases n with
          | zero => omega
          | succ m => exact ⟨_, _, _, rfl⟩
      rcases hcons with ⟨a, b, rest, hrep⟩
      have hstep : treeReduceAux (rneAdd P) 0 (fuel' + 1)
          (List.replicate (2 ^ (K + 1)) (v : Int)) =
          treeReduceAux (rneAdd P) 0 fuel'
            (pairwiseStep (rneAdd P) (List.replicate (2 ^ (K + 1)) (v : Int))) := by
        rw [hrep]; rfl
      rw [hstep, hlen, pairwiseStep_replicate]
      have hadd : rneAdd P (v : Int) (v : Int) = ((2 ^ (j + 1) : Nat) : Int) := by
        subst hv
        unfold rneAdd
        have hsum : ((2 ^ j : Nat) : Int) + ((2 ^ j : Nat) : Int) =
            ((2 ^ (j + 1) : Nat) : Int) := by
          rw [Nat.pow_succ]; omega
        rw [hsum, flRNE_natCast, flRNENat_exact_pow2]
      rw [hadd]
      have hrec := ih fuel' (by omega) (2 ^ (j + 1)) rfl
      rw [hrec]
      have hexp : j + 1 + K = j + (K + 1) := by omega
      rw [hexp]

theorem treeRNE_pow2_ones (P K : Nat) :
    treeRNE P (List.replicate (2 ^ K) 1) = ((2 ^ K : Nat) : Int) := by
  unfold treeRNE
  rw [List.length_replicate]
  have h := treeReduceAux_pow2_const (P := P) (K := K) (j := 0) (2 ^ K) (le_pow2 K) 1 rfl
  simpa using h

/-- Exact pairwise binary-tree reduction of `S :: List.replicate (2^K - 1) 1` where
    `S = 2^{P+1}` and `1 ≤ K ≤ P + 1`: preserves `2^K - 2` of the `2^K - 1` signals. -/
theorem treeReduceAux_early_spike {P K : Nat} (_hP : 1 ≤ P) (fuel : Nat) (hfuel : K ≤ fuel)
    (j : Nat) (hj : 1 ≤ j) (hK : j + K ≤ P + 1) :
    treeReduceAux (rneAdd P) 0 fuel
      (((2 ^ (P + 1) + 2 ^ j - 2 : Nat) : Int) ::
        List.replicate (2 ^ K - 1) ((2 ^ j : Nat) : Int)) =
      ((2 ^ (P + 1) + 2 ^ (j + K) - 2 : Nat) : Int) := by
  induction K generalizing fuel j with
  | zero =>
    cases fuel with
    | zero => simp [treeReduceAux, Nat.add_zero]
    | succ fuel' => simp [treeReduceAux, Nat.add_zero]
  | succ K ih =>
    cases fuel with
    | zero => omega
    | succ fuel' =>
      have hposK : 0 < 2 ^ K := pow2_pos K
      have hrep_len : 2 ^ (K + 1) - 1 = 1 + 2 * (2 ^ K - 1) := by
        rw [Nat.pow_succ]; omega
      have hlist :
          ((2 ^ (P + 1) + 2 ^ j - 2 : Nat) : Int) ::
            List.replicate (2 ^ (K + 1) - 1) ((2 ^ j : Nat) : Int) =
          ((2 ^ (P + 1) + 2 ^ j - 2 : Nat) : Int) ::
            ((2 ^ j : Nat) : Int) ::
            List.replicate (2 * (2 ^ K - 1)) ((2 ^ j : Nat) : Int) := by
        rw [hrep_len]
        have : 1 + 2 * (2 ^ K - 1) = (2 * (2 ^ K - 1)) + 1 := by omega
        rw [this, List.replicate_succ]
      rw [hlist]
      simp only [treeReduceAux, pairwiseStep, pairwiseStep_replicate]
      have h2j : 2 ≤ 2 ^ j := by
        have : 2 ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
        simpa using this
      have hhead :
          rneAdd P ((2 ^ (P + 1) + 2 ^ j - 2 : Nat) : Int) ((2 ^ j : Nat) : Int) =
            ((2 ^ (P + 1) + 2 ^ (j + 1) - 2 : Nat) : Int) := by
        unfold rneAdd
        have hsum : ((2 ^ (P + 1) + 2 ^ j - 2 : Nat) : Int) + ((2 ^ j : Nat) : Int) =
            ((2 ^ (P + 1) + 2 ^ (j + 1) - 2 : Nat) : Int) := by
          rw [← Int.natCast_add]
          congr 1
          have h1 : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
          have h2 : 0 < 2 ^ (P + 1) := pow2_pos (P + 1)
          omega
        rw [hsum, flRNE_natCast]
        have heven : 2 ^ (P + 1) + 2 ^ (j + 1) - 2 =
            2 * (2 ^ P + 2 ^ j - 1) := by
          have h1 : 2 ^ (P + 1) = 2 * 2 ^ P := by rw [Nat.pow_succ]; omega
          have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
          omega
        rw [heven]
        have hk1 : 2 ^ P ≤ 2 ^ P + 2 ^ j - 1 := by omega
        have hk2 : 2 ^ P + 2 ^ j - 1 < 2 ^ (P + 1) := by
          have : 2 ^ j ≤ 2 ^ P := Nat.pow_le_pow_right (by decide) (by omega)
          have := pow2_pos P
          rw [Nat.pow_succ]; omega
        rw [flRNENat_even_in_binade hk1 hk2]
      have htail : rneAdd P ((2 ^ j : Nat) : Int) ((2 ^ j : Nat) : Int) =
          ((2 ^ (j + 1) : Nat) : Int) := by
        unfold rneAdd
        have hsum : ((2 ^ j : Nat) : Int) + ((2 ^ j : Nat) : Int) =
            ((2 ^ (j + 1) : Nat) : Int) := by
          rw [Nat.pow_succ]; omega
        rw [hsum, flRNE_natCast, flRNENat_exact_pow2]
      rw [hhead, htail]
      have hrec := ih fuel' (by omega) (j + 1) (by omega) (by omega)
      rw [hrec]
      have hexp : j + 1 + K = j + (K + 1) := by omega
      rw [hexp]

theorem treeRNE_early_spike_preserves {P K : Nat} (hP : 1 ≤ P) (hK1 : 1 ≤ K) (hK2 : K ≤ P + 1) :
    treeRNE P ((rhoFreezeMin P : Int) :: List.replicate (2 ^ K - 1) 1) =
      (rhoFreezeMin P : Int) + ((2 ^ K - 2 : Nat) : Int) := by
  unfold treeRNE
  simp only [List.length_cons, List.length_replicate]
  have hKpos : 0 < 2 ^ K := pow2_pos K
  have hlen : 2 ^ K - 1 + 1 = 2 ^ K := by omega
  rw [hlen]
  have h2K_ge2 : 2 ≤ 2 ^ K := by
    have : 2 ^ 1 ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hK1
    simpa using this
  have hrep_len : 2 ^ K - 1 = 1 + 2 * (2 ^ (K - 1) - 1) := by
    have h1 : K = (K - 1) + 1 := by omega
    conv => lhs; rw [h1, Nat.pow_succ]
    have := pow2_pos (K - 1)
    omega
  have hlist :
      (rhoFreezeMin P : Int) :: List.replicate (2 ^ K - 1) 1 =
      (rhoFreezeMin P : Int) :: (1 : Int) :: List.replicate (2 * (2 ^ (K - 1) - 1)) 1 := by
    rw [hrep_len]
    have : 1 + 2 * (2 ^ (K - 1) - 1) = (2 * (2 ^ (K - 1) - 1)) + 1 := by omega
    rw [this, List.replicate_succ]
  rw [hlist]
  have hf_eq : 2 ^ K = (2 ^ K - 1) + 1 := by omega
  have hf_le : K - 1 ≤ 2 ^ K - 1 := by have := le_pow2 K; omega
  conv => lhs; arg 3; rw [hf_eq]
  simp only [treeReduceAux, pairwiseStep, pairwiseStep_replicate]
  have hhead : rneAdd P (rhoFreezeMin P : Int) 1 = ((2 ^ (P + 1) + 2 ^ 1 - 2 : Nat) : Int) := by
    have h1 : rneAdd P (rhoFreezeMin P : Int) 1 = (rhoFreezeMin P : Int) :=
      flRNE_freeze_at_min hP
    rw [h1]
    simp [rhoFreezeMin]
  have htail : rneAdd P 1 1 = ((2 ^ 1 : Nat) : Int) := by
    unfold rneAdd
    have hsum : (1 : Int) + 1 = ((2 : Nat) : Int) := rfl
    rw [hsum, flRNE_natCast, flRNENat_exact_pow2 P 1]
  rw [hhead, htail]
  have hrec := treeReduceAux_early_spike (P := P) (K := K - 1) hP (2 ^ K - 1) hf_le 1 (by decide) (by omega)
  rw [hrec]
  have h1K : 1 + (K - 1) = K := by omega
  rw [h1K]
  simp only [rhoFreezeMin]
  have hnat : 2 ^ (P + 1) + 2 ^ K - 2 = 2 ^ (P + 1) + (2 ^ K - 2) :=
    Nat.add_sub_assoc h2K_ge2 (2 ^ (P + 1))
  rw [hnat, Int.natCast_add]

/-- Headline Theorem 1 (`microbatch_rne_freeze_threshold_exact`):
    Proves the exact worst-case IEEE-754 RNE freeze threshold `ρ_{freeze,min}(P) = 2^{P+1}`
    (`8` E5M2, `16` E4M3, `256` BF16, `2048` FP16) and max non-freeze ratio
    `ρ_{nonfreeze,max}(P) = 2^{P+2} - 2` (`14, 30, 510, 4094`), universal freeze/non-freeze
    characterization, 100% sequential RNE early-spike erasure on `[S, 1, ..., 1]`, and
    pairwise binary-tree RNE preservation of the microbatch signals. -/
theorem microbatch_rne_freeze_threshold_exact :
    (rhoFreezeMin 2 = 8 ∧ rhoFreezeMin 3 = 16 ∧
     rhoFreezeMin 7 = 256 ∧ rhoFreezeMin 10 = 2048) ∧
    (rhoNonfreezeMax 2 = 14 ∧ rhoNonfreezeMax 3 = 30 ∧
     rhoNonfreezeMax 7 = 510 ∧ rhoNonfreezeMax 10 = 4094) ∧
    (∀ (P : Nat), 1 ≤ P →
      (flRNENat P (rhoFreezeMin P + 1) = rhoFreezeMin P) ∧
      (∀ n : Nat, n < rhoFreezeMin P → flRNENat P (n + 1) = n + 1 ∧ flRNENat P (n + 1) ≠ n) ∧
      (flRNENat P (rhoNonfreezeMax P) = rhoNonfreezeMax P ∧
       flRNENat P (rhoNonfreezeMax P + 1) = 2 ^ (P + 2) ∧
       flRNENat P (rhoNonfreezeMax P + 1) ≠ rhoNonfreezeMax P) ∧
      (∀ S : Nat, 2 ^ (P + 2) ≤ S → flRNENat P S = S → flRNENat P (S + 1) = S)) ∧
    (∀ (P K : Nat), 1 ≤ P → 1 ≤ K → K ≤ P + 1 →
      seqRNE P ((rhoFreezeMin P : Int) :: List.replicate (2 ^ K - 1) 1) = (rhoFreezeMin P : Int) ∧
      treeRNE P ((rhoFreezeMin P : Int) :: List.replicate (2 ^ K - 1) 1) =
        (rhoFreezeMin P : Int) + ((2 ^ K - 2 : Nat) : Int) ∧
      treeRNE P (List.replicate (2 ^ K) 1) = ((2 ^ K : Nat) : Int) ∧
      rneAdd P (rhoFreezeMin P : Int) (treeRNE P (List.replicate (2 ^ K) 1)) =
        (rhoFreezeMin P : Int) + ((2 ^ K : Nat) : Int)) := by
  refine ⟨⟨by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide⟩, ?_, ?_⟩
  · intro P hP
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := flRNENat_pow2_add_of_le_half (P := P) (e := P + 1) (m := 1) hP (by omega) (by
        have : P + 1 - P - 1 = 0 := by omega
        rw [this]; decide)
      simpa [rhoFreezeMin] using h
    · intro n hn
      have hle : n + 1 ≤ 2 ^ (P + 1) := by unfold rhoFreezeMin at hn; omega
      have hex := flRNENat_exact_of_le_pow hle
      exact ⟨hex, by omega⟩
    · have hrep : flRNENat P (rhoNonfreezeMax P) = rhoNonfreezeMax P := by
        have heven : rhoNonfreezeMax P = 2 * (2 ^ (P + 1) - 1) := by
          unfold rhoNonfreezeMax
          have : 2 ^ (P + 2) = 2 * 2 ^ (P + 1) := by rw [Nat.pow_succ]; omega
          have := pow2_pos (P + 1)
          omega
        rw [heven]
        have hP2 : 2 ^ P ≤ 2 ^ (P + 1) - 1 := by
          rw [Nat.pow_succ]; have := pow2_pos P; omega
        have hP3 : 2 ^ (P + 1) - 1 < 2 ^ (P + 1) := by
          have := pow2_pos (P + 1); omega
        exact flRNENat_even_in_binade hP2 hP3
      have hinc : flRNENat P (rhoNonfreezeMax P + 1) = 2 ^ (P + 2) := by
        have h1 : rhoNonfreezeMax P + 1 = 2 ^ (P + 2) - 1 := by
          unfold rhoNonfreezeMax
          have h4 : 4 ≤ 2 ^ (P + 2) := by
            have : 2 ^ 2 ≤ 2 ^ (P + 2) := Nat.pow_le_pow_right (by decide) (by omega)
            simpa using this
          omega
        rw [h1]
        exact flRNENat_pow2_sub_of_le_quarter (P := P) (e := P + 2) (m := 1)
          (Nat.le_refl _) (by
            have : P + 2 - P - 2 = 0 := by omega
            rw [this]; decide)
      refine ⟨hrep, hinc, ?_⟩
      rw [hinc]
      unfold rhoNonfreezeMax
      have := pow2_pos (P + 2)
      omega
    · intro S hS hRep
      exact flRNENat_freeze_above_max hS hRep
  · intro P K hP hK1 hK2
    refine ⟨seqRNE_early_spike_freeze hP,
            treeRNE_early_spike_preserves hP hK1 hK2,
            treeRNE_pow2_ones P K, ?_⟩
    rw [treeRNE_pow2_ones]
    unfold rneAdd rhoFreezeMin
    have hsum : ((2 ^ (P + 1) : Nat) : Int) + ((2 ^ K : Nat) : Int) =
        ((2 ^ (P + 1) + 2 ^ K : Nat) : Int) := by omega
    rw [hsum, flRNE_natCast]
    by_cases hKeq : K = P + 1
    · subst hKeq
      have h2 : 2 ^ (P + 1) + 2 ^ (P + 1) = 2 ^ (P + 2) := by
        have hsucc : 2 ^ (P + 2) = 2 ^ (P + 1) * 2 := Nat.pow_succ 2 (P + 1)
        omega
      rw [h2, flRNENat_exact_pow2]
    · have h2K : 2 ^ K = 2 * 2 ^ (K - 1) := by
        have h1 : K = (K - 1) + 1 := by omega
        conv => lhs; rw [h1, Nat.pow_succ]
        omega
      have heven : 2 ^ (P + 1) + 2 ^ K = 2 * (2 ^ P + 2 ^ (K - 1)) := by
        have h1 : 2 ^ (P + 1) = 2 * 2 ^ P := by rw [Nat.pow_succ]; omega
        omega
      rw [heven]
      have hk1 : 2 ^ P ≤ 2 ^ P + 2 ^ (K - 1) := by omega
      have hk2 : 2 ^ P + 2 ^ (K - 1) < 2 ^ (P + 1) := by
        have hlt : 2 ^ (K - 1) < 2 ^ P := Nat.pow_lt_pow_right (by decide) (by omega)
        rw [Nat.pow_succ]; omega
      rw [flRNENat_even_in_binade hk1 hk2]

end KahanNeumaierFp8
