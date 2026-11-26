/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlibiBitsplitKulisch.Defs

/-!
# Pillar 3: Exact Mixed-Format Signed Kulisch Accumulator Widths & FP32 Non-Associativity

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. Single-bit tight signed two's-complement Kulisch accumulator width theorem across all 4 mixed formats
   (`FP4×INT4`, `FP4×INT8`, `INT4×FP8-E4M3`, `FP4×FP8-E4M3` at `K ∈ {32, 128, 4096, 16384}`).
2. Exact associativity, split-merge, reversal, and `List.Perm` permutation invariance of `intSum`,
   alongside an explicit `K = 32` `INT4 × FP8-E4M3` witness where FP32 RNE fails exact associativity.
-/

namespace AlibiBitsplitKulisch

/-! ### Exact `Int` Sum Algebra (`foldl` / `foldr` / `Perm`) -/

theorem foldl_add_shift (xs : List Int) (init : Int) :
    xs.foldl (· + ·) init = init + xs.foldl (· + ·) 0 := by
  induction xs generalizing init with
  | nil =>
    simp [List.foldl]
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (init + x), ih (0 + x)]
    omega

theorem intSum_nil : intSum [] = 0 := rfl

theorem intSum_cons (x : Int) (xs : List Int) : intSum (x :: xs) = x + intSum xs := by
  unfold intSum
  simp only [List.foldl]
  rw [foldl_add_shift]
  omega

theorem intSum_append (xs ys : List Int) : intSum (xs ++ ys) = intSum xs + intSum ys := by
  induction xs with
  | nil =>
    simp [intSum_nil]
  | cons x xs ih =>
    simp only [List.cons_append, intSum_cons, ih]
    omega

theorem intSum_eq_intSumR (xs : List Int) : intSum xs = intSumR xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [intSum_cons, ih]
    rfl

theorem intSum_reverse (xs : List Int) : intSum xs.reverse = intSum xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, intSum_append, ih, intSum_cons, intSum_cons, intSum_nil]
    omega

theorem intSum_perm {xs ys : List Int} (h : List.Perm xs ys) : intSum xs = intSum ys := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    rw [intSum_cons, intSum_cons, ih]
  | swap x y zs =>
    rw [intSum_cons, intSum_cons, intSum_cons, intSum_cons]
    omega
  | trans _ _ ih1 ih2 =>
    exact Eq.trans ih1 ih2

theorem intSum_replicate (K : Nat) (v : Int) :
    intSum (List.replicate K v) = (K : Int) * v := by
  induction K with
  | zero =>
    simp [intSum_nil]
  | succ k ih =>
    rw [List.replicate_succ, intSum_cons, ih]
    have hsucc : ((k + 1 : Nat) : Int) * v = v + (k : Int) * v := by
      have : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [this, Int.add_mul, Int.one_mul]
      omega
    omega

theorem intSum_bounds (Mmax : Nat) (xs : List Int)
    (hbound : ∀ x ∈ xs, -(Mmax : Int) ≤ x ∧ x ≤ (Mmax : Int)) :
    -((xs.length * Mmax : Nat) : Int) ≤ intSum xs ∧
    intSum xs ≤ ((xs.length * Mmax : Nat) : Int) := by
  induction xs with
  | nil =>
    simp [intSum_nil]
  | cons x xs ih =>
    have hx := hbound x (List.mem_cons_self ..)
    have hxs := ih (fun y hy => hbound y (List.mem_cons_of_mem x hy))
    rw [intSum_cons]
    have hlen : (((x :: xs).length * Mmax : Nat) : Int) =
        (Mmax : Int) + ((xs.length * Mmax : Nat) : Int) := by
      simp only [List.length_cons, Nat.succ_mul]
      omega
    omega

/-- Universal single-bit tight signed two's-complement Kulisch accumulator theorem:
    `isExactMinSignedWidth Mmax K W` implies BOTH zero overflow for every `K`-term dot product
    with `|p_i| ≤ Mmax` AND strict overflow at width `W - 1` on the all-`+Mmax` witness. -/
theorem exact_min_signed_width_sound_and_tight {Mmax K W : Nat}
    (hW : isExactMinSignedWidth Mmax K W) :
    (∀ xs : List Int, xs.length ≤ K →
      (∀ x ∈ xs, -(Mmax : Int) ≤ x ∧ x ≤ (Mmax : Int)) →
      fitsSignedWidth W (intSum xs)) ∧
    ¬ fitsSignedWidth (W - 1) (intSum (List.replicate K (Mmax : Int))) := by
  rcases hW with ⟨hW2, hlo, hhi⟩
  constructor
  · intro xs hlen hbound
    have hb := intSum_bounds Mmax xs hbound
    have hmul : xs.length * Mmax ≤ K * Mmax := Nat.mul_le_mul_right Mmax hlen
    have hcomm : K * Mmax = Mmax * K := Nat.mul_comm K Mmax
    unfold fitsSignedWidth
    omega
  · intro hfits
    rw [intSum_replicate] at hfits
    unfold fitsSignedWidth at hfits
    have hsub : W - 1 - 1 = W - 2 := by omega
    rw [hsub] at hfits
    have hcomm : (K : Int) * (Mmax : Int) = ((Mmax * K : Nat) : Int) := by
      have : K * Mmax = Mmax * K := Nat.mul_comm K Mmax
      rw [← Int.natCast_mul, this]
    omega

/-- Headline Theorem 5 (`mixed_format_signed_kulisch_width_exact`):
    Proves the universal single-bit tight signed Kulisch accumulator width theorem, verifies all
    16 exact `(format, K)` bit-widths across `FP4×INT4`, `FP4×INT8`, `INT4×FP8-E4M3`, and
    `FP4×FP8-E4M3` for `K ∈ {32, 128, 4096, 16384}`, proves `INT4×FP8-E4M3` exceeds FP32's
    24-bit mantissa even at `K = 32` (`27 > 24`) and exceeds `int32_t` at `K = 4096` (`34 > 32`),
    and proves `int64_t` holds all 4 formats up to `K = 16384` with `≥ 27` bits of headroom. -/
theorem mixed_format_signed_kulisch_width_exact :
    (∀ (Mmax K W : Nat), isExactMinSignedWidth Mmax K W →
      (∀ xs : List Int, xs.length ≤ K →
        (∀ x ∈ xs, -(Mmax : Int) ≤ x ∧ x ≤ (Mmax : Int)) →
        fitsSignedWidth W (intSum xs)) ∧
      ¬ fitsSignedWidth (W - 1) (intSum (List.replicate K (Mmax : Int)))) ∧
    (isExactMinSignedWidth mMaxFP4xINT4 32 13 ∧
      isExactMinSignedWidth mMaxFP4xINT4 128 15 ∧
      isExactMinSignedWidth mMaxFP4xINT4 4096 20 ∧
      isExactMinSignedWidth mMaxFP4xINT4 16384 22) ∧
    (isExactMinSignedWidth mMaxFP4xINT8 32 17 ∧
      isExactMinSignedWidth mMaxFP4xINT8 128 19 ∧
      isExactMinSignedWidth mMaxFP4xINT8 4096 24 ∧
      isExactMinSignedWidth mMaxFP4xINT8 16384 26) ∧
    (isExactMinSignedWidth mMaxINT4xFP8E4M3 32 27 ∧
      isExactMinSignedWidth mMaxINT4xFP8E4M3 128 29 ∧
      isExactMinSignedWidth mMaxINT4xFP8E4M3 4096 34 ∧
      isExactMinSignedWidth mMaxINT4xFP8E4M3 16384 36 ∧
      (24 : Nat) < 27 ∧ (32 : Nat) < 34) ∧
    (isExactMinSignedWidth mMaxFP4xFP8E4M3 32 28 ∧
      isExactMinSignedWidth mMaxFP4xFP8E4M3 128 30 ∧
      isExactMinSignedWidth mMaxFP4xFP8E4M3 4096 35 ∧
      isExactMinSignedWidth mMaxFP4xFP8E4M3 16384 37 ∧
      (37 : Nat) + 27 = 64) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Mmax K W hW
    exact exact_min_signed_width_sound_and_tight hW
  · unfold isExactMinSignedWidth mMaxFP4xINT4; decide
  · unfold isExactMinSignedWidth mMaxFP4xINT8; decide
  · unfold isExactMinSignedWidth mMaxINT4xFP8E4M3; decide
  · unfold isExactMinSignedWidth mMaxFP4xFP8E4M3; decide

/-! ### FP32 RNE Non-Associativity Witness at `K = 32` (`INT4 × FP8-E4M3`) -/

theorem fp32DriftWitnessK32_mem_bound :
    ∀ x ∈ fp32DriftWitnessK32, x ≤ mMaxINT4xFP8E4M3 := by
  intro x hx
  unfold fp32DriftWitnessK32 at hx
  rw [List.mem_append] at hx
  cases hx with
  | inl h1 =>
    have heq := List.eq_of_mem_replicate h1
    rw [heq]
    unfold mMaxINT4xFP8E4M3; decide
  | inr h2 =>
    have heq := List.eq_of_mem_replicate h2
    rw [heq]
    unfold mMaxINT4xFP8E4M3; decide

theorem nat_log2_eq_of_bounds {n k : Nat} (hlo : 2 ^ k ≤ n) (hhi : n < 2 ^ (k + 1)) :
    Nat.log2 n = k := by
  have hle1 : k ≤ Nat.log2 n := Nat.le_log2 (by omega) |>.mpr hlo
  have hlt2 : Nat.log2 n < k + 1 := Nat.log2_lt (by omega) |>.mpr hhi
  omega

theorem fp32RneNat_of_le (n : Nat) (h : n ≤ 2 ^ 24) : fp32RneNat n = n := by
  unfold fp32RneNat
  simp only [h, ite_true]

theorem fp32RneNat_pow24_add_one : fp32RneNat (2 ^ 24 + 1) = 2 ^ 24 := by
  unfold fp32RneNat
  have hnotle : ¬ (2 ^ 24 + 1 ≤ 2 ^ 24) := by decide
  have hlog : Nat.log2 (2 ^ 24 + 1) = 24 := nat_log2_eq_of_bounds (by decide) (by decide)
  simp only [hnotle, ite_false, hlog]
  decide

theorem fp32RneNat_pow24_add_16 : fp32RneNat (2 ^ 24 + 16) = 2 ^ 24 + 16 := by
  unfold fp32RneNat
  have hnotle : ¬ (2 ^ 24 + 16 ≤ 2 ^ 24) := by decide
  have hlog : Nat.log2 (2 ^ 24 + 16) = 24 := nat_log2_eq_of_bounds (by decide) (by decide)
  simp only [hnotle, ite_false, hlog]
  decide

theorem foldl_fp32_exact_replicate (k init v : Nat) (hbound : init + k * v ≤ 2 ^ 24) :
    (List.replicate k v).foldl fp32RneAddNat init = init + k * v := by
  induction k generalizing init with
  | zero => simp [List.replicate]
  | succ m ih =>
    rw [List.replicate_succ, List.foldl_cons]
    have hstep : fp32RneAddNat init v = init + v := by
      unfold fp32RneAddNat
      apply fp32RneNat_of_le
      have : init + v ≤ init + (m + 1) * v := by
        rw [Nat.succ_mul]; omega
      omega
    rw [hstep, ih (init + v) (by rw [Nat.succ_mul] at hbound; omega)]
    rw [Nat.succ_mul]; omega

theorem foldl_fp32_swamp_ones (k : Nat) :
    (List.replicate k 1).foldl fp32RneAddNat (2 ^ 24) = 2 ^ 24 := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.foldl_cons]
    have hstep : fp32RneAddNat (2 ^ 24) 1 = 2 ^ 24 := fp32RneNat_pow24_add_one
    rw [hstep, ih]

theorem fp32SumNat_witness_fwd : fp32SumNat fp32DriftWitnessK32 = 16777216 := by
  unfold fp32SumNat fp32DriftWitnessK32
  rw [List.foldl_append]
  have h1 : (List.replicate 16 (2 ^ 20)).foldl fp32RneAddNat 0 = 2 ^ 24 := by
    have h := foldl_fp32_exact_replicate 16 0 (2 ^ 20) (by decide)
    simpa using h
  rw [h1, foldl_fp32_swamp_ones]

theorem fp32SumNat_witness_rev : fp32SumNat fp32DriftWitnessK32.reverse = 16777232 := by
  unfold fp32SumNat fp32DriftWitnessK32
  rw [List.reverse_append, List.reverse_replicate, List.reverse_replicate, List.foldl_append]
  have h1 : (List.replicate 16 1).foldl fp32RneAddNat 0 = 16 := by
    have h := foldl_fp32_exact_replicate 16 0 1 (by decide)
    simpa using h
  rw [h1]
  have hsplit : List.replicate 16 (2 ^ 20) = List.replicate 15 (2 ^ 20) ++ [2 ^ 20] := rfl
  rw [hsplit, List.foldl_append]
  have h2 : (List.replicate 15 (2 ^ 20)).foldl fp32RneAddNat 16 = 16 + 15 * 2 ^ 20 :=
    foldl_fp32_exact_replicate 15 16 (2 ^ 20) (by decide)
  rw [h2, List.foldl_cons, List.foldl_nil]
  unfold fp32RneAddNat
  have heq : 16 + 15 * 2 ^ 20 + 2 ^ 20 = 2 ^ 24 + 16 := by decide
  rw [heq, fp32RneNat_pow24_add_16]

/-- Headline Theorem 6 (`kulisch_int64_exact_associativity_vs_fp32_drift`):
    Proves exact associativity, split-merge, reversal, and `List.Perm` permutation invariance
    of exact Kulisch `Int` accumulation (`0` order diffs), alongside the explicit `K = 32`
    `INT4 × FP8-E4M3` witness (`16` terms of `2^{20}` and `16` terms of `1` in units of `2^{-9}`)
    where `int64_t` Kulisch yields `16777232` in both orders while IEEE-754 FP32 RNE yields
    `16777216` forward vs `16777232` reversed. -/
theorem kulisch_int64_exact_associativity_vs_fp32_drift :
    (∀ xs ys : List Int, intSum (xs ++ ys) = intSum xs + intSum ys) ∧
    (∀ xs ys zs : List Int, intSum ((xs ++ ys) ++ zs) = intSum (xs ++ (ys ++ zs))) ∧
    (∀ xs : List Int, intSum xs = intSumR xs) ∧
    (∀ xs : List Int, intSum xs.reverse = intSum xs) ∧
    (∀ xs ys : List Int, List.Perm xs ys → intSum xs = intSum ys) ∧
    (fp32DriftWitnessK32.length = 32 ∧
      (∀ x ∈ fp32DriftWitnessK32, x ≤ mMaxINT4xFP8E4M3) ∧
      intSum (fp32DriftWitnessK32.map Int.ofNat) = 16777232 ∧
      intSum (fp32DriftWitnessK32.reverse.map Int.ofNat) = 16777232 ∧
      fitsSignedWidth 64 (intSum (fp32DriftWitnessK32.map Int.ofNat)) ∧
      fp32SumNat fp32DriftWitnessK32 = 16777216 ∧
      fp32SumNat fp32DriftWitnessK32.reverse = 16777232 ∧
      fp32SumNat fp32DriftWitnessK32 ≠ fp32SumNat fp32DriftWitnessK32.reverse) := by
  refine ⟨intSum_append, ?_, intSum_eq_intSumR, intSum_reverse, fun _ _ h => intSum_perm h, ?_⟩
  · intro xs ys zs
    rw [List.append_assoc]
  · refine ⟨?_, fp32DriftWitnessK32_mem_bound, ?_, ?_, ?_, fp32SumNat_witness_fwd,
        fp32SumNat_witness_rev, ?_⟩
    · rfl
    · decide
    · decide
    · unfold fitsSignedWidth; decide
    · rw [fp32SumNat_witness_fwd, fp32SumNat_witness_rev]; decide

end AlibiBitsplitKulisch
