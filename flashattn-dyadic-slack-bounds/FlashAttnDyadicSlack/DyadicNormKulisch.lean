/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FlashAttnDyadicSlack.Defs
import FlashAttnDyadicSlack.DyadicRescale

/-!
# Dyadic Exponent Normalization & Signed `int32` Kulisch Tile Accumulator

Pure-`Init` (zero Mathlib) proofs of:
5. `dyadic_exponent_normalization_cancels_identically`: scaling `(O, l)` by exact `2^-1`
   whenever `l >= 2^14 = 16384` incurs zero mantissa rounding error in normal `FP16`, keeps
   `0 <= l < 2^14` (and intermediate `l' < 2^15 < 65504`) unconditionally for arbitrary
   sequence length `L` (including `L = 131072` and `L = 10^9`), and cancels identically in
   the final ratio `(2^-k O) / (2^-k l) = O / l` with zero division/reconstruction cost.
6. `flash_tile_int32_kulisch_associativity_and_exactness`: exact signed `int32` (`Q8.20`)
   Kulisch accumulator width, zero-overflow bound for `64`-element `FP8-E4M3` and
   `UE3M1_PROB` `P * V` tiles, exact rational correspondence (zero rounding drift), and
   unconditional associativity, split-merge, and `List.Perm` permutation invariance.
-/

namespace FlashAttnDyadicSlack

/-! ### Theorem 5: Dyadic Exponent Normalization (`|l| >= 2^14`) -/

theorem rat_div_cancel_pow2 (O l : Rat) (hl : l ≠ 0) (k : Nat) :
    (O * invPow2Rat k) / (l * invPow2Rat k) = O / l := by
  have hden : l * invPow2Rat k ≠ 0 := by
    intro h
    have h1 : (l * invPow2Rat k) * pow2Rat k = 0 := by rw [h, Rat.zero_mul]
    rw [Rat.mul_assoc, invPow2Rat_mul_pow2Rat, Rat.mul_one] at h1
    exact hl h1
  apply rat_mul_right_cancel hden
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel (l * invPow2Rat k) hden, Rat.mul_one]
  rw [Rat.div_def]
  calc
    O * invPow2Rat k
        = (O * (l⁻¹ * l)) * invPow2Rat k := by
          rw [Rat.inv_mul_cancel l hl, Rat.mul_one]
    _ = O * l⁻¹ * (l * invPow2Rat k) := by grind

theorem invPow2Rat_le_one (k : Nat) : invPow2Rat k ≤ (1 : Rat) := by
  have h1 : (1 : Rat) ≤ pow2Rat k := rat_natCast_le (Nat.two_pow_pos k)
  have h2 := rat_mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (invPow2Rat_pos k))
  rw [Rat.mul_one, invPow2Rat_mul_pow2Rat] at h2
  exact h2

theorem invPow2Rat_succ (k : Nat) : invPow2Rat (k + 1) = invPow2Rat k / 2 := by
  rw [invPow2Rat_add]
  have hhalf : invPow2Rat 1 = (1 : Rat) / 2 := by
    unfold invPow2Rat pow2Rat
    simp
  rw [hhalf, Rat.div_def, Rat.div_def, Rat.one_mul]

theorem dyadicNormStep_invariant
    (O l exactO exactL w v : Rat) (k : Nat)
    (hl0 : (0 : Rat) ≤ l) (hl_lt : l < fp16NormThreshold)
    (hO : O = exactO * invPow2Rat k) (hL : l = exactL * invPow2Rat k)
    (hw0 : (0 : Rat) ≤ w) (hw_le : w ≤ fp16NormThreshold) :
    let (O1, l1, k1) := dyadicNormStep (O, l, k) (w, v)
    (0 : Rat) ≤ l1 ∧
    l1 < fp16NormThreshold ∧
    l + w * invPow2Rat k < (32768 : Rat) ∧
    O1 = (exactO + w * v) * invPow2Rat k1 ∧
    l1 = (exactL + w) * invPow2Rat k1 := by
  unfold dyadicNormStep
  dsimp only
  have hsc_pos : (0 : Rat) < invPow2Rat k := invPow2Rat_pos k
  have hsc_le1 : invPow2Rat k ≤ 1 := invPow2Rat_le_one k
  have hwsc0 : (0 : Rat) ≤ w * invPow2Rat k :=
    Rat.mul_nonneg hw0 (Rat.le_of_lt hsc_pos)
  have hwsc_le : w * invPow2Rat k ≤ fp16NormThreshold := by
    have h1 := rat_mul_le_mul_of_nonneg_left hsc_le1 hw0
    rw [Rat.mul_one] at h1
    exact Rat.le_trans h1 hw_le
  have hmid0 : (0 : Rat) ≤ l + w * invPow2Rat k := by
    have h1 := (Rat.add_le_add_right (c := w * invPow2Rat k)).mpr hl0
    rw [Rat.zero_add] at h1
    exact Rat.le_trans hwsc0 h1
  have hmid_lt : l + w * invPow2Rat k < (32768 : Rat) := by
    unfold fp16NormThreshold at hl_lt hwsc_le
    have h1 : l + w * invPow2Rat k < (16384 : Rat) + w * invPow2Rat k :=
      (Rat.add_lt_add_right (c := w * invPow2Rat k)).mpr hl_lt
    have h2 : (16384 : Rat) + w * invPow2Rat k ≤ (16384 : Rat) + (16384 : Rat) := by
      rw [Rat.add_comm (16384 : Rat) _, Rat.add_comm (16384 : Rat) _]
      exact (Rat.add_le_add_right (c := (16384 : Rat))).mpr hwsc_le
    have h3 : (16384 : Rat) + (16384 : Rat) = (32768 : Rat) := by grind
    rw [h3] at h2
    exact rat_lt_of_lt_of_le h1 h2
  have hO' : O + w * invPow2Rat k * v = (exactO + w * v) * invPow2Rat k := by
    rw [hO]
    grind
  have hL' : l + w * invPow2Rat k = (exactL + w) * invPow2Rat k := by
    rw [hL]
    grind
  split
  · rename_i hlt
    exact ⟨hmid0, hlt, hmid_lt, hO', hL'⟩
  · rename_i hge
    have hdiv0 : (0 : Rat) ≤ (l + w * invPow2Rat k) / 2 :=
      rat_div_nonneg hmid0 (by decide : (0 : Rat) < 2)
    have hdiv_lt : (l + w * invPow2Rat k) / 2 < fp16NormThreshold := by
      unfold fp16NormThreshold
      have h2pos : (0 : Rat) < 2 := by decide
      have hmul : (l + w * invPow2Rat k) / 2 * 2 = l + w * invPow2Rat k := by
        rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel (2 : Rat) (by decide), Rat.mul_one]
      have htarget : (16384 : Rat) * 2 = 32768 := by grind
      have hstep : (l + w * invPow2Rat k) / 2 * 2 < (16384 : Rat) * 2 := by
        rw [hmul, htarget]
        exact hmid_lt
      exact rat_lt_of_mul_lt_mul_right h2pos hstep
    have hO1 : (O + w * invPow2Rat k * v) / 2 = (exactO + w * v) * invPow2Rat (k + 1) := by
      rw [hO', invPow2Rat_succ, Rat.div_def, Rat.div_def, Rat.mul_assoc]
    have hL1 : (l + w * invPow2Rat k) / 2 = (exactL + w) * invPow2Rat (k + 1) := by
      rw [hL', invPow2Rat_succ, Rat.div_def, Rat.div_def, Rat.mul_assoc]
    exact ⟨hdiv0, hdiv_lt, hmid_lt, hO1, hL1⟩

theorem dyadicNormFold_invariant (xs : List (Rat × Rat))
    (hxs : ∀ wv ∈ xs, (0 : Rat) ≤ wv.1 ∧ wv.1 ≤ fp16NormThreshold) :
    ∀ (O l exactO exactL : Rat) (k : Nat),
      (0 : Rat) ≤ l → l < fp16NormThreshold →
      O = exactO * invPow2Rat k → l = exactL * invPow2Rat k →
      let (O1, l1, k1) := xs.foldl dyadicNormStep (O, l, k)
      (0 : Rat) ≤ l1 ∧
      l1 < fp16NormThreshold ∧
      O1 = (xs.foldl (fun acc wv => acc + wv.1 * wv.2) exactO) * invPow2Rat k1 ∧
      l1 = (xs.foldl (fun acc wv => acc + wv.1) exactL) * invPow2Rat k1 := by
  induction xs with
  | nil =>
    intro O l exactO exactL k hl0 hl_lt hO hL
    exact ⟨hl0, hl_lt, hO, hL⟩
  | cons hd tl ih =>
    intro O l exactO exactL k hl0 hl_lt hO hL
    have hhd : (0 : Rat) ≤ hd.1 ∧ hd.1 ≤ fp16NormThreshold :=
      hxs hd (List.mem_cons_self ..)
    have htl : ∀ wv ∈ tl, (0 : Rat) ≤ wv.1 ∧ wv.1 ≤ fp16NormThreshold :=
      fun wv hwv => hxs wv (List.mem_cons_of_mem hd hwv)
    simp only [List.foldl_cons]
    have hstep := dyadicNormStep_invariant O l exactO exactL hd.1 hd.2 k hl0 hl_lt hO hL hhd.1 hhd.2
    rcases heq : dyadicNormStep (O, l, k) hd with ⟨O', l', k'⟩
    rw [heq] at hstep
    dsimp only at hstep
    exact ih htl O' l' (exactO + hd.1 * hd.2) (exactL + hd.1) k' hstep.1 hstep.2.1 hstep.2.2.2.1 hstep.2.2.2.2

/-- Headline Theorem 5 (`dyadic_exponent_normalization_cancels_identically`). -/
theorem dyadic_exponent_normalization_cancels_identically :
    (∀ (x : NormalFloat 10), (-13 : Int) ≤ x.exp →
      (-14 : Int) ≤ (x.scaleNegPow2 1).exp ∧
      (x.scaleNegPow2 1).neg = x.neg ∧
      (x.scaleNegPow2 1).mant = x.mant ∧
      (x.scaleNegPow2 1).toRat = x.toRat * invPow2Rat 1) ∧
    (∀ (O l : Rat) (k : Nat), l ≠ 0 →
      (O * invPow2Rat k) / (l * invPow2Rat k) = O / l) ∧
    (∀ (p k : Nat) (xO xl : NormalFloat p), xl.toRat ≠ 0 →
      (xO.scaleNegPow2 k).toRat / (xl.scaleNegPow2 k).toRat = xO.toRat / xl.toRat) ∧
    (∀ (xs : List (Rat × Rat)),
      (∀ wv ∈ xs, (0 : Rat) ≤ wv.1 ∧ wv.1 ≤ fp16NormThreshold) →
      let (O, l, k) := dyadicNormRun xs
      (0 : Rat) ≤ l ∧
      l < fp16NormThreshold ∧
      l < (fp16MaxNormal : Rat) ∧
      O = exactAttentionO xs * invPow2Rat k ∧
      l = exactAttentionL xs * invPow2Rat k ∧
      (exactAttentionL xs ≠ 0 → O / l = exactAttentionO xs / exactAttentionL xs)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hexp
    refine ⟨?_, rfl, rfl, scaleNegPow2_toRat x 1⟩
    unfold NormalFloat.scaleNegPow2
    dsimp only
    omega
  · intro O l k hl
    exact rat_div_cancel_pow2 O l hl k
  · intro p k xO xl hxl
    rw [scaleNegPow2_toRat, scaleNegPow2_toRat]
    exact rat_div_cancel_pow2 xO.toRat xl.toRat hxl k
  · intro xs hxs
    unfold dyadicNormRun exactAttentionO exactAttentionL
    have h0 : (0 : Rat) ≤ 0 := by decide
    have hlt0 : (0 : Rat) < fp16NormThreshold := by unfold fp16NormThreshold; decide
    have hO0 : (0 : Rat) = (0 : Rat) * invPow2Rat 0 := by
      unfold invPow2Rat pow2Rat; simp
    have hinv := dyadicNormFold_invariant xs hxs 0 0 0 0 0 h0 hlt0 hO0 hO0
    rcases heq : xs.foldl dyadicNormStep (0, 0, 0) with ⟨O, l, k⟩
    rw [heq] at hinv
    dsimp only at hinv ⊢
    have hltMax : l < (fp16MaxNormal : Rat) := by
      have h1 : fp16NormThreshold < (fp16MaxNormal : Rat) := by
        unfold fp16NormThreshold fp16MaxNormal
        decide
      exact rat_lt_trans hinv.2.1 h1
    refine ⟨hinv.1, hinv.2.1, hltMax, hinv.2.2.1, hinv.2.2.2, ?_⟩
    intro hlne
    rw [hinv.2.2.1, hinv.2.2.2]
    exact rat_div_cancel_pow2 _ _ hlne k

/-! ### Theorem 6: Signed `int32` (`Q8.20`) Kulisch Tile Accumulator -/

theorem kulischSum_append (xs ys : List Int) :
    kulischSum (xs ++ ys) = kulischSum xs + kulischSum ys := by
  induction xs with
  | nil => simp [kulischSum]
  | cons x xs ih =>
    simp only [List.cons_append, kulischSum, ih]
    omega

theorem kulischFoldl_eq (xs : List Int) :
    ∀ acc : Int, xs.foldl (· + ·) acc = acc + kulischSum xs := by
  induction xs with
  | nil =>
    intro acc
    simp [kulischSum]
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, kulischSum]
    rw [ih]
    omega

theorem kulischFoldl_eq_kulischSum (xs : List Int) :
    kulischFoldl xs = kulischSum xs := by
  unfold kulischFoldl
  rw [kulischFoldl_eq, Int.zero_add]

theorem kulischSum_reverse (xs : List Int) :
    kulischSum xs.reverse = kulischSum xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons, kulischSum_append, kulischSum, ih]
    omega

theorem kulischSum_perm {xs ys : List Int} (h : xs.Perm ys) :
    kulischSum xs = kulischSum ys := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp only [kulischSum, ih]
  | swap x y l =>
    simp only [kulischSum]
    omega
  | trans _ _ ih1 ih2 =>
    exact Eq.trans ih1 ih2

theorem kulischSum_bound (xs : List Int) (M : Int) (_hM : 0 ≤ M)
    (hxs : ∀ x ∈ xs, -M ≤ x ∧ x ≤ M) :
    -(xs.length : Int) * M ≤ kulischSum xs ∧ kulischSum xs ≤ (xs.length : Int) * M := by
  induction xs with
  | nil =>
    simp [kulischSum]
  | cons x xs ih =>
    have hx := hxs x (List.mem_cons_self ..)
    have htl := ih (fun y hy => hxs y (List.mem_cons_of_mem x hy))
    simp only [kulischSum, List.length_cons]
    have hlen : ((xs.length + 1 : Nat) : Int) = (xs.length : Int) + 1 := by omega
    rw [hlen]
    constructor <;> grind

theorem kulischSum_toRat_exact (xs : List Int) :
    (kulischSum xs : Rat) / (kulischScale : Rat) =
      ratSum (xs.map (fun (t : Int) => (t : Rat) / (kulischScale : Rat))) := by
  induction xs with
  | nil =>
    simp only [kulischSum, List.map_nil, ratSum]
    change (0 : Rat) / (kulischScale : Rat) = 0
    rw [Rat.div_def, Rat.zero_mul]
  | cons x xs ih =>
    simp only [kulischSum, List.map_cons, ratSum, ← ih]
    have hadd : (((x + kulischSum xs : Int) : Rat)) = (x : Rat) + (kulischSum xs : Rat) :=
      Rat.intCast_add x (kulischSum xs)
    rw [hadd, Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]

theorem fp8ProdToQ20_exact (pInt vInt : Int) :
    ((fp8ProdToQ20 pInt vInt : Int) : Rat) / (kulischScale : Rat) =
      ((pInt : Rat) / pow2Rat 9) * ((vInt : Rat) / pow2Rat 9) := by
  unfold fp8ProdToQ20 kulischScale pow2Rat
  have hcast : ((pInt * vInt * 4 : Int) : Rat) = (pInt : Rat) * (vInt : Rat) * (4 : Rat) := by
    rw [Rat.intCast_mul, Rat.intCast_mul]
    rfl
  rw [hcast]
  have h1 : (((2 ^ 20 : Nat) : Rat)) = (4 : Rat) * (((2 ^ 9 : Nat) : Rat) * ((2 ^ 9 : Nat) : Rat)) := by
    simp; grind
  have h20 : (((2 ^ 20 : Nat) : Rat)) ≠ 0 := pow2Rat_ne_zero 20
  have h9 : (((2 ^ 9 : Nat) : Rat)) ≠ 0 := pow2Rat_ne_zero 9
  apply rat_mul_right_cancel h20
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ h20, Rat.mul_one]
  rw [h1, Rat.div_def, Rat.div_def]
  calc
    (pInt : Rat) * (vInt : Rat) * 4
        = (pInt : Rat) * (((2 ^ 9 : Nat) : Rat)⁻¹ * ((2 ^ 9 : Nat) : Rat)) *
          ((vInt : Rat) * (((2 ^ 9 : Nat) : Rat)⁻¹ * ((2 ^ 9 : Nat) : Rat))) * 4 := by
          rw [Rat.inv_mul_cancel _ h9, Rat.mul_one, Rat.mul_one]
    _ = (pInt : Rat) * ((2 ^ 9 : Nat) : Rat)⁻¹ * ((vInt : Rat) * ((2 ^ 9 : Nat) : Rat)⁻¹) *
        (4 * (((2 ^ 9 : Nat) : Rat) * ((2 ^ 9 : Nat) : Rat))) := by grind

theorem ue3m1ProdToQ20_exact (pInt vInt : Int) :
    ((ue3m1ProdToQ20 pInt vInt : Int) : Rat) / (kulischScale : Rat) =
      ((pInt : Rat) / pow2Rat 7) * ((vInt : Rat) / pow2Rat 9) := by
  unfold ue3m1ProdToQ20 kulischScale pow2Rat
  have hcast : ((pInt * vInt * 16 : Int) : Rat) = (pInt : Rat) * (vInt : Rat) * (16 : Rat) := by
    rw [Rat.intCast_mul, Rat.intCast_mul]
    rfl
  rw [hcast]
  have h1 : (((2 ^ 20 : Nat) : Rat)) = (16 : Rat) * (((2 ^ 7 : Nat) : Rat) * ((2 ^ 9 : Nat) : Rat)) := by
    simp; grind
  have h20 : (((2 ^ 20 : Nat) : Rat)) ≠ 0 := pow2Rat_ne_zero 20
  have h7 : (((2 ^ 7 : Nat) : Rat)) ≠ 0 := pow2Rat_ne_zero 7
  have h9 : (((2 ^ 9 : Nat) : Rat)) ≠ 0 := pow2Rat_ne_zero 9
  apply rat_mul_right_cancel h20
  rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ h20, Rat.mul_one]
  rw [h1, Rat.div_def, Rat.div_def]
  calc
    (pInt : Rat) * (vInt : Rat) * 16
        = (pInt : Rat) * (((2 ^ 7 : Nat) : Rat)⁻¹ * ((2 ^ 7 : Nat) : Rat)) *
          ((vInt : Rat) * (((2 ^ 9 : Nat) : Rat)⁻¹ * ((2 ^ 9 : Nat) : Rat))) * 16 := by
          rw [Rat.inv_mul_cancel _ h7, Rat.inv_mul_cancel _ h9, Rat.mul_one, Rat.mul_one]
    _ = (pInt : Rat) * ((2 ^ 7 : Nat) : Rat)⁻¹ * ((vInt : Rat) * ((2 ^ 9 : Nat) : Rat)⁻¹) *
        (16 * (((2 ^ 7 : Nat) : Rat) * ((2 ^ 9 : Nat) : Rat))) := by grind

/-- Headline Theorem 6 (`flash_tile_int32_kulisch_associativity_and_exactness`). -/
theorem flash_tile_int32_kulisch_associativity_and_exactness :
    (∀ (pInt vInt : Int),
      ((fp8ProdToQ20 pInt vInt : Int) : Rat) / (kulischScale : Rat) =
        ((pInt : Rat) / pow2Rat 9) * ((vInt : Rat) / pow2Rat 9) ∧
      ((ue3m1ProdToQ20 pInt vInt : Int) : Rat) / (kulischScale : Rat) =
        ((pInt : Rat) / pow2Rat 7) * ((vInt : Rat) / pow2Rat 9)) ∧
    (∀ (xs : List Int) (M : Int),
      xs.length ≤ tileWidthBc → 0 ≤ M → (tileWidthBc : Int) * M ≤ int32Max →
      (∀ x ∈ xs, -M ≤ x ∧ x ≤ M) →
      inInt32Range (kulischSum xs)) ∧
    (∀ (xs : List Int),
      xs.length ≤ tileWidthBc →
      (∀ x ∈ xs, -(4 * (kulischScale : Int)) ≤ x ∧ x ≤ 4 * (kulischScale : Int)) →
      inInt32Range (kulischSum xs) ∧
      -(2 ^ 28 : Int) ≤ kulischSum xs ∧ kulischSum xs ≤ (2 ^ 28 : Int)) ∧
    (∀ (xs : List Int),
      (kulischSum xs : Rat) / (kulischScale : Rat) =
        ratSum (xs.map (fun (t : Int) => (t : Rat) / (kulischScale : Rat))) ∧
      kulischFoldl xs = kulischSum xs) ∧
    (∀ (xs ys : List Int),
      kulischSum (xs ++ ys) = kulischSum xs + kulischSum ys ∧
      kulischSum xs.reverse = kulischSum xs ∧
      (xs.Perm ys → kulischSum xs = kulischSum ys)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro pInt vInt
    exact ⟨fp8ProdToQ20_exact pInt vInt, ue3m1ProdToQ20_exact pInt vInt⟩
  · intro xs M hlen hM hbound hxs
    have hb := kulischSum_bound xs M hM hxs
    have hlen_le : (xs.length : Int) ≤ (tileWidthBc : Int) := Int.ofNat_le.mpr hlen
    have hmul : (xs.length : Int) * M ≤ (tileWidthBc : Int) * M :=
      Int.mul_le_mul_of_nonneg_right hlen_le hM
    have hneg : -(xs.length : Int) * M = -((xs.length : Int) * M) := Int.neg_mul ..
    rw [hneg] at hb
    unfold inInt32Range int32Min
    unfold int32Max at hbound ⊢
    constructor <;> omega
  · intro xs hlen hxs
    have hM : (0 : Int) ≤ 4 * (kulischScale : Int) := by
      unfold kulischScale; decide
    have hb := kulischSum_bound xs (4 * (kulischScale : Int)) hM hxs
    have hlen_le : (xs.length : Int) ≤ (tileWidthBc : Int) := Int.ofNat_le.mpr hlen
    have hmul : (xs.length : Int) * (4 * (kulischScale : Int)) ≤
        (tileWidthBc : Int) * (4 * (kulischScale : Int)) :=
      Int.mul_le_mul_of_nonneg_right hlen_le hM
    have hneg : -(xs.length : Int) * (4 * (kulischScale : Int)) =
        -((xs.length : Int) * (4 * (kulischScale : Int))) := Int.neg_mul ..
    rw [hneg] at hb
    have h28 : (tileWidthBc : Int) * (4 * (kulischScale : Int)) = (2 ^ 28 : Int) := by
      unfold tileWidthBc kulischScale; decide
    have hmin : int32Min = -(2 ^ 31 : Int) := by unfold int32Min; decide
    have hmax : int32Max = (2 ^ 31 : Int) - 1 := by unfold int32Max; decide
    unfold inInt32Range
    rw [h28] at hmul
    rw [hmin, hmax]
    constructor
    · constructor <;> omega
    · constructor <;> omega
  · intro xs
    exact ⟨kulischSum_toRat_exact xs, kulischFoldl_eq_kulischSum xs⟩
  · intro xs ys
    exact ⟨kulischSum_append xs ys, kulischSum_reverse xs, kulischSum_perm⟩

end FlashAttnDyadicSlack
