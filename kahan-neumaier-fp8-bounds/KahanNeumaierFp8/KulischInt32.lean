/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KahanNeumaierFp8.RneFreeze

/-!
# Exact Signed Kulisch Bit-Width Law & OCP FP8-E4M3FN Kulisch-in-INT32 (`M ≤ 9,362`)

Proves Theorem 4 (`fp8_e4m3fn_kulisch_int32_9362_exact`).
-/

namespace KahanNeumaierFp8

theorem le_pow_ceilLog2 {M : Nat} (_hM : 1 ≤ M) : M ≤ 2 ^ ceilLog2 M := by
  unfold ceilLog2
  split
  · omega
  · rename_i hgt
    have hnz : M - 1 ≠ 0 := by omega
    have hlt : M - 1 < 2 ^ (Nat.log2 (M - 1) + 1) :=
      (Nat.log2_lt hnz).mp (Nat.lt_succ_self _)
    omega

theorem seqIntSum_nil : seqIntSum [] = 0 := rfl

theorem seqIntSum_cons (a : Int) (xs : List Int) :
    seqIntSum (a :: xs) = a + seqIntSum xs := by
  unfold seqIntSum
  have hgen : ∀ (acc : Int) (ys : List Int), ys.foldl (· + ·) acc = acc + ys.foldl (· + ·) 0 := by
    intro acc ys
    induction ys generalizing acc with
    | nil => simp
    | cons y ys ih =>
      simp only [List.foldl_cons, Int.zero_add]
      rw [ih (acc + y), ih y]
      omega
  simpa using hgen a xs

theorem seqIntSum_append (xs ys : List Int) :
    seqIntSum (xs ++ ys) = seqIntSum xs + seqIntSum ys := by
  induction xs with
  | nil => simp [seqIntSum]
  | cons x xs ih =>
    rw [List.cons_append, seqIntSum_cons, seqIntSum_cons, ih]
    omega

theorem seqIntSum_perm {xs ys : List Int} (h : List.Perm xs ys) :
    seqIntSum xs = seqIntSum ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [seqIntSum_cons, seqIntSum_cons, ih]
  | swap x y l =>
    rw [seqIntSum_cons, seqIntSum_cons, seqIntSum_cons, seqIntSum_cons]
    omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem seqIntSum_replicate (n : Nat) (a : Int) :
    seqIntSum (List.replicate n a) = (n : Int) * a := by
  induction n with
  | zero => simp [seqIntSum]
  | succ n ih =>
    rw [List.replicate_succ, seqIntSum_cons, ih]
    have : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
    rw [this, Int.add_mul, Int.one_mul]
    omega

theorem seqIntSum_natAbs_le {xs : List Int} {B : Nat}
    (h : ∀ x ∈ xs, x.natAbs ≤ B) :
    (seqIntSum xs).natAbs ≤ xs.length * B := by
  induction xs with
  | nil => simp [seqIntSum]
  | cons x xs ih =>
    rw [seqIntSum_cons, List.length_cons]
    have hx : x.natAbs ≤ B := h x (by simp)
    have hxs : (seqIntSum xs).natAbs ≤ xs.length * B :=
      ih (fun y hy => h y (by simp [hy]))
    have htri : (x + seqIntSum xs).natAbs ≤ x.natAbs + (seqIntSum xs).natAbs :=
      Int.natAbs_add_le x (seqIntSum xs)
    have hmul : (xs.length + 1) * B = xs.length * B + B := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

theorem kulisch_width_overflow_free {M P deltaE : Nat} (hM : 1 ≤ M)
    (xs : List Int) (hlen : xs.length ≤ M)
    (hbound : ∀ x ∈ xs, x.natAbs ≤ (2 ^ (P + 1) - 1) * 2 ^ deltaE) :
    (seqIntSum xs).natAbs < 2 ^ (kulischMinBits M P deltaE - 1) := by
  have h1 : (seqIntSum xs).natAbs ≤ xs.length * ((2 ^ (P + 1) - 1) * 2 ^ deltaE) :=
    seqIntSum_natAbs_le hbound
  have h2 : xs.length * ((2 ^ (P + 1) - 1) * 2 ^ deltaE) ≤
      M * ((2 ^ (P + 1) - 1) * 2 ^ deltaE) :=
    Nat.mul_le_mul_right _ hlen
  have hMpow : M ≤ 2 ^ ceilLog2 M := le_pow_ceilLog2 hM
  have h3 : M * ((2 ^ (P + 1) - 1) * 2 ^ deltaE) ≤
      2 ^ ceilLog2 M * ((2 ^ (P + 1) - 1) * 2 ^ deltaE) :=
    Nat.mul_le_mul_right _ hMpow
  have hposC : 0 < 2 ^ ceilLog2 M := pow2_pos (ceilLog2 M)
  have hposD : 0 < 2 ^ deltaE := pow2_pos deltaE
  have hposP : 0 < 2 ^ (P + 1) := pow2_pos (P + 1)
  have hstrict : (2 ^ (P + 1) - 1) * 2 ^ deltaE < 2 ^ (P + 1) * 2 ^ deltaE :=
    Nat.mul_lt_mul_of_pos_right (by omega) hposD
  have h4 : 2 ^ ceilLog2 M * ((2 ^ (P + 1) - 1) * 2 ^ deltaE) <
      2 ^ ceilLog2 M * (2 ^ (P + 1) * 2 ^ deltaE) :=
    Nat.mul_lt_mul_of_pos_left hstrict hposC
  have hexp : 2 ^ ceilLog2 M * (2 ^ (P + 1) * 2 ^ deltaE) =
      2 ^ (kulischMinBits M P deltaE - 1) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    unfold kulischMinBits
    omega
  omega

theorem fp8_e4m3fn_mag_le_max (x : Fp8E4M3FN) : x.magUnits ≤ e4m3MaxUnits := by
  unfold Fp8E4M3FN.magUnits e4m3MaxUnits
  have hE := x.hExp
  have hM := x.hMant
  have hN := x.hNotNaN
  by_cases h0 : x.exp = 0
  · simp only [h0, ↓reduceIte]; omega
  · simp only [h0, ↓reduceIte]
    by_cases h15 : x.exp = 15
    · have hm6 : x.mant ≤ 6 := by omega
      rw [h15]
      have hpow : 2 ^ (15 - 1) = 16384 := by decide
      rw [hpow]
      omega
    · have he14 : x.exp - 1 ≤ 13 := by omega
      have hpow : 2 ^ (x.exp - 1) ≤ 2 ^ 13 := Nat.pow_le_pow_right (by decide) he14
      have h13 : 2 ^ 13 = 8192 := by decide
      rw [h13] at hpow
      have hmul : (8 + x.mant) * 2 ^ (x.exp - 1) ≤ 15 * 8192 :=
        Nat.mul_le_mul (by omega) hpow
      omega

theorem fp8_e4m3fn_toUnits_natAbs_le (x : Fp8E4M3FN) :
    x.toUnits.natAbs ≤ e4m3MaxUnits := by
  unfold Fp8E4M3FN.toUnits
  split
  · simpa using fp8_e4m3fn_mag_le_max x
  · simpa using fp8_e4m3fn_mag_le_max x

theorem int32_foldl_eq_ofInt_seqIntSum (xs : List Int) :
    (xs.map Int32.ofInt).foldl (· + ·) (0 : Int32) = Int32.ofInt (seqIntSum xs) := by
  have hgen : ∀ (acc : Int) (ys : List Int),
      (ys.map Int32.ofInt).foldl (· + ·) (Int32.ofInt acc) =
        Int32.ofInt (ys.foldl (· + ·) acc) := by
    intro acc ys
    induction ys generalizing acc with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hadd : Int32.ofInt acc + Int32.ofInt y = Int32.ofInt (acc + y) := by
        rw [Int32.ofInt_add]
      rw [hadd]
      exact ih (acc + y)
  simpa [seqIntSum] using hgen 0 xs

theorem int32_toInt_ofInt_exact {x : Int} (hlo : int32Min ≤ x) (hhi : x ≤ int32Max) :
    (Int32.ofInt x).toInt = x := by
  rw [Int32.toInt_ofInt]
  unfold int32Min at hlo
  unfold int32Max at hhi
  unfold Int.bmod Int32.size
  dsimp only
  split <;> omega

theorem rat_foldl_fp8_eq_units (xs : List Fp8E4M3FN) :
    (xs.map Fp8E4M3FN.toRat).foldl (· + ·) (0 : Rat) =
      ((seqIntSum (xs.map Fp8E4M3FN.toUnits) : Rat) / (512 : Rat)) := by
  have hgen : ∀ (acc : Int) (ys : List Fp8E4M3FN),
      (ys.map Fp8E4M3FN.toRat).foldl (· + ·) ((acc : Rat) / (512 : Rat)) =
        ((((ys.map Fp8E4M3FN.toUnits).foldl (· + ·) acc : Int) : Rat) / (512 : Rat)) := by
    intro acc ys
    induction ys generalizing acc with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_cons, List.foldl_cons, Fp8E4M3FN.toRat]
      have hdiv : (acc : Rat) / (512 : Rat) + (y.toUnits : Rat) / (512 : Rat) =
          (((acc + y.toUnits : Int) : Rat) / (512 : Rat)) := by
        rw [Rat.intCast_add]
        grind
      rw [hdiv]
      exact ih (acc + y.toUnits)
  have h0 : ((0 : Int) : Rat) / (512 : Rat) = (0 : Rat) := by grind
  have h := hgen 0 xs
  rw [h0] at h
  exact h

/-- Headline Theorem 4 (`fp8_e4m3fn_kulisch_int32_9362_exact`):
    Exact signed Kulisch width law and 100% bit-exact, zero-overflow, unconditionally
    associative & permutation-invariant OCP `FP8-E4M3FN` accumulation in `int32_t` up
    to `M ≤ 9,362`, with tight overflow at `9,363` copies of `448`. -/
theorem fp8_e4m3fn_kulisch_int32_9362_exact :
    (∀ (M P deltaE : Nat) (xs : List Int),
      1 ≤ M → xs.length ≤ M →
      (∀ x ∈ xs, x.natAbs ≤ (2 ^ (P + 1) - 1) * 2 ^ deltaE) →
      (seqIntSum xs).natAbs < 2 ^ (kulischMinBits M P deltaE - 1)) ∧
    (fp8E4M3MinSubnormal.toUnits = 1 ∧ fp8E4M3MinSubnormal.toRat = 1 / 512 ∧
     fp8E4M3MaxFinite.toUnits = 229376 ∧ fp8E4M3MaxFinite.toRat = 448 ∧
     (2 ^ 31 - 1) / e4m3MaxUnits = e4m3MaxInt32Count) ∧
    (∀ (xs : List Fp8E4M3FN), xs.length ≤ e4m3MaxInt32Count →
      let s := seqIntSum (xs.map Fp8E4M3FN.toUnits)
      int32Min ≤ s ∧ s ≤ int32Max ∧
      ((xs.map (fun x => Int32.ofInt x.toUnits)).foldl (· + ·) (0 : Int32)).toInt = s ∧
      (xs.map Fp8E4M3FN.toRat).foldl (· + ·) (0 : Rat) = (s : Rat) / (512 : Rat)) ∧
    (∀ (xs ys : List Fp8E4M3FN),
      seqIntSum ((xs ++ ys).map Fp8E4M3FN.toUnits) =
        seqIntSum (xs.map Fp8E4M3FN.toUnits) + seqIntSum (ys.map Fp8E4M3FN.toUnits)) ∧
    (∀ (xs ys : List Fp8E4M3FN), List.Perm xs ys →
      seqIntSum (xs.map Fp8E4M3FN.toUnits) = seqIntSum (ys.map Fp8E4M3FN.toUnits)) ∧
    (seqIntSum ((List.replicate 9362 fp8E4M3MaxFinite).map Fp8E4M3FN.toUnits) ≤ int32Max ∧
     int32Max < seqIntSum ((List.replicate 9363 fp8E4M3MaxFinite).map Fp8E4M3FN.toUnits)) := by
  refine ⟨?_, ⟨by decide, by simp [Fp8E4M3FN.toRat, fp8E4M3MinSubnormal, Fp8E4M3FN.toUnits, Fp8E4M3FN.magUnits],
               by decide, by simp [Fp8E4M3FN.toRat, fp8E4M3MaxFinite, Fp8E4M3FN.toUnits, Fp8E4M3FN.magUnits]; grind,
               by decide⟩, ?_, ?_, ?_, ?_⟩
  · intro M P deltaE xs hM hlen hbound
    exact kulisch_width_overflow_free hM xs hlen hbound
  · intro xs hlen
    have habs : (seqIntSum (xs.map Fp8E4M3FN.toUnits)).natAbs ≤
        (xs.map Fp8E4M3FN.toUnits).length * e4m3MaxUnits :=
      seqIntSum_natAbs_le (fun y hy => by
        rcases List.mem_map.mp hy with ⟨x, _, rfl⟩
        exact fp8_e4m3fn_toUnits_natAbs_le x)
    rw [List.length_map] at habs
    have hmul : xs.length * e4m3MaxUnits ≤ e4m3MaxInt32Count * e4m3MaxUnits :=
      Nat.mul_le_mul_right _ hlen
    have hmax : e4m3MaxInt32Count * e4m3MaxUnits = 2147418112 := by decide
    have hlo : int32Min ≤ seqIntSum (xs.map Fp8E4M3FN.toUnits) := by
      unfold int32Min; omega
    have hhi : seqIntSum (xs.map Fp8E4M3FN.toUnits) ≤ int32Max := by
      unfold int32Max; omega
    refine ⟨hlo, hhi, ?_, rat_foldl_fp8_eq_units xs⟩
    have hmap : xs.map (fun x => Int32.ofInt x.toUnits) =
        (xs.map Fp8E4M3FN.toUnits).map Int32.ofInt := by
      rw [List.map_map]; rfl
    rw [hmap, int32_foldl_eq_ofInt_seqIntSum, int32_toInt_ofInt_exact hlo hhi]
  · intro xs ys
    rw [List.map_append, seqIntSum_append]
  · intro xs ys hperm
    exact seqIntSum_perm (hperm.map Fp8E4M3FN.toUnits)
  · constructor
    · rw [List.map_replicate, seqIntSum_replicate]
      decide
    · rw [List.map_replicate, seqIntSum_replicate]
      decide

end KahanNeumaierFp8
