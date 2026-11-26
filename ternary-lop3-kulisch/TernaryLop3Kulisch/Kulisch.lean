/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TernaryLop3Kulisch.Defs

/-!
# Exact OCP FP8-E4M3 & FP8-E5M2 Kulisch Accumulator Bit-Width Theorems

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
- Theorem 4 (`fp8_e4m3_exact_kulisch_49bit_int64_theorem`): Every product of two finite OCP FP8-E4M3
  numbers is an exact integer multiple of `2^-18` bounded in magnitude by `448^2 * 2^18 = 52,613,349,376 < 2^36`
  (37 signed bits), and exact zero-error `int64` Kulisch accumulation holds for all `K ≤ 175,304,787`
  (with `K = 4096` requiring only 49 signed bits: `< 2^48`).
- Theorem 6 (`fp8_e5m2_vs_e4m3_kulisch_width_gap`): Every finite OCP FP8-E5M2 product at quantum `2^-32`
  is bounded by `57344^2 * 2^32 = 14,123,288,431,433,875,456 ≥ 2^63`, proving single-`int64` exact Kulisch
  accumulation is impossible for E5M2 even at `K = 1` (65 vs 37 bits at `K = 1`; 77 vs 49 bits at `K = 4096`).
-/

namespace TernaryLop3Kulisch

/-! ## 1. Helper Lemmas on `Int.natAbs` and `List.sum` -/

theorem natAbs_int_sum_le {α : Type} (l : List α) (f : α → Int) (B : Nat)
    (hB : ∀ x ∈ l, (f x).natAbs ≤ B) :
    (l.map f).sum.natAbs ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha : (f a).natAbs ≤ B := hB a (List.mem_cons_self ..)
    have ht : (t.map f).sum.natAbs ≤ t.length * B :=
      ih (fun x hx => hB x (List.mem_cons_of_mem a hx))
    have htri : (f a + (t.map f).sum).natAbs ≤ (f a).natAbs + (t.map f).sum.natAbs :=
      Int.natAbs_add_le _ _
    have hmul : (t.length + 1) * B = t.length * B + B := Nat.succ_mul t.length B
    omega

theorem pow_two_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

/-! ## 2. OCP FP8-E4M3 Exact 37-Bit / 49-Bit `int64` Kulisch Theorem -/

theorem e4m3Scaled_natAbs_le (x : BitVec 8) (hf : e4m3Finite x = true) :
    (e4m3Scaled x).natAbs ≤ 229376 := by
  unfold e4m3Scaled
  unfold e4m3Finite at hf
  dsimp only
  have he : ((x.toNat >>> 3) &&& 15) < 16 := Nat.and_lt_two_pow _ (n := 4) (by decide)
  have hm : (x.toNat &&& 7) < 8 := Nat.and_lt_two_pow _ (n := 3) (by decide)
  generalize he_eq : ((x.toNat >>> 3) &&& 15) = e at he hf ⊢
  generalize hm_eq : (x.toNat &&& 7) = m at hm hf ⊢
  have hnotnan : (e == 15 && m == 7) = false := by
    cases h : (e == 15 && m == 7)
    · rfl
    · simp [h] at hf
  simp only [hnotnan, Bool.false_eq_true, ↓reduceIte]
  have hmag : (if e == 0 then m else (8 + m) * 2 ^ (e - 1)) ≤ 229376 := by
    by_cases he0 : e = 0
    · simp only [he0, beq_self_eq_true, ↓reduceIte]
      omega
    · have hbe0 : (e == 0) = false := beq_false_of_ne he0
      simp only [hbe0, Bool.false_eq_true, ↓reduceIte]
      by_cases he15 : e = 15
      · have hmle : m ≤ 6 := by
          have hmne : m ≠ 7 := by
            intro hm7
            simp [he15, hm7] at hnotnan
          omega
        rw [he15]
        have : 2 ^ (15 - 1) = 16384 := by decide
        rw [this]
        omega
      · have hele : e - 1 ≤ 13 := by omega
        have hpow : 2 ^ (e - 1) ≤ 2 ^ 13 := pow_two_mono hele
        have h13 : 2 ^ 13 = 8192 := by decide
        rw [h13] at hpow
        have h1 : (8 + m) * 2 ^ (e - 1) ≤ 15 * 8192 :=
          Nat.mul_le_mul (by omega) hpow
        omega
  split
  · rw [Int.natAbs_neg]; exact hmag
  · exact hmag

theorem e4m3ProdScaled_natAbs_le (x y : BitVec 8)
    (hx : e4m3Finite x = true) (hy : e4m3Finite y = true) :
    (e4m3ProdScaled x y).natAbs ≤ 52613349376 ∧ (e4m3ProdScaled x y).natAbs < 2 ^ 36 := by
  unfold e4m3ProdScaled
  rw [Int.natAbs_mul]
  have h1 := e4m3Scaled_natAbs_le x hx
  have h2 := e4m3Scaled_natAbs_le y hy
  have hmul : (e4m3Scaled x).natAbs * (e4m3Scaled y).natAbs ≤ 229376 * 229376 :=
    Nat.mul_le_mul h1 h2
  have hval : 229376 * 229376 = 52613349376 := by decide
  have hlt : 52613349376 < 2 ^ 36 := by decide
  omega

theorem e4m3_max_witness :
    e4m3Finite (BitVec.ofNat 8 0x7E) = true ∧
    e4m3Scaled (BitVec.ofNat 8 0x7E) = 229376 ∧
    e4m3ProdScaled (BitVec.ofNat 8 0x7E) (BitVec.ofNat 8 0x7E) = 52613349376 := by
  decide

theorem e4m3DotScaled_natAbs_le (pairs : List (BitVec 8 × BitVec 8))
    (hfin : ∀ p ∈ pairs, e4m3Finite p.1 = true ∧ e4m3Finite p.2 = true) :
    (e4m3DotScaled pairs).natAbs ≤ pairs.length * 52613349376 := by
  unfold e4m3DotScaled
  apply natAbs_int_sum_le
  intro p hp
  rcases hfin p hp with ⟨h1, h2⟩
  exact (e4m3ProdScaled_natAbs_le p.1 p.2 h1 h2).1

/-- Headline Theorem 4: Universal OCP FP8-E4M3 exact 37-bit product and 49-bit / `int64` Kulisch theorem. -/
theorem fp8_e4m3_exact_kulisch_49bit_int64_theorem :
    (∀ x y : BitVec 8, e4m3Finite x = true → e4m3Finite y = true →
      (e4m3ProdScaled x y).natAbs ≤ 52613349376 ∧ (e4m3ProdScaled x y).natAbs < 2 ^ 36) ∧
    (e4m3Finite (BitVec.ofNat 8 0x7E) = true ∧
      e4m3ProdScaled (BitVec.ofNat 8 0x7E) (BitVec.ofNat 8 0x7E) = 52613349376) ∧
    (∀ pairs : List (BitVec 8 × BitVec 8),
      (∀ p ∈ pairs, e4m3Finite p.1 = true ∧ e4m3Finite p.2 = true) →
      (e4m3DotScaled pairs).natAbs ≤ pairs.length * 52613349376) ∧
    (∀ pairs : List (BitVec 8 × BitVec 8),
      (∀ p ∈ pairs, e4m3Finite p.1 = true ∧ e4m3Finite p.2 = true) →
      pairs.length ≤ 175304787 →
      (e4m3DotScaled pairs).natAbs < 2 ^ 63) ∧
    (175304788 * 52613349376 ≥ 2 ^ 63) ∧
    (∀ pairs : List (BitVec 8 × BitVec 8),
      (∀ p ∈ pairs, e4m3Finite p.1 = true ∧ e4m3Finite p.2 = true) →
      pairs.length ≤ 4096 →
      (e4m3DotScaled pairs).natAbs < 2 ^ 48) ∧
    (2 ^ 47 ≤ 4096 * 52613349376 ∧ 4096 * 52613349376 < 2 ^ 48) := by
  refine ⟨e4m3ProdScaled_natAbs_le, ⟨e4m3_max_witness.1, e4m3_max_witness.2.2⟩,
    e4m3DotScaled_natAbs_le, ?_, by decide, ?_, by decide⟩
  · intro pairs hfin hlen
    have h1 := e4m3DotScaled_natAbs_le pairs hfin
    have h2 : pairs.length * 52613349376 ≤ 175304787 * 52613349376 :=
      Nat.mul_le_mul_right _ hlen
    have h3 : 175304787 * 52613349376 < 2 ^ 63 := by decide
    omega
  · intro pairs hfin hlen
    have h1 := e4m3DotScaled_natAbs_le pairs hfin
    have h2 : pairs.length * 52613349376 ≤ 4096 * 52613349376 :=
      Nat.mul_le_mul_right _ hlen
    have h3 : 4096 * 52613349376 < 2 ^ 48 := by decide
    omega

/-! ## 3. OCP FP8-E5M2 vs FP8-E4M3 Kulisch Width-Gap Theorem -/

theorem e5m2Scaled_natAbs_le (x : BitVec 8) (hf : e5m2Finite x = true) :
    (e5m2Scaled x).natAbs ≤ 3758096384 := by
  unfold e5m2Scaled
  unfold e5m2Finite at hf
  dsimp only
  have he : ((x.toNat >>> 2) &&& 31) < 32 := Nat.and_lt_two_pow _ (n := 5) (by decide)
  have hm : (x.toNat &&& 3) < 4 := Nat.and_lt_two_pow _ (n := 2) (by decide)
  generalize he_eq : ((x.toNat >>> 2) &&& 31) = e at he hf ⊢
  generalize hm_eq : (x.toNat &&& 3) = m at hm hf ⊢
  have hene : e ≠ 31 := by
    intro h31
    simp [h31] at hf
  have hne31 : (e == 31) = false := beq_false_of_ne hene
  simp only [hne31, Bool.false_eq_true, ↓reduceIte]
  have he30 : e ≤ 30 := by omega
  have hmag : (if e == 0 then m else (4 + m) * 2 ^ (e - 1)) ≤ 3758096384 := by
    by_cases he0 : e = 0
    · simp only [he0, beq_self_eq_true, ↓reduceIte]
      omega
    · have hbe0 : (e == 0) = false := beq_false_of_ne he0
      simp only [hbe0, Bool.false_eq_true, ↓reduceIte]
      have hele : e - 1 ≤ 29 := by omega
      have hpow : 2 ^ (e - 1) ≤ 2 ^ 29 := pow_two_mono hele
      have h29 : 2 ^ 29 = 536870912 := by decide
      rw [h29] at hpow
      have h1 : (4 + m) * 2 ^ (e - 1) ≤ 7 * 536870912 :=
        Nat.mul_le_mul (by omega) hpow
      omega
  split
  · rw [Int.natAbs_neg]; exact hmag
  · exact hmag

theorem e5m2ProdScaled_natAbs_le (x y : BitVec 8)
    (hx : e5m2Finite x = true) (hy : e5m2Finite y = true) :
    (e5m2ProdScaled x y).natAbs ≤ 14123288431433875456 := by
  unfold e5m2ProdScaled
  rw [Int.natAbs_mul]
  have h1 := e5m2Scaled_natAbs_le x hx
  have h2 := e5m2Scaled_natAbs_le y hy
  have hmul : (e5m2Scaled x).natAbs * (e5m2Scaled y).natAbs ≤ 3758096384 * 3758096384 :=
    Nat.mul_le_mul h1 h2
  have hval : 3758096384 * 3758096384 = 14123288431433875456 := by decide
  omega

theorem e5m2_max_witness :
    e5m2Finite (BitVec.ofNat 8 0x7B) = true ∧
    e5m2Scaled (BitVec.ofNat 8 0x7B) = 3758096384 ∧
    e5m2ProdScaled (BitVec.ofNat 8 0x7B) (BitVec.ofNat 8 0x7B) = 14123288431433875456 := by
  decide

/-- Headline Theorem 6: Exact 28-bit Kulisch width gap between OCP FP8-E5M2 and FP8-E4M3. -/
theorem fp8_e5m2_vs_e4m3_kulisch_width_gap :
    (∀ x y : BitVec 8, e5m2Finite x = true → e5m2Finite y = true →
      (e5m2ProdScaled x y).natAbs ≤ 14123288431433875456) ∧
    (e5m2Finite (BitVec.ofNat 8 0x7B) = true ∧
      e5m2ProdScaled (BitVec.ofNat 8 0x7B) (BitVec.ofNat 8 0x7B) = 14123288431433875456 ∧
      2 ^ 63 ≤ (e5m2ProdScaled (BitVec.ofNat 8 0x7B) (BitVec.ofNat 8 0x7B)).natAbs ∧
      (e5m2ProdScaled (BitVec.ofNat 8 0x7B) (BitVec.ofNat 8 0x7B)).natAbs < 2 ^ 64) ∧
    (2 ^ 35 ≤ 52613349376 ∧ 52613349376 < 2 ^ 36) ∧
    (2 ^ 47 ≤ 4096 * 52613349376 ∧ 4096 * 52613349376 < 2 ^ 48) ∧
    (2 ^ 75 ≤ 4096 * 14123288431433875456 ∧ 4096 * 14123288431433875456 < 2 ^ 76) := by
  refine ⟨e5m2ProdScaled_natAbs_le,
    ⟨e5m2_max_witness.1, e5m2_max_witness.2.2, ?_, ?_⟩,
    by decide, by decide, by decide⟩
  · rw [e5m2_max_witness.2.2]; decide
  · rw [e5m2_max_witness.2.2]; decide

end TernaryLop3Kulisch
