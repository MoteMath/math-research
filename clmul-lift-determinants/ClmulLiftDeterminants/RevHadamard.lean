/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ClmulLiftDeterminants.BitAlgebra
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

/-!
# Bit-Reversed Sylvester Hadamard Matrices & Principal Minor Determinants

Defines `hadamard R k` and `revHadamard R k m` over any commutative ring `R`, and proves exact
determinants for:
- full size `m = 2^k` (via `sign(bitrevPerm k) = -1` iff `k = 2`),
- cofactor size `m = 2^k - 1` (via Hadamard orthogonality + `Matrix.mul_adjugate`),
- all gap sizes `2 ≤ m ≤ 2^k - 2` (`det = 0` over EVERY commutative ring `R`).
-/

namespace ClmulLiftDeterminants

open scoped BigOperators
open Matrix Finset

/-- Number of set bits of `x` in positions `< k`. -/
def popcntK (k x : ℕ) : ℕ :=
  ((Finset.range k).filter (fun u => x.testBit u = true)).card

/-- Standard `2^k × 2^k` Sylvester Hadamard matrix over `R`:
`(H_k)_{i, j} = (-1)^{popcnt_k(i &&& j)}`. -/
def hadamard (R : Type*) [CommRing R] (k : ℕ) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R :=
  Matrix.of fun i j => (-1 : R) ^ popcntK k (i.1 &&& j.1)

/-- Leading `m × m` principal submatrix of the bit-reversed `2^k × 2^k` Hadamard matrix over `R`:
`(H_{k, m}^{rev})_{r, j} = (-1)^{popcnt_k(bitrev_k(r) &&& j)}`. -/
def revHadamard (R : Type*) [CommRing R] (k m : ℕ) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun r j => (-1 : R) ^ popcntK k (bitrevNat k r.1 &&& j.1)

/-- `k`-bit reversal as an involution permutation on `Fin (2 ^ k)`. -/
def bitrevPerm (k : ℕ) : Equiv.Perm (Fin (2 ^ k)) where
  toFun i := ⟨bitrevNat k i.1, bitrevNat_lt k i.1⟩
  invFun i := ⟨bitrevNat k i.1, bitrevNat_lt k i.1⟩
  left_inv i := Fin.ext (bitrevNat_bitrevNat k i.1 i.2)
  right_inv i := Fin.ext (bitrevNat_bitrevNat k i.1 i.2)

/-! ## Section 1: Sylvester Hadamard Determinant & Orthogonality -/

theorem popcntK_succ_split (k x : ℕ) :
    popcntK (k + 1) x = popcntK k x + (if x.testBit k = true then 1 else 0) := by
  unfold popcntK
  rw [Finset.range_add_one, Finset.filter_insert]
  have hnotmem : k ∉ (Finset.range k).filter (fun u => x.testBit u = true) := by simp
  split_ifs with h
  · rw [Finset.card_insert_of_notMem hnotmem]
  · omega

theorem hadamard_block_decomp (R : Type*) [CommRing R] (k : ℕ) :
    let e : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) :=
      finSumFinEquiv.trans (finCongr (by rw [pow_succ]; ring))
    (hadamard R (k + 1)).submatrix e e =
      Matrix.fromBlocks (hadamard R k) (hadamard R k) (hadamard R k) (-hadamard R k) := by
  intro e
  have he_inl : ∀ i : Fin (2 ^ k), (e (Sum.inl i)).1 = i.1 := fun i => by simp [e]
  have he_inr : ∀ i : Fin (2 ^ k), (e (Sum.inr i)).1 = 2 ^ k + i.1 := fun i => by simp [e]; omega
  have hlt_bit : ∀ (x : Fin (2 ^ k)), x.1.testBit k = false :=
    fun x => testBit_eq_false_of_lt_two_pow x.2
  have hadd_bit : ∀ (x : Fin (2 ^ k)) (u : ℕ), u < k → (2 ^ k + x.1).testBit u = x.1.testBit u := by
    intro x u hu
    have hand : x.1 &&& (2 ^ k * 1) = 0 := and_eq_zero_of_lt_two_pow_mul x.2
    have hxor : 2 ^ k + x.1 = x.1 ^^^ 2 ^ k := by
      rw [add_comm]; exact (xor_eq_add_of_and_eq_zero (by simpa using hand)).symm
    rw [hxor, Nat.testBit_xor, Nat.testBit_two_pow]
    have hne : k ≠ u := ne_of_gt hu
    simp [hne]
  have hadd_top : ∀ (x : Fin (2 ^ k)), (2 ^ k + x.1).testBit k = true := by
    intro x
    have hand : x.1 &&& (2 ^ k * 1) = 0 := and_eq_zero_of_lt_two_pow_mul x.2
    have hxor : 2 ^ k + x.1 = x.1 ^^^ 2 ^ k := by
      rw [add_comm]; exact (xor_eq_add_of_and_eq_zero (by simpa using hand)).symm
    rw [hxor, Nat.testBit_xor, hlt_bit x, Nat.testBit_two_pow]
    simp
  ext a b
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, hadamard, Matrix.of_apply,
        he_inl, popcntK_succ_split, Nat.testBit_and, hlt_bit i, Bool.false_and]
      simp
    | inr j =>
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, hadamard, Matrix.of_apply,
        he_inl, he_inr, popcntK_succ_split, Nat.testBit_and, hlt_bit i, Bool.false_and]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      congr 1
      unfold popcntK
      refine congrArg Finset.card (Finset.filter_congr fun u hu => ?_)
      simp [Nat.testBit_and, hadd_bit j u (Finset.mem_range.mp hu)]
  | inr i =>
    cases b with
    | inl j =>
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, hadamard, Matrix.of_apply,
        he_inl, he_inr, popcntK_succ_split, Nat.testBit_and, hlt_bit j, Bool.and_false]
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      congr 1
      unfold popcntK
      refine congrArg Finset.card (Finset.filter_congr fun u hu => ?_)
      simp [Nat.testBit_and, hadd_bit i u (Finset.mem_range.mp hu)]
    | inr j =>
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, hadamard,
        Matrix.of_apply, he_inr, popcntK_succ_split, Nat.testBit_and, hadd_top i, hadd_top j,
        Bool.and_self, ↓reduceIte, pow_succ]
      have hpop : popcntK k ((2 ^ k + i.1) &&& (2 ^ k + j.1)) = popcntK k (i.1 &&& j.1) := by
        unfold popcntK
        refine congrArg Finset.card (Finset.filter_congr fun u hu => ?_)
        simp [Nat.testBit_and, hadd_bit i u (Finset.mem_range.mp hu),
              hadd_bit j u (Finset.mem_range.mp hu)]
      rw [hpop]; ring

theorem det_hadamard (R : Type*) [CommRing R] : ∀ k : ℕ,
    (hadamard R k).det = (if k = 1 then (-1 : R) else 1) * (2 : R) ^ (k * 2 ^ (k - 1))
  | 0 => by
    simp [hadamard, popcntK]
  | k + 1 => by
    have ih := det_hadamard R k
    let e : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) :=
      finSumFinEquiv.trans (finCongr (by rw [pow_succ]; ring))
    have hsub := hadamard_block_decomp R k
    have hdet_eq : (hadamard R (k + 1)).det =
        (Matrix.fromBlocks (hadamard R k) (hadamard R k) (hadamard R k) (-hadamard R k)).det := by
      rw [← hsub, Matrix.det_submatrix_equiv_self]
    rw [hdet_eq]
    let L : Matrix (Fin (2 ^ k) ⊕ Fin (2 ^ k)) (Fin (2 ^ k) ⊕ Fin (2 ^ k)) R :=
      Matrix.fromBlocks 1 0 (-1) 1
    have hL_det : L.det = 1 := by simp [L]
    have hmul : L * Matrix.fromBlocks (hadamard R k) (hadamard R k) (hadamard R k) (-hadamard R k) =
        Matrix.fromBlocks (hadamard R k) (hadamard R k) 0 ((-2 : R) • hadamard R k) := by
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.neg_mul, add_zero, neg_add_cancel]
      congr 1
      ext i j; simp; ring
    have hdet_mul := congrArg Matrix.det hmul
    rw [Matrix.det_mul, hL_det, one_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul,
        Fintype.card_fin] at hdet_mul
    rw [hdet_mul, ih]
    cases k with
    | zero => simp
    | succ k' =>
      have hne1 : k' + 1 + 1 ≠ 1 := by omega
      simp only [hne1, ↓reduceIte, one_mul]
      have hsq_sgn : (if k' + 1 = 1 then (-1 : R) else 1) * (if k' + 1 = 1 then (-1 : R) else 1) = 1 := by
        split_ifs <;> ring
      have hneg2 : (-2 : R) ^ (2 ^ (k' + 1)) = (2 : R) ^ (2 ^ (k' + 1)) := by
        have heven : 2 ^ (k' + 1) = 2 * 2 ^ k' := by rw [pow_succ, mul_comm]
        rw [heven, pow_mul, pow_mul]; ring
      have hexp : 2 ^ (k' + 1) + (k' + 1) * 2 ^ k' + (k' + 1) * 2 ^ k' =
          (k' + 1 + 1) * 2 ^ (k' + 1) := by
        rw [pow_succ]; ring
      calc (if k' + 1 = 1 then (-1 : R) else 1) * 2 ^ ((k' + 1) * 2 ^ k') *
            ((-2) ^ 2 ^ (k' + 1) * ((if k' + 1 = 1 then (-1 : R) else 1) * 2 ^ ((k' + 1) * 2 ^ k')))
          = ((if k' + 1 = 1 then (-1 : R) else 1) * (if k' + 1 = 1 then (-1 : R) else 1)) *
            ((-2) ^ 2 ^ (k' + 1) * 2 ^ ((k' + 1) * 2 ^ k') * 2 ^ ((k' + 1) * 2 ^ k')) := by ring
        _ = 2 ^ 2 ^ (k' + 1) * 2 ^ ((k' + 1) * 2 ^ k') * 2 ^ ((k' + 1) * 2 ^ k') := by
            rw [hsq_sgn, one_mul, hneg2]
        _ = 2 ^ ((k' + 1 + 1) * 2 ^ (k' + 1)) := by
            rw [← pow_add, ← pow_add, hexp]

theorem hadamard_mul_transpose (R : Type*) [CommRing R] : ∀ k : ℕ,
    hadamard R k * (hadamard R k).transpose = ((2 ^ k : ℕ) : R) • (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R)
  | 0 => by
    ext i j; fin_cases i; fin_cases j; simp [hadamard, popcntK, Matrix.mul_apply]
  | k + 1 => by
    have ih := hadamard_mul_transpose R k
    let e : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) :=
      finSumFinEquiv.trans (finCongr (by rw [pow_succ]; ring))
    have hsub := hadamard_block_decomp R k
    have hmul_sub :
        (hadamard R (k + 1) * (hadamard R (k + 1)).transpose).submatrix e e =
        ((hadamard R (k + 1)).submatrix e e) * ((hadamard R (k + 1)).submatrix e e).transpose := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
      exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    have hblocks :
        ((hadamard R (k + 1)).submatrix e e) * ((hadamard R (k + 1)).submatrix e e).transpose =
        ((2 ^ (k + 1) : ℕ) : R) • (1 : Matrix (Fin (2 ^ k) ⊕ Fin (2 ^ k)) (Fin (2 ^ k) ⊕ Fin (2 ^ k)) R) := by
      rw [hsub, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
      simp only [Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg, add_neg_cancel, ih]
      ext a b
      cases a <;> cases b <;>
        simp [Matrix.fromBlocks, pow_succ, Matrix.one_apply] <;> split_ifs <;> ring
    ext i j
    have hij := congrArg (fun M => M (e.symm i) (e.symm j)) (hmul_sub.trans hblocks)
    simpa [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply, e.injective.eq_iff] using hij

/-! ## Section 2: Sign of `bitrevPerm k` -/

private def flipFin2 (c x : Fin 2) : Fin 2 :=
  if c = 0 then x else if x = 0 then 1 else 0

private theorem flipFin2_invol (c x : Fin 2) : flipFin2 c (flipFin2 c x) = x := by
  fin_cases c <;> fin_cases x <;> decide

private theorem flipFin2_eq_zero_iff (c x : Fin 2) : flipFin2 c x = 0 ↔ x = c := by
  fin_cases c <;> fin_cases x <;> decide

private theorem fin2_eq_one_of_ne_zero {x : Fin 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

private theorem sign_mid_perm_eq_one {M : Type*} [Fintype M] [DecidableEq M] (g : Equiv.Perm M) :
    Equiv.Perm.sign
      ({ toFun := fun (x : Fin 2 × M × Fin 2) => (x.1, g x.2.1, x.2.2)
         invFun := fun x => (x.1, g.symm x.2.1, x.2.2)
         left_inv := fun ⟨_, _, _⟩ => by simp
         right_inv := fun ⟨_, _, _⟩ => by simp } : Equiv.Perm (Fin 2 × M × Fin 2)) = 1 := by
  let midRev : Equiv.Perm (Fin 2 × M × Fin 2) := {
    toFun := fun x => (x.1, g x.2.1, x.2.2)
    invFun := fun x => (x.1, g.symm x.2.1, x.2.2)
    left_inv := fun ⟨_, _, _⟩ => by simp
    right_inv := fun ⟨_, _, _⟩ => by simp
  }
  let mr (a0 b0 : Fin 2) : Equiv.Perm (Fin 2 × M × Fin 2) := {
    toFun := fun x => if x.1 = a0 ∧ x.2.2 = b0 then (x.1, g x.2.1, x.2.2) else x
    invFun := fun x => if x.1 = a0 ∧ x.2.2 = b0 then (x.1, g.symm x.2.1, x.2.2) else x
    left_inv := fun ⟨a, mid, b⟩ => by by_cases h : a = a0 ∧ b = b0 <;> simp [h]
    right_inv := fun ⟨a, mid, b⟩ => by by_cases h : a = a0 ∧ b = b0 <;> simp [h]
  }
  let flipOuter (a0 b0 : Fin 2) : Equiv.Perm (Fin 2 × M × Fin 2) := {
    toFun := fun x => (flipFin2 a0 x.1, x.2.1, flipFin2 b0 x.2.2)
    invFun := fun x => (flipFin2 a0 x.1, x.2.1, flipFin2 b0 x.2.2)
    left_inv := fun ⟨a, mid, b⟩ => by simp [flipFin2_invol]
    right_inv := fun ⟨a, mid, b⟩ => by simp [flipFin2_invol]
  }
  have hmr_fac : midRev = mr 0 0 * mr 0 1 * mr 1 0 * mr 1 1 := by
    refine Equiv.ext fun ⟨a, mid, b⟩ => ?_
    change midRev (a, mid, b) = mr 0 0 (mr 0 1 (mr 1 0 (mr 1 1 (a, mid, b))))
    by_cases ha : a = 0
    · subst ha
      by_cases hb : b = 0
      · subst hb; simp [midRev, mr]
      · have hb1 : b = 1 := fin2_eq_one_of_ne_zero hb
        subst hb1; simp [midRev, mr]
    · have ha1 : a = 1 := fin2_eq_one_of_ne_zero ha
      subst ha1
      by_cases hb : b = 0
      · subst hb; simp [midRev, mr]
      · have hb1 : b = 1 := fin2_eq_one_of_ne_zero hb
        subst hb1; simp [midRev, mr]
  have hmr_conj : ∀ a0 b0 : Fin 2, mr a0 b0 = flipOuter a0 b0 * mr 0 0 * (flipOuter a0 b0)⁻¹ := by
    intro a0 b0
    refine Equiv.ext fun ⟨a, mid, b⟩ => ?_
    change mr a0 b0 (a, mid, b) = flipOuter a0 b0 (mr 0 0 ((flipOuter a0 b0).symm (a, mid, b)))
    simp only [mr, flipOuter, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, flipFin2_eq_zero_iff]
    by_cases h : a = a0 ∧ b = b0
    · simp [h, flipFin2_invol]
    · simp [h, flipFin2_invol]
  change Equiv.Perm.sign midRev = 1
  rw [hmr_fac, map_mul, map_mul, map_mul]
  have hsame : ∀ a0 b0 : Fin 2, Equiv.Perm.sign (mr a0 b0) = Equiv.Perm.sign (mr 0 0) := by
    intro a0 b0
    rw [hmr_conj a0 b0, map_mul, map_mul, map_inv]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (mr 0 0)) with h1 | h1 <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign (flipOuter a0 b0)) with h2 | h2 <;>
    rw [h1, h2] <;> rfl
  rw [hsame 0 1, hsame 1 0, hsame 1 1]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (mr 0 0)) with h | h <;> rw [h] <;> rfl

/-- Exact sign of the `k`-bit reversal permutation: `-1` at `k = 2`, and `+1` for every other `k`. -/
theorem sign_bitrevPerm : ∀ k : ℕ, Equiv.Perm.sign (bitrevPerm k) = if k = 2 then (-1 : ℤˣ) else 1
  | 0 => by
    have h1 : bitrevPerm 0 = 1 := Equiv.ext fun x => by fin_cases x; rfl
    rw [h1, map_one]; rfl
  | 1 => by
    have h1 : bitrevPerm 1 = 1 := Equiv.ext fun x => by fin_cases x <;> rfl
    rw [h1, map_one]; rfl
  | 2 => by
    have hsw : bitrevPerm 2 = Equiv.swap (⟨1, by omega⟩ : Fin 4) ⟨2, by omega⟩ := by
      refine Equiv.ext fun x => ?_
      fin_cases x <;> decide
    rw [hsw, Equiv.Perm.sign_swap (by decide)]; rfl
  | m + 3 => by
    -- For k = m + 3 (so k = (m + 1) + 2 with m + 1 ≥ 1), decompose Fin (2^(m+3)) ≃ Fin 2 × Fin (2^(m+1)) × Fin 2
    -- via (top bit a, middle (m+1) bits mid, bottom bit b).
    -- bitrevPerm (m+3) = swapOuter * midRev:
    --   - swapOuter swaps (0, mid, 1) ↔ (1, mid, 0) for all mid < 2^(m+1) (splits into 2 conjugate halves ⇒ sign = 1!)
    --   - midRev applies bitrev on mid for each of the 4 outer pairs (a, b) (4 conjugate copies ⇒ sign = 1!)
    set M := 2 ^ (m + 1)
    have hM_eq : M = 2 * 2 ^ m := by dsimp [M]; rw [pow_succ, mul_comm]
    have hN_eq : 2 ^ (m + 3) = 2 * (2 * M) := by dsimp [M]; rw [pow_succ, pow_succ]; ring
    have hM_pos : 0 < M := by positivity
    -- Equivalence e : Fin (2^(m+3)) ≃ Fin 2 × Fin M × Fin 2 via x = a * (2*M) + 2*mid + b
    let e : Fin (2 ^ (m + 3)) ≃ Fin 2 × Fin M × Fin 2 := {
      toFun := fun x =>
        (⟨x.1 / (2 * M), by
            have hx : x.1 < 2 * (2 * M) := lt_of_lt_of_eq x.2 hN_eq
            exact Nat.div_lt_of_lt_mul (by omega)⟩,
         ⟨(x.1 % (2 * M)) / 2, by have := Nat.mod_lt x.1 (show 0 < 2 * M by omega); omega⟩,
         ⟨x.1 % 2, Nat.mod_lt _ (by omega)⟩)
      invFun := fun p =>
        ⟨p.1.1 * (2 * M) + 2 * p.2.1.1 + p.2.2.1, by
          have ha := p.1.2; have hmid := p.2.1.2; have hb := p.2.2.2
          have ha2 : p.1.1 = 0 ∨ p.1.1 = 1 := by omega
          rcases ha2 with h0 | h1
          · rw [h0]; omega
          · rw [h1]; omega⟩
      left_inv := fun x => by
        apply Fin.ext
        dsimp only
        have hdm := Nat.div_add_mod x.1 (2 * M)
        have hmod2 : (x.1 % (2 * M)) % 2 = x.1 % 2 := Nat.mod_mod_of_dvd x.1 ⟨M, rfl⟩
        have hmul : x.1 / (2 * M) * (2 * M) = (2 * M) * (x.1 / (2 * M)) := mul_comm _ _
        omega
      right_inv := fun ⟨⟨a, ha⟩, ⟨mid, hmid⟩, ⟨b, hb⟩⟩ => by
        have hlt : 2 * mid + b < 2 * M := by omega
        have hdiv1 : (a * (2 * M) + 2 * mid + b) / (2 * M) = a := by
          have : a * (2 * M) + 2 * mid + b = (2 * mid + b) + (2 * M) * a := by ring
          rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, zero_add]
        have hmod1 : (a * (2 * M) + 2 * mid + b) % (2 * M) = 2 * mid + b := by
          have : a * (2 * M) + 2 * mid + b = (2 * mid + b) + (2 * M) * a := by ring
          rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
        have hmod2 : (a * (2 * M) + 2 * mid + b) % 2 = b := by
          have : a * (2 * M) + 2 * mid + b = b + 2 * (a * M + mid) := by ring
          rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
        ext
        · simp [hdiv1]
        · simp [hmod1]; omega
        · simp [hmod2]
    }
    -- Transport bitrevPerm (m + 3) across e to Fin 2 × Fin M × Fin 2
    let p : Equiv.Perm (Fin 2 × Fin M × Fin 2) := {
      toFun := fun ⟨a, mid, b⟩ => (b, bitrevPerm (m + 1) mid, a)
      invFun := fun ⟨a, mid, b⟩ => (b, bitrevPerm (m + 1) mid, a)
      left_inv := fun ⟨a, mid, b⟩ => by simp [bitrevPerm, bitrevNat_bitrevNat _ _ mid.2]
      right_inv := fun ⟨a, mid, b⟩ => by simp [bitrevPerm, bitrevNat_bitrevNat _ _ mid.2]
    }
    have hconj : bitrevPerm (m + 3) = e.symm.permCongr p := by
      ext x
      -- Show bitrevNat (m + 3) (e.symm (a, mid, b)) = e.symm (b, bitrevNat (m + 1) mid, a)
      have hbit : ∀ (a : Fin 2) (mid : Fin M) (b : Fin 2),
          bitrevNat (m + 3) (e.symm (a, mid, b)).1 =
          (e.symm (b, bitrevPerm (m + 1) mid, a)).1 := by
        intro a mid b
        apply Nat.eq_of_testBit_eq; intro u
        by_cases hu : u < m + 3
        · rw [testBit_bitrevNat (m + 3) _ u hu]
          have hval : ∀ (a' : Fin 2) (mid' : Fin M) (b' : Fin 2) (r : ℕ), r < m + 3 →
              (e.symm (a', mid', b')).1.testBit r =
              if r = 0 then (b'.1 == 1)
              else if r = m + 2 then (a'.1 == 1)
              else mid'.1.testBit (r - 1) := by
            intro a' mid' b' r hr
            have heval : (e.symm (a', mid', b')).1 = a'.1 * (2 * M) + 2 * mid'.1 + b'.1 := rfl
            rw [heval]
            have ha' : a'.1 < 2 := a'.2
            have hb' : b'.1 < 2 := b'.2
            have hmid' : mid'.1 < M := mid'.2
            by_cases hr0 : r = 0
            · subst hr0
              simp only [↓reduceIte, Nat.testBit_zero]
              have hmod2 : (a'.1 * (2 * M) + 2 * mid'.1 + b'.1) % 2 = b'.1 := by
                have : a'.1 * (2 * M) + 2 * mid'.1 + b'.1 = b'.1 + 2 * (a'.1 * M + mid'.1) := by ring
                rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb']
              rw [hmod2]
              have hb2 : b'.1 = 0 ∨ b'.1 = 1 := by omega
              rcases hb2 with h | h <;> simp [h]
            · by_cases hrt : r = m + 2
              · subst hrt
                simp only [hr0, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
                have h2m2 : 2 ^ (m + 2) = 2 * M := by dsimp [M]; rw [pow_succ]; ring
                rw [h2m2]
                have hdiv : (a'.1 * (2 * M) + 2 * mid'.1 + b'.1) / (2 * M) = a'.1 := by
                  have : a'.1 * (2 * M) + 2 * mid'.1 + b'.1 = (2 * mid'.1 + b'.1) + (2 * M) * a'.1 := by ring
                  rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
                rw [hdiv]
                have ha2 : a'.1 = 0 ∨ a'.1 = 1 := by omega
                rcases ha2 with h | h <;> simp [h]
              · simp only [hr0, hrt, ↓reduceIte]
                have hr1 : r = (r - 1) + 1 := by omega
                have h2m2 : 2 * M = 2 ^ (m + 2) := by dsimp [M]; rw [pow_succ]; ring
                have hmid_lt : 2 * mid'.1 + b'.1 < 2 ^ (m + 2) := by omega
                have hand : (2 * mid'.1 + b'.1) &&& (2 ^ (m + 2) * a'.1) = 0 :=
                  and_eq_zero_of_lt_two_pow_mul hmid_lt
                have hxor : a'.1 * (2 * M) + 2 * mid'.1 + b'.1 =
                    (2 * mid'.1 + b'.1) ^^^ (2 ^ (m + 2) * a'.1) := by
                  have : a'.1 * (2 * M) + 2 * mid'.1 + b'.1 = (2 * mid'.1 + b'.1) + (2 ^ (m + 2) * a'.1) := by
                    rw [h2m2]; ring
                  rw [this]; exact (xor_eq_add_of_and_eq_zero hand).symm
                have hlt_m2 : r < m + 2 := by omega
                rw [hxor, Nat.testBit_xor, testBit_pow_two_mul]
                simp only [hlt_m2, ↓reduceIte, Bool.xor_false]
                conv_lhs => rw [hr1, Nat.testBit_succ]
                have hdiv2 : (2 * mid'.1 + b'.1) / 2 = mid'.1 := by omega
                rw [hdiv2]
          rw [hval a mid b (m + 3 - 1 - u) (by omega), hval b (bitrevPerm (m + 1) mid) a u hu]
          by_cases hu0 : u = 0
          · subst hu0; simp
          · by_cases hut : u = m + 2
            · subst hut; simp
            · have hne1 : m + 3 - 1 - u ≠ 0 := by omega
              have hne2 : m + 3 - 1 - u ≠ m + 2 := by omega
              simp only [hu0, hut, hne1, hne2, ↓reduceIte, bitrevPerm, Equiv.coe_fn_mk]
              rw [testBit_bitrevNat (m + 1) mid.1 (u - 1) (by omega)]
              congr 1; omega
        · have hge : m + 3 ≤ u := Nat.not_lt.mp hu
          rw [testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le (bitrevNat_lt _ _) (Nat.pow_le_pow_right (by omega) hge)),
              testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le (e.symm _).2 (Nat.pow_le_pow_right (by omega) hge))]
      have hx := hbit (e x).1 (e x).2.1 (e x).2.2
      have he_eta : ((e x).1, (e x).2.1, (e x).2.2) = e x := rfl
      rw [he_eta, Equiv.symm_apply_apply] at hx
      simpa [bitrevPerm, p, Equiv.permCongr_apply] using hx
    -- Now sign(bitrevPerm (m+3)) = sign(p)! Factor p = swapOuter * midRev and prove both signs = 1!
    have hsign_eq : Equiv.Perm.sign (bitrevPerm (m + 3)) = Equiv.Perm.sign p := by
      rw [hconj, Equiv.Perm.sign_permCongr]
    rw [hsign_eq]
    have hne2 : m + 3 ≠ 2 := by omega
    simp only [hne2, ↓reduceIte]
    let swapOuter : Equiv.Perm (Fin 2 × Fin M × Fin 2) := {
      toFun := fun ⟨a, mid, b⟩ => (b, mid, a)
      invFun := fun ⟨a, mid, b⟩ => (b, mid, a)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl
    }
    let midRev : Equiv.Perm (Fin 2 × Fin M × Fin 2) := {
      toFun := fun ⟨a, mid, b⟩ => (a, bitrevPerm (m + 1) mid, b)
      invFun := fun ⟨a, mid, b⟩ => (a, bitrevPerm (m + 1) mid, b)
      left_inv := fun ⟨a, mid, b⟩ => by simp [bitrevPerm, bitrevNat_bitrevNat _ _ mid.2]
      right_inv := fun ⟨a, mid, b⟩ => by simp [bitrevPerm, bitrevNat_bitrevNat _ _ mid.2]
    }
    have hp_fac : p = swapOuter * midRev := by ext ⟨a, mid, b⟩ <;> rfl
    -- 1) sign(swapOuter) = 1: split mid < 2^m vs mid ≥ 2^m (two conjugate halves!)
    let sw0 : Equiv.Perm (Fin 2 × Fin M × Fin 2) := {
      toFun := fun ⟨a, mid, b⟩ => if mid.1 < 2 ^ m then (b, mid, a) else (a, mid, b)
      invFun := fun ⟨a, mid, b⟩ => if mid.1 < 2 ^ m then (b, mid, a) else (a, mid, b)
      left_inv := fun ⟨a, mid, b⟩ => by by_cases h : mid.1 < 2 ^ m <;> simp [h]
      right_inv := fun ⟨a, mid, b⟩ => by by_cases h : mid.1 < 2 ^ m <;> simp [h]
    }
    let sw1 : Equiv.Perm (Fin 2 × Fin M × Fin 2) := {
      toFun := fun ⟨a, mid, b⟩ => if mid.1 < 2 ^ m then (a, mid, b) else (b, mid, a)
      invFun := fun ⟨a, mid, b⟩ => if mid.1 < 2 ^ m then (a, mid, b) else (b, mid, a)
      left_inv := fun ⟨a, mid, b⟩ => by by_cases h : mid.1 < 2 ^ m <;> simp [h]
      right_inv := fun ⟨a, mid, b⟩ => by by_cases h : mid.1 < 2 ^ m <;> simp [h]
    }
    let flipMid : Equiv.Perm (Fin 2 × Fin M × Fin 2) := {
      toFun := fun ⟨a, mid, b⟩ =>
        (a, if h : mid.1 < 2 ^ m then ⟨mid.1 + 2 ^ m, by omega⟩ else ⟨mid.1 - 2 ^ m, by omega⟩, b)
      invFun := fun ⟨a, mid, b⟩ =>
        (a, if h : mid.1 < 2 ^ m then ⟨mid.1 + 2 ^ m, by omega⟩ else ⟨mid.1 - 2 ^ m, by omega⟩, b)
      left_inv := fun ⟨a, mid, b⟩ => by
        by_cases h : mid.1 < 2 ^ m
        · have h2 : ¬(mid.1 + 2 ^ m < 2 ^ m) := by omega
          ext <;> simp [h, h2]
        · have h2 : mid.1 - 2 ^ m < 2 ^ m := by have := mid.2; omega
          ext <;> simp [h, h2]; omega
      right_inv := fun ⟨a, mid, b⟩ => by
        by_cases h : mid.1 < 2 ^ m
        · have h2 : ¬(mid.1 + 2 ^ m < 2 ^ m) := by omega
          ext <;> simp [h, h2]
        · have h2 : mid.1 - 2 ^ m < 2 ^ m := by have := mid.2; omega
          ext <;> simp [h, h2]; omega
    }
    have hsw_fac : swapOuter = sw0 * sw1 := by
      ext ⟨a, mid, b⟩ <;> by_cases h : mid.1 < 2 ^ m <;> simp [swapOuter, sw0, sw1, h]
    have hsw_conj : sw1 = flipMid * sw0 * flipMid⁻¹ := by
      refine Equiv.ext fun ⟨a, mid, b⟩ => ?_
      change sw1 (a, mid, b) = flipMid (sw0 (flipMid.symm (a, mid, b)))
      by_cases h : mid.1 < 2 ^ m
      · have h2 : ¬(mid.1 + 2 ^ m < 2 ^ m) := by omega
        ext <;> simp [sw0, sw1, flipMid, h, h2]
      · have h2 : mid.1 - 2 ^ m < 2 ^ m := by have := mid.2; omega
        ext
        · simp [sw0, sw1, flipMid, h, h2]
        · simp [sw0, sw1, flipMid, h, h2]; omega
        · simp [sw0, sw1, flipMid, h, h2]
    have hsign_sw : Equiv.Perm.sign swapOuter = 1 := by
      rw [hsw_fac, map_mul, hsw_conj, map_mul, map_mul, map_inv]
      rcases Int.units_eq_one_or (Equiv.Perm.sign sw0) with h1 | h1 <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign flipMid) with h2 | h2 <;>
      rw [h1, h2] <;> rfl
    -- 2) sign(midRev) = 1 via sign_mid_perm_eq_one!
    have hsign_mr : Equiv.Perm.sign midRev = 1 := by
      have hmid_eq : midRev =
          ({ toFun := fun (x : Fin 2 × Fin M × Fin 2) => (x.1, bitrevPerm (m + 1) x.2.1, x.2.2)
             invFun := fun x => (x.1, (bitrevPerm (m + 1)).symm x.2.1, x.2.2)
             left_inv := fun ⟨_, _, _⟩ => by simp
             right_inv := fun ⟨_, _, _⟩ => by simp } : Equiv.Perm (Fin 2 × Fin M × Fin 2)) :=
        Equiv.ext fun ⟨_, _, _⟩ => rfl
      rw [hmid_eq]
      exact sign_mid_perm_eq_one (bitrevPerm (m + 1))
    rw [hp_fac, map_mul, hsign_sw, hsign_mr, mul_one]

/-! ## Section 3: Exact Determinants of `revHadamard R k m` -/

theorem revHadamard_full_eq_submatrix (R : Type*) [CommRing R] (k : ℕ) :
    revHadamard R k (2 ^ k) = (hadamard R k).submatrix (bitrevPerm k) id := by
  ext r j
  simp [revHadamard, hadamard, bitrevPerm]

/-- Full-size (`m = 2^k`) bit-reversed Hadamard determinant over any commutative ring `R`. -/
theorem det_revHadamard_full (R : Type*) [CommRing R] (k : ℕ) :
    (revHadamard R k (2 ^ k)).det =
      (if k = 1 ∨ k = 2 then (-1 : R) else 1) * (2 : R) ^ (k * 2 ^ (k - 1)) := by
  rw [revHadamard_full_eq_submatrix, Matrix.det_permute, det_hadamard, sign_bitrevPerm]
  by_cases h1 : k = 1
  · subst h1; simp
  · by_cases h2 : k = 2
    · subst h2; simp
    · simp [h1, h2]

theorem map_revHadamard {R : Type*} [CommRing R] (k m : ℕ) :
    (Int.castRingHom R).mapMatrix (revHadamard ℤ k m) = revHadamard R k m := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, revHadamard]

/-- Cofactor-size (`m = 2^k - 1`) bit-reversed Hadamard determinant over `ℚ`. -/
theorem det_revHadamard_sub_one_rat (k : ℕ) (hk : 1 ≤ k) :
    (revHadamard ℚ k (2 ^ k - 1)).det =
      (if k = 1 then (1 : ℚ) else if k = 2 then -1 else (-1 : ℚ) ^ k) *
        (2 : ℚ) ^ (k * 2 ^ (k - 1) - k) := by
  set H := revHadamard ℚ k (2 ^ k)
  -- H * Hᵀ = (2^k) • 1 (follows from hadamard_mul_transpose since bitrevPerm is a permutation)
  have hH_orth : H * H.transpose = ((2 ^ k : ℕ) : ℚ) • (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℚ) := by
    have h1 := hadamard_mul_transpose ℚ k
    ext i j
    simp only [H, revHadamard_full_eq_submatrix, Matrix.mul_apply, Matrix.submatrix_apply,
      Matrix.transpose_apply, id_eq, Matrix.smul_apply, Matrix.one_apply]
    have hij := congrArg (fun M => M (bitrevPerm k i) (bitrevPerm k j)) h1
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      (bitrevPerm k).injective.eq_iff] using hij
  -- Multiply H * adjugate H = det H • 1 on the left by Hᵀ? No: multiply H * Hᵀ = 2^k • 1 on left by adjugate H!
  -- Wait: adjugate H * H = det H • 1, so adjugate H * (H * Hᵀ) = det H • Hᵀ = (2^k) • adjugate H!
  have hadj_eq : ((2 ^ k : ℕ) : ℚ) • Matrix.adjugate H = H.det • H.transpose := by
    calc ((2 ^ k : ℕ) : ℚ) • Matrix.adjugate H
        = Matrix.adjugate H * (((2 ^ k : ℕ) : ℚ) • (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℚ)) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
      _ = Matrix.adjugate H * (H * H.transpose) := by rw [hH_orth]
      _ = (Matrix.adjugate H * H) * H.transpose := by rw [Matrix.mul_assoc]
      _ = (H.det • (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℚ)) * H.transpose := by
          rw [Matrix.adjugate_mul]
      _ = H.det • H.transpose := by rw [Matrix.smul_mul, Matrix.one_mul]
  -- Evaluate at (last, last)!
  have hpos : 0 < 2 ^ k := by positivity
  set last : Fin (2 ^ k) := ⟨2 ^ k - 1, by omega⟩
  have hpt := congrArg (fun M => M last last) hadj_eq
  simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at hpt
  -- Compute H last last = (-1)^k
  have hH_last : H last last = (-1 : ℚ) ^ k := by
    simp only [H, revHadamard, Matrix.of_apply, last, bitrevNat_allOnes, Nat.and_self]
    have hpop : popcntK k (2 ^ k - 1) = k := by
      unfold popcntK
      have hfilt : (Finset.range k).filter (fun u => (2 ^ k - 1).testBit u = true) = Finset.range k := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
        intro hu
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have hpow : 2 ^ k = 2 ^ u * (2 * 2 ^ (k - 1 - u)) := by
          have : k = u + 1 + (k - 1 - u) := by omega
          conv_lhs => rw [this, pow_add, pow_add, pow_one]
          ac_rfl
        have hpos_u : 0 < 2 ^ u := by positivity
        have hpos_rem : 0 < 2 ^ (k - 1 - u) := by positivity
        have hdiv : (2 ^ k - 1) / 2 ^ u = 2 * 2 ^ (k - 1 - u) - 1 := by
          have h1 : 2 ^ k - 1 = (2 ^ u - 1) + 2 ^ u * (2 * 2 ^ (k - 1 - u) - 1) := by
            have : 1 ≤ 2 * 2 ^ (k - 1 - u) := by omega
            calc 2 ^ k - 1 = 2 ^ u * (2 * 2 ^ (k - 1 - u)) - 1 := by rw [hpow]
              _ = 2 ^ u * ((2 * 2 ^ (k - 1 - u) - 1) + 1) - 1 := by congr 2; omega
              _ = (2 ^ u - 1) + 2 ^ u * (2 * 2 ^ (k - 1 - u) - 1) := by ring_nf; omega
          rw [h1, Nat.add_mul_div_left _ _ hpos_u, Nat.div_eq_of_lt (by omega), zero_add]
        rw [hdiv]
        have : (2 * 2 ^ (k - 1 - u) - 1) % 2 = 1 := by omega
        simp [this]
      rw [hfilt, Finset.card_range]
    rw [hpop]
  -- Compute adjugate H last last = det(revHadamard ℚ k (2^k - 1))!
  have hadj_last : Matrix.adjugate H last last = (revHadamard ℚ k (2 ^ k - 1)).det := by
    have hN : 2 ^ k = (2 ^ k - 1) + 1 := by omega
    let e : Fin (2 ^ k - 1) ⊕ Fin 1 ≃ Fin (2 ^ k) := finSumFinEquiv.trans (finCongr hN.symm)
    rw [Matrix.adjugate_apply]
    set U := H.updateRow last (Pi.single last 1)
    have hsub :
        U.submatrix e e =
        Matrix.fromBlocks (revHadamard ℚ k (2 ^ k - 1))
          (Matrix.of fun i _ => H (e (Sum.inl i)) last)
          0 (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
      ext i j
      cases i with
      | inl i =>
        have hi_ne : e (Sum.inl i) ≠ last := by
          intro h; have := congrArg Fin.val h; simp [e, last] at this; omega
        cases j with
        | inl j =>
          simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, U,
            Matrix.updateRow_ne hi_ne, H, revHadamard, Matrix.of_apply]
          simp [e]
        | inr j =>
          have hj_eq : e (Sum.inr j) = last := by
            ext; simp [e, last]
          simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, U,
            Matrix.updateRow_ne hi_ne, Matrix.of_apply, hj_eq]
      | inr i =>
        have hi_eq : e (Sum.inr i) = last := by
          ext; simp [e, last]
        cases j with
        | inl j =>
          have hj_ne : e (Sum.inl j) ≠ last := by
            intro h; have := congrArg Fin.val h; simp [e, last] at this; omega
          simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, U, hi_eq,
            Matrix.updateRow_self, Pi.single_eq_of_ne hj_ne, Matrix.zero_apply]
        | inr j =>
          have hj_eq : e (Sum.inr j) = last := by
            ext; simp [e, last]
          simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, U, hi_eq, hj_eq,
            Matrix.updateRow_self, Pi.single_eq_same]
          fin_cases i; fin_cases j
          simp only [Matrix.one_apply_eq]
    rw [← Matrix.det_submatrix_equiv_self e U, hsub, Matrix.det_fromBlocks_zero₂₁,
        Matrix.det_one, mul_one]
  -- Combine and cancel 2^k ≠ 0!
  rw [hadj_last, hH_last, det_revHadamard_full ℚ k] at hpt
  have h2k_ne : ((2 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
  have hexp : k ≤ k * 2 ^ (k - 1) := by
    have : 0 < 2 ^ (k - 1) := by positivity
    exact Nat.le_mul_of_pos_right k this
  have h2pow : (2 : ℚ) ^ (k * 2 ^ (k - 1)) = ((2 ^ k : ℕ) : ℚ) * (2 : ℚ) ^ (k * 2 ^ (k - 1) - k) := by
    push_cast
    rw [← pow_add, Nat.add_sub_of_le hexp]
  rw [h2pow] at hpt
  have hcomb : ((2 ^ k : ℕ) : ℚ) * (revHadamard ℚ k (2 ^ k - 1)).det =
      ((2 ^ k : ℕ) : ℚ) *
        ((if k = 1 then (1 : ℚ) else if k = 2 then -1 else (-1 : ℚ) ^ k) *
          (2 : ℚ) ^ (k * 2 ^ (k - 1) - k)) := by
    rw [hpt]
    by_cases h1 : k = 1
    · subst h1; norm_num
    · by_cases h2 : k = 2
      · subst h2; norm_num
      · simp only [h1, h2, or_self, ↓reduceIte]; ring
  exact mul_left_cancel₀ h2k_ne hcomb

/-- Cofactor-size (`m = 2^k - 1`) bit-reversed Hadamard determinant over ANY commutative ring `R`. -/
theorem det_revHadamard_sub_one (R : Type*) [CommRing R] (k : ℕ) (hk : 1 ≤ k) :
    (revHadamard R k (2 ^ k - 1)).det =
      (if k = 1 then (1 : R) else if k = 2 then -1 else (-1 : R) ^ k) *
        (2 : R) ^ (k * 2 ^ (k - 1) - k) := by
  have hint : (revHadamard ℤ k (2 ^ k - 1)).det =
      (if k = 1 then (1 : ℤ) else if k = 2 then -1 else (-1 : ℤ) ^ k) *
        (2 : ℤ) ^ (k * 2 ^ (k - 1) - k) := by
    apply Int.cast_injective (α := ℚ)
    have hmap : ((revHadamard ℤ k (2 ^ k - 1)).det : ℚ) = (revHadamard ℚ k (2 ^ k - 1)).det := by
      calc ((revHadamard ℤ k (2 ^ k - 1)).det : ℚ)
          = (Int.castRingHom ℚ) (revHadamard ℤ k (2 ^ k - 1)).det := rfl
        _ = ((Int.castRingHom ℚ).mapMatrix (revHadamard ℤ k (2 ^ k - 1))).det :=
            RingHom.map_det (Int.castRingHom ℚ) _
        _ = (revHadamard ℚ k (2 ^ k - 1)).det := by rw [map_revHadamard]
    rw [hmap, det_revHadamard_sub_one_rat k hk]
    split_ifs <;> push_cast <;> rfl
  have h := congrArg (Int.castRingHom R) hint
  rw [RingHom.map_det, map_revHadamard] at h
  rw [h]
  split_ifs <;> simp

/-- Gap vanishing: for every `2 ≤ m ≤ 2^k - 2` and every commutative ring `R`,
`det(revHadamard R k m) = 0`. -/
theorem det_revHadamard_gap (R : Type*) [CommRing R] (k m : ℕ)
    (hlo : 2 ≤ m) (hhi : m ≤ 2 ^ k - 2) :
    (revHadamard R k m).det = 0 := by
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk1 : k ≤ 1 := by omega
    interval_cases k <;> omega
  by_cases hhalf : m ≤ 2 ^ (k - 1)
  · -- Case 1: m ≤ 2^(k - 1): row 0 equals row 1 on all columns j < m!
    let r0 : Fin m := ⟨0, by omega⟩
    let r1 : Fin m := ⟨1, by omega⟩
    have hne : r0 ≠ r1 := by intro h; have := congrArg Fin.val h; simp [r0, r1] at this
    refine Matrix.det_zero_of_row_eq hne ?_
    ext j
    simp only [revHadamard, Matrix.of_apply, r0, r1, bitrevNat_zero, bitrevNat_one k (by omega),
      Nat.zero_and]
    have hj_lt : j.1 < 2 ^ (k - 1) := lt_of_lt_of_le j.2 hhalf
    have hand : 2 ^ (k - 1) &&& j.1 = 0 := by
      rw [Nat.and_comm]
      simpa using and_eq_zero_of_lt_two_pow_mul (b := 1) hj_lt
    rw [hand]
  · -- Case 2: 2^(k - 1) < m ≤ 2^k - 2: rows 0..2^(k-1)-1 with weights (-1)^popcnt(r) sum to 0!
    have hhalf_lt : 2 ^ (k - 1) < m := Nat.not_le.mp hhalf
    let i0 : Fin m := ⟨0, by omega⟩
    let v : Fin m → R := fun r => if r.1 < 2 ^ (k - 1) then (-1 : R) ^ popcntK (k - 1) r.1 else 0
    have hv0 : v i0 = 1 := by
      have hpos : 0 < 2 ^ (k - 1) := by positivity
      simp [v, i0, hpos, popcntK]
    -- Unimodular row-operation matrix E replacing row 0 by v (det = v 0 = 1)
    let E : Matrix (Fin m) (Fin m) R :=
      Matrix.of fun i j => if i = i0 then v j else if i = j then 1 else 0
    have hE_det : E.det = 1 := by
      have htri : E.BlockTriangular id := by
        intro i j hij
        have hne : i ≠ j := ne_of_gt hij
        have hi0 : i ≠ i0 := by intro h; subst h; exact Nat.not_lt_zero _ hij
        simp [E, hi0, hne]
      rw [Matrix.det_of_isUpperTriangular htri]
      refine Finset.prod_eq_one fun i _ => ?_
      by_cases hi : i = i0
      · subst hi; simp [E, hv0]
      · simp [E, hi]
    -- Show row i0 of (E * revHadamard R k m) is identically 0!
    have hrow0 : ∀ j : Fin m, (E * revHadamard R k m) i0 j = 0 := by
      intro j
      simp only [Matrix.mul_apply, E, Matrix.of_apply, ↓reduceIte, v, revHadamard]
      -- Since j < m ≤ 2^k - 2, among the top (k - 1) bits {1, ..., k - 1} of j, at least one bit u0 is 0!
      have hj_le : j.1 ≤ 2 ^ k - 3 := by omega
      have hex_zero : ∃ u0, 1 ≤ u0 ∧ u0 < k ∧ j.1.testBit u0 = false := by
        by_contra hall
        push Not at hall
        -- If all bits 1..k-1 of j are 1, then j ≥ ∑_{u=1}^{k-1} 2^u = 2^k - 2!
        have hge : 2 ^ k - 2 ≤ j.1 := by
          have hdiv_ge : 2 ^ (k - 1) - 1 ≤ j.1 / 2 := by
            have hbit : ∀ r < k - 1, (j.1 / 2).testBit r = true := by
              intro r hr
              rw [← Nat.testBit_succ]
              have h1 := hall (r + 1) (by omega) (by omega)
              cases h : j.1.testBit (r + 1)
              · exact absurd h h1
              · rfl
            -- Any number whose low (k-1) bits are all 1 is ≥ 2^(k-1) - 1!
            have hall1 : ∀ t n : ℕ, (∀ r < t, n.testBit r = true) → 2 ^ t - 1 ≤ n := by
              intro t
              induction t with
              | zero => intro n _; simp
              | succ t iht =>
                intro n hn
                have h0 := hn 0 (by omega)
                rw [Nat.testBit_zero] at h0
                have hmod : n % 2 = 1 := by simpa using h0
                have hdiv := iht (n / 2) (fun r hr => by rw [← Nat.testBit_succ]; exact hn (r + 1) (by omega))
                have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ, mul_comm]
                have hpos_t : 0 < 2 ^ t := by positivity
                omega
            exact hall1 (k - 1) (j.1 / 2) hbit
          have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
            have : k = (k - 1) + 1 := by omega
            conv_lhs => rw [this, pow_succ, mul_comm]
          omega
        omega
      rcases hex_zero with ⟨u0, hu0_ge, hu0_lt, hj_u0⟩
      -- Bit position in r corresponding to bit u0 in bitrevNat k r is d0 = k - 1 - u0 < k - 1!
      set d0 := k - 1 - u0
      have hd0_lt : d0 < k - 1 := by omega
      -- Restrict sum to Fin (2^(k-1))
      have hrestrict :
          (∑ r : Fin m, (if r.1 < 2 ^ (k - 1) then (-1 : R) ^ popcntK (k - 1) r.1 else 0) *
            (-1 : R) ^ popcntK k (bitrevNat k r.1 &&& j.1)) =
          ∑ r : Fin (2 ^ (k - 1)), (-1 : R) ^ popcntK (k - 1) r.1 *
            (-1 : R) ^ popcntK k (bitrevNat k r.1 &&& j.1) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin m => r.1 < 2 ^ (k - 1))]
        have hzero : ∑ r ∈ Finset.univ.filter (fun r : Fin m => ¬r.1 < 2 ^ (k - 1)),
            (if r.1 < 2 ^ (k - 1) then (-1 : R) ^ popcntK (k - 1) r.1 else 0) *
            (-1 : R) ^ popcntK k (bitrevNat k r.1 &&& j.1) = 0 :=
          Finset.sum_eq_zero fun r hr => by simp [(Finset.mem_filter.mp hr).2]
        rw [hzero, add_zero]
        refine Finset.sum_bij (fun r hr => ⟨r.1, (Finset.mem_filter.mp hr).2⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro a _ b _ h
          have hv : a.1 = b.1 := congrArg (fun x : Fin (2 ^ (k - 1)) => x.1) h
          exact Fin.ext hv
        · intro r _
          refine ⟨⟨r.1, lt_trans r.2 hhalf_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.2⟩, rfl⟩
        · intro r hr; simp [(Finset.mem_filter.mp hr).2]
      rw [hrestrict]
      -- Pair each r < 2^(k-1) with r ^^^ 2^d0 (involutive, flips popcntK (k-1) by ±1, leaves bitrevNat k r &&& j unchanged!)
      have hxor_lt : ∀ r : Fin (2 ^ (k - 1)), r.1 ^^^ 2 ^ d0 < 2 ^ (k - 1) := by
        intro r
        exact Nat.xor_lt_two_pow r.2 (Nat.pow_lt_pow_right (by omega) hd0_lt)
      let flip : Equiv.Perm (Fin (2 ^ (k - 1))) := {
        toFun := fun r => ⟨r.1 ^^^ 2 ^ d0, hxor_lt r⟩
        invFun := fun r => ⟨r.1 ^^^ 2 ^ d0, hxor_lt r⟩
        left_inv := fun r => Fin.ext (by
          apply Nat.eq_of_testBit_eq; intro u; simp [Nat.testBit_xor])
        right_inv := fun r => Fin.ext (by
          apply Nat.eq_of_testBit_eq; intro u; simp [Nat.testBit_xor])
      }
      have hflip_and : ∀ r : Fin (2 ^ (k - 1)),
          bitrevNat k (flip r).1 &&& j.1 = bitrevNat k r.1 &&& j.1 := by
        intro r
        apply Nat.eq_of_testBit_eq; intro u
        rw [Nat.testBit_and, Nat.testBit_and]
        by_cases hu : u < k
        · rw [testBit_bitrevNat k _ u hu, testBit_bitrevNat k _ u hu]
          simp only [flip, Equiv.coe_fn_mk, Nat.testBit_xor, Nat.testBit_two_pow]
          by_cases hu0 : u = u0
          · subst hu0; simp [hj_u0]
          · have hne : d0 ≠ k - 1 - u := by omega
            simp [hne]
        · have hge : k ≤ u := Nat.not_lt.mp hu
          rw [testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le (bitrevNat_lt _ _) (Nat.pow_le_pow_right (by omega) hge)),
              testBit_eq_false_of_lt_two_pow (lt_of_lt_of_le (bitrevNat_lt _ _) (Nat.pow_le_pow_right (by omega) hge))]
      have hflip_sgn : ∀ r : Fin (2 ^ (k - 1)),
          (-1 : R) ^ popcntK (k - 1) (flip r).1 = -(-1 : R) ^ popcntK (k - 1) r.1 := by
        intro r
        have hd_mem : d0 ∈ Finset.range (k - 1) := Finset.mem_range.mpr hd0_lt
        have hpop : ∀ x : ℕ, popcntK (k - 1) x =
            (if x.testBit d0 = true then 1 else 0) +
            (((Finset.range (k - 1)).erase d0).filter (fun u => x.testBit u = true)).card := by
          intro x
          unfold popcntK
          have h1 : (Finset.range (k - 1)).filter (fun u => x.testBit u = true) =
              if x.testBit d0 = true then
                insert d0 (((Finset.range (k - 1)).erase d0).filter (fun u => x.testBit u = true))
              else ((Finset.range (k - 1)).erase d0).filter (fun u => x.testBit u = true) := by
            split_ifs with h
            · ext u; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
              by_cases hu : u = d0
              · subst hu; simp [hd_mem, h]
              · simp [hu]
            · ext u; simp only [Finset.mem_filter, Finset.mem_erase]
              by_cases hu : u = d0
              · subst hu; simp [h]
              · simp [hu]
          rw [h1]
          split_ifs with h
          · rw [Finset.card_insert_of_notMem (by simp)]; omega
          · omega
        have herase_eq :
            (((Finset.range (k - 1)).erase d0).filter (fun u => (flip r).1.testBit u = true)) =
            (((Finset.range (k - 1)).erase d0).filter (fun u => r.1.testBit u = true)) := by
          refine Finset.filter_congr fun u hu => ?_
          have hne : d0 ≠ u := (Finset.ne_of_mem_erase hu).symm
          simp [flip, Nat.testBit_xor, hne]
        rw [hpop (flip r).1, hpop r.1, herase_eq]
        simp only [flip, Equiv.coe_fn_mk, Nat.testBit_xor, Nat.testBit_two_pow]
        cases h : r.1.testBit d0 <;> simp [pow_add]
      -- Split Fin (2^(k-1)) into bit d0 = false vs bit d0 = true; flip bijects them and negates each term!
      let S0 := Finset.univ.filter (fun r : Fin (2 ^ (k - 1)) => r.1.testBit d0 = false)
      let S1 := Finset.univ.filter (fun r : Fin (2 ^ (k - 1)) => r.1.testBit d0 = true)
      have hdisj : Disjoint S0 S1 := by
        rw [Finset.disjoint_left]; intro r hr0 hr1
        have h0 := (Finset.mem_filter.mp hr0).2
        have h1 := (Finset.mem_filter.mp hr1).2
        simp [h0] at h1
      have hunion : S0 ∪ S1 = Finset.univ := by
        ext r; simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        cases r.1.testBit d0 <;> simp
      rw [← hunion, Finset.sum_union hdisj]
      have hS1 :
          (∑ r ∈ S1, (-1 : R) ^ popcntK (k - 1) r.1 * (-1 : R) ^ popcntK k (bitrevNat k r.1 &&& j.1)) =
          -∑ r ∈ S0, (-1 : R) ^ popcntK (k - 1) r.1 * (-1 : R) ^ popcntK k (bitrevNat k r.1 &&& j.1) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_bij (fun r _ => flip r) ?_ ?_ ?_ ?_
        · intro r hr
          have h1 := (Finset.mem_filter.mp hr).2
          simp [S0, flip, Nat.testBit_xor, h1]
        · intro a _ b _ h; exact flip.injective h
        · intro r hr
          have h0 := (Finset.mem_filter.mp hr).2
          refine ⟨flip r, ?_, flip.left_inv r⟩
          simp [S1, flip, Nat.testBit_xor, h0]
        · intro r _
          rw [hflip_sgn r, hflip_and r]; ring
      rw [hS1, add_neg_cancel]
    have hdet0 : (E * revHadamard R k m).det = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero i0 hrow0
    rw [Matrix.det_mul, hE_det, one_mul] at hdet0
    exact hdet0

end ClmulLiftDeterminants
