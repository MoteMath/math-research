import Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

namespace F2BilinearHadamard

/-! ## Section 1: Pure Bitwise, Popcount, and `bitXorSum` Infrastructure -/

private theorem popcount_zero : popcount 0 = 0 := by unfold popcount; rfl

private theorem popcount_pos {n : ℕ} (hn : n ≠ 0) :
    popcount n = n % 2 + popcount (n / 2) := by
  conv => lhs; unfold popcount
  simp [hn]

private theorem popcount_eq (n : ℕ) : popcount n = n % 2 + popcount (n / 2) := by
  by_cases hn : n = 0
  · subst hn; simp [popcount_zero]
  · exact popcount_pos hn

private theorem popcount_xor_mod_two (x y : ℕ) :
    popcount (x ^^^ y) % 2 = (popcount x + popcount y) % 2 := by
  induction h : x + y using Nat.strongRecOn generalizing x y with
  | ind s ih =>
    by_cases h0 : x = 0 ∧ y = 0
    · rcases h0 with ⟨rfl, rfl⟩; simp [popcount_zero]
    · have hlt : x / 2 + y / 2 < s := by omega
      have ih' := ih (x / 2 + y / 2) hlt (x / 2) (y / 2) rfl
      have hxd : (x ^^^ y) / 2 = x / 2 ^^^ y / 2 := by
        apply Nat.eq_of_testBit_eq; intro j
        rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ]
      have hxm : (x ^^^ y) % 2 = (x % 2 + y % 2) % 2 := by
        have htb := Nat.testBit_xor x y 0
        simp only [Nat.testBit_zero] at htb
        have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
        have hy2 : y % 2 = 0 ∨ y % 2 = 1 := by omega
        rcases hx2 with hx2 | hx2 <;> rcases hy2 with hy2 | hy2 <;>
          (rw [hx2, hy2] at htb; by_cases h1 : (x ^^^ y) % 2 = 1 <;> (simp [h1] at htb; try omega))
      rw [popcount_eq (x ^^^ y), popcount_eq x, popcount_eq y, hxd, hxm]
      omega

private theorem popcount_two_pow_add (d m : ℕ) (hm : m < 2 ^ d) :
    popcount (2 ^ d + m) = 1 + popcount m := by
  induction d generalizing m with
  | zero =>
    have : m = 0 := by omega
    subst this
    rw [Nat.pow_zero, Nat.add_zero, popcount_zero, popcount_eq 1]
    simp [popcount_zero]
  | succ d ih =>
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
    rw [hpow] at hm ⊢
    rw [popcount_eq (2 * 2 ^ d + m), popcount_eq m]
    have hmod : (2 * 2 ^ d + m) % 2 = m % 2 := by omega
    have hdiv : (2 * 2 ^ d + m) / 2 = 2 ^ d + m / 2 := by omega
    rw [hmod, hdiv, ih (m / 2) (by omega)]
    omega

private theorem two_pow_add_eq_xor (d m : ℕ) (hm : m < 2 ^ d) :
    2 ^ d + m = 2 ^ d ^^^ m := by
  induction d generalizing m with
  | zero =>
    have : m = 0 := by omega
    subst this; rfl
  | succ d ih =>
    apply Nat.eq_of_testBit_eq; intro j
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
    cases j with
    | zero =>
      rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero, hpow]
      have h1 : (2 * 2 ^ d + m) % 2 = m % 2 := by omega
      have h2 : (2 * 2 ^ d) % 2 = 0 := by omega
      simp [h1, h2]
    | succ j =>
      rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, hpow]
      have h1 : (2 * 2 ^ d + m) / 2 = 2 ^ d + m / 2 := by omega
      have h2 : (2 * 2 ^ d) / 2 = 2 ^ d := by omega
      rw [h1, h2, ih (m / 2) (by omega), Nat.testBit_xor]

private theorem bitXorSumAux_eq (f : ℕ → Bool) (r n : ℕ) :
    bitXorSum.bitXorSumAux f r n =
      xor (if n % 2 = 1 then f r else false) (bitXorSum.bitXorSumAux f (r + 1) (n / 2)) := by
  by_cases hn : n = 0
  · subst hn; unfold bitXorSum.bitXorSumAux; simp
  · conv => lhs; unfold bitXorSum.bitXorSumAux
    simp [hn]

private theorem bitXorSumAux_zero (f : ℕ → Bool) (r : ℕ) :
    bitXorSum.bitXorSumAux f r 0 = false := by
  unfold bitXorSum.bitXorSumAux; rfl

private theorem bitXorSumAux_xor (f : ℕ → Bool) (r x y : ℕ) :
    bitXorSum.bitXorSumAux f r (x ^^^ y) =
      xor (bitXorSum.bitXorSumAux f r x) (bitXorSum.bitXorSumAux f r y) := by
  induction h : x + y using Nat.strongRecOn generalizing r x y with
  | ind s ih =>
    by_cases h0 : x = 0 ∧ y = 0
    · rcases h0 with ⟨rfl, rfl⟩; simp [bitXorSumAux_zero]
    · have hlt : x / 2 + y / 2 < s := by omega
      have ih' := ih (x / 2 + y / 2) hlt (r + 1) (x / 2) (y / 2) rfl
      have hxd : (x ^^^ y) / 2 = x / 2 ^^^ y / 2 := by
        apply Nat.eq_of_testBit_eq; intro j
        rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ]
      have hxm : (x ^^^ y) % 2 = (x % 2 + y % 2) % 2 := by
        have htb := Nat.testBit_xor x y 0
        simp only [Nat.testBit_zero] at htb
        have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
        have hy2 : y % 2 = 0 ∨ y % 2 = 1 := by omega
        rcases hx2 with hx2 | hx2 <;> rcases hy2 with hy2 | hy2 <;>
          (rw [hx2, hy2] at htb; by_cases h1 : (x ^^^ y) % 2 = 1 <;> (simp [h1] at htb; try omega))
      rw [bitXorSumAux_eq f r (x ^^^ y), bitXorSumAux_eq f r x, bitXorSumAux_eq f r y,
        hxd, hxm, ih']
      have hx2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hy2 : y % 2 = 0 ∨ y % 2 = 1 := by omega
      rcases hx2 with hx2 | hx2 <;> rcases hy2 with hy2 | hy2 <;>
        (simp [hx2, hy2]; try (cases f r <;> cases bitXorSum.bitXorSumAux f (r + 1) (x / 2) <;>
        cases bitXorSum.bitXorSumAux f (r + 1) (y / 2) <;> rfl))

private theorem bitXorSumAux_fun_xor (f g : ℕ → Bool) (r n : ℕ) :
    bitXorSum.bitXorSumAux (fun k => xor (f k) (g k)) r n =
      xor (bitXorSum.bitXorSumAux f r n) (bitXorSum.bitXorSumAux g r n) := by
  induction n using Nat.strongRecOn generalizing r with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; simp [bitXorSumAux_zero]
    · have ih' := ih (n / 2) (Nat.div_lt_self (by omega) (by omega)) (r + 1)
      rw [bitXorSumAux_eq _ r n, bitXorSumAux_eq f r n, bitXorSumAux_eq g r n, ih']
      by_cases h1 : n % 2 = 1 <;>
        (simp [h1]; try (cases f r <;> cases g r <;>
        cases bitXorSum.bitXorSumAux f (r + 1) (n / 2) <;>
        cases bitXorSum.bitXorSumAux g (r + 1) (n / 2) <;> rfl))

private theorem bitXorSumAux_false (r n : ℕ) :
    bitXorSum.bitXorSumAux (fun _ => false) r n = false := by
  induction n using Nat.strongRecOn generalizing r with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; exact bitXorSumAux_zero _ r
    · rw [bitXorSumAux_eq _ r n, ih (n / 2) (Nat.div_lt_self (by omega) (by omega)) (r + 1)]
      simp

private theorem bitXorSumAux_swap (A : ℕ → ℕ → Bool) (r s i j : ℕ) :
    bitXorSum.bitXorSumAux (fun r' => bitXorSum.bitXorSumAux (fun s' => A r' s') s j) r i =
      bitXorSum.bitXorSumAux (fun s' => bitXorSum.bitXorSumAux (fun r' => A r' s') r i) s j := by
  induction i using Nat.strongRecOn generalizing r with
  | ind i ih =>
    by_cases hi : i = 0
    · subst hi
      rw [bitXorSumAux_zero]
      have : (fun s' => bitXorSum.bitXorSumAux (fun r' => A r' s') r 0) = fun _ => false := by
        funext s'; exact bitXorSumAux_zero _ r
      rw [this, bitXorSumAux_false]
    · have ih' := ih (i / 2) (Nat.div_lt_self (by omega) (by omega)) (r + 1)
      rw [bitXorSumAux_eq _ r i, ih']
      have heq : (fun s' => bitXorSum.bitXorSumAux (fun r' => A r' s') r i) =
          fun s' => xor (if i % 2 = 1 then A r s' else false)
            (bitXorSum.bitXorSumAux (fun r' => A r' s') (r + 1) (i / 2)) := by
        funext s'; exact bitXorSumAux_eq (fun r' => A r' s') r i
      rw [heq, bitXorSumAux_fun_xor]
      by_cases h1 : i % 2 = 1
      · simp [h1]
      · simp [h1, bitXorSumAux_false]

private theorem bitXorSumAux_two_pow (f : ℕ → Bool) (r d : ℕ) :
    bitXorSum.bitXorSumAux f r (2 ^ d) = f (r + d) := by
  induction d generalizing r with
  | zero =>
    rw [Nat.pow_zero, bitXorSumAux_eq]
    simp [bitXorSumAux_zero]
  | succ d ih =>
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
    rw [hpow, bitXorSumAux_eq]
    have hmod : (2 * 2 ^ d) % 2 = 0 := by omega
    have hdiv : (2 * 2 ^ d) / 2 = 2 ^ d := by omega
    rw [hmod, hdiv]
    simp [ih (r + 1), show r + 1 + d = r + (d + 1) by omega]

private theorem bitXorSum_zero (f : ℕ → Bool) : bitXorSum f 0 = false :=
  bitXorSumAux_zero f 0

private theorem bitXorSum_xor (f : ℕ → Bool) (x y : ℕ) :
    bitXorSum f (x ^^^ y) = xor (bitXorSum f x) (bitXorSum f y) :=
  bitXorSumAux_xor f 0 x y

private theorem bitXorSum_two_pow (f : ℕ → Bool) (d : ℕ) :
    bitXorSum f (2 ^ d) = f d := by
  unfold bitXorSum; simpa using bitXorSumAux_two_pow f 0 d

private theorem bitXorSum_two_pow_add (f : ℕ → Bool) (d m : ℕ) (hm : m < 2 ^ d) :
    bitXorSum f (2 ^ d + m) = xor (f d) (bitXorSum f m) := by
  rw [two_pow_add_eq_xor d m hm, bitXorSum_xor, bitXorSum_two_pow]

private theorem bitXorSum_congr_lt (f g : ℕ → Bool) (d n : ℕ) (hn : n < 2 ^ d)
    (h : ∀ r, r < d → f r = g r) :
    bitXorSum f n = bitXorSum g n := by
  have aux : ∀ r d n, n < 2 ^ d → (∀ k, k < d → f (r + k) = g (r + k)) →
      bitXorSum.bitXorSumAux f r n = bitXorSum.bitXorSumAux g r n := by
    intro r d
    induction d generalizing r with
    | zero =>
      intro n hn _; have : n = 0 := by omega
      subst this; simp [bitXorSumAux_zero]
    | succ d ih =>
      intro n hn hf
      rw [bitXorSumAux_eq f r n, bitXorSumAux_eq g r n]
      have h0 : f r = g r := by simpa using hf 0 (by omega)
      have hlt : n / 2 < 2 ^ d := by rw [Nat.pow_succ] at hn; omega
      have hih := ih (r + 1) (n / 2) hlt (fun k hk => by
        have := hf (k + 1) (by omega)
        rwa [show r + (k + 1) = r + 1 + k by omega] at this)
      rw [h0, hih]
  exact aux 0 d n hn (fun k hk => by simpa using h k hk)

private theorem bitXorSum_congr {f g : ℕ → Bool} (h : ∀ r, f r = g r) (n : ℕ) :
    bitXorSum f n = bitXorSum g n :=
  bitXorSum_congr_lt f g n n Nat.lt_two_pow_self (fun r _ => h r)

private theorem f2Bilin_zero_left (A : ℕ → ℕ → Bool) (j : ℕ) :
    f2Bilin A 0 j = false := bitXorSum_zero _

private theorem f2Bilin_two_pow_two_pow (A : ℕ → ℕ → Bool) (r s : ℕ) :
    f2Bilin A (2 ^ r) (2 ^ s) = A r s := by
  unfold f2Bilin
  rw [bitXorSum_two_pow, bitXorSum_two_pow]

theorem f2Bilin_xor_left_right (A : ℕ → ℕ → Bool) :
    (∀ x y z, f2Bilin A (x ^^^ y) z = xor (f2Bilin A x z) (f2Bilin A y z)) ∧
    (∀ x y z, f2Bilin A x (y ^^^ z) = xor (f2Bilin A x y) (f2Bilin A x z)) ∧
    ((∀ r s, A r s = A s r) → ∀ i j, f2Bilin A i j = f2Bilin A j i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y z; exact bitXorSum_xor _ x y
  · intro x y z
    unfold f2Bilin
    have : (fun r => bitXorSum (fun s => A r s) (y ^^^ z)) =
        fun r => xor (bitXorSum (fun s => A r s) y) (bitXorSum (fun s => A r s) z) := by
      funext r; exact bitXorSum_xor _ y z
    rw [this]; exact bitXorSumAux_fun_xor _ _ 0 x
  · intro hsym i j
    unfold f2Bilin bitXorSum
    rw [bitXorSumAux_swap]
    have : (fun s' => bitXorSum.bitXorSumAux (fun r' => A r' s') 0 i) =
        fun s' => bitXorSum.bitXorSumAux (fun r' => A s' r') 0 i := by
      funext s'; congr 1; funext r'; exact hsym r' s'
    rw [this]

private theorem diagSign_two_pow_add {R : Type*} [CommRing R] (A : ℕ → ℕ → Bool)
    (d m : ℕ) (hm : m < 2 ^ d) :
    diagSign (R := R) A (2 ^ d + m) = diagSign A (2 ^ d) * diagSign A m := by
  unfold diagSign
  rw [bitXorSum_two_pow_add (fun r => A r r) d m hm, bitXorSum_two_pow]
  cases A d d <;> cases bitXorSum (fun r => A r r) m <;> simp

private theorem diagSign_zero {R : Type*} [Ring R] (A : ℕ → ℕ → Bool) :
    diagSign (R := R) A 0 = 1 := by
  unfold diagSign; simp [bitXorSum_zero]

/-! ## Section 2: Universal Integer Block Schur Elimination (Over Every `CommRing R`) -/

private theorem sign_bool_mul {R : Type*} [CommRing R] (x y : Bool) :
    (if xor x y then (-1 : R) else 1) = (if x then -1 else 1) * (if y then -1 else 1) := by
  cases x <;> cases y <;> simp

private theorem bilin_diff_eval {R : Type*} [CommRing R] (a b : R) (u v w : Bool) :
    (if xor u w then b else a) - (if xor v w then b else a) =
      if u = v then 0 else ((a - b) * (if u then -1 else 1)) * (if w then -1 else 1) := by
  cases u <;> cases v <;> cases w <;> simp

theorem bilinCharMat_det_block_elimination {R : Type*} [CommRing R]
    (A : ℕ → ℕ → Bool) (a b : R) (d m : ℕ) (hm : m ≤ 2 ^ d)
    (p : ℕ) (hp : p < 2 ^ d)
    (helim : ∀ j, j < 2 ^ d → f2Bilin A (2 ^ d) j = f2Bilin A p j) :
    (A d d = f2Bilin A p (2 ^ d) → 1 ≤ m →
      Matrix.det (bilinCharMat A a b (2 ^ d + m)) = 0) ∧
    (A d d ≠ f2Bilin A p (2 ^ d) →
      Matrix.det (bilinCharMat A a b (2 ^ d + m)) =
        Matrix.det (bilinCharMat A a b (2 ^ d)) *
        ((a - b) * diagSign A (2 ^ d)) ^ m *
        ((Finset.univ : Finset (Fin m)).prod fun i =>
          if xor (f2Bilin A i.1 (2 ^ d)) (f2Bilin A (2 ^ d) i.1) then (-1 : R) else 1) *
        Matrix.det (walshCharMat (R := R) A m)) := by
  have hbil := f2Bilin_xor_left_right A
  let e : Fin (2 ^ d) ⊕ Fin m ≃ Fin (2 ^ d + m) := finSumFinEquiv
  let M : Matrix (Fin (2 ^ d + m)) (Fin (2 ^ d + m)) R := bilinCharMat A a b (2 ^ d + m)
  let M' : Matrix (Fin (2 ^ d) ⊕ Fin m) (Fin (2 ^ d) ⊕ Fin m) R := M.submatrix e e
  have hdet_M : M.det = M'.det := (Matrix.det_submatrix_equiv_self e M).symm
  let A11 : Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) R := bilinCharMat A a b (2 ^ d)
  let A12 : Matrix (Fin (2 ^ d)) (Fin m) R :=
    Matrix.of fun i j => if f2Bilin A i.1 (2 ^ d + j.1) then b else a
  let A21 : Matrix (Fin m) (Fin (2 ^ d)) R :=
    Matrix.of fun i j => if f2Bilin A (2 ^ d + i.1) j.1 then b else a
  let A22 : Matrix (Fin m) (Fin m) R :=
    Matrix.of fun i j => if f2Bilin A (2 ^ d + i.1) (2 ^ d + j.1) then b else a
  have hM'_blocks : M' = Matrix.fromBlocks A11 A12 A21 A22 := by
    ext x y
    cases x with
    | inl i =>
      cases y with
      | inl j => simp [M', M, e, A11, bilinCharMat]
      | inr j => simp [M', M, e, A12, bilinCharMat]
    | inr i =>
      cases y with
      | inl j => simp [M', M, e, A21, bilinCharMat]
      | inr j => simp [M', M, e, A22, bilinCharMat]
  let P : Matrix (Fin m) (Fin (2 ^ d)) R :=
    Matrix.of fun i' i => if i.1 = (i'.1 ^^^ p) then 1 else 0
  let E : Matrix (Fin (2 ^ d) ⊕ Fin m) (Fin (2 ^ d) ⊕ Fin m) R :=
    Matrix.fromBlocks 1 0 (-P) 1
  have hdet_E : E.det = 1 := by
    dsimp only [E]
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, mul_one]
  have hP_mul : ∀ {α : Type} (X : Matrix (Fin (2 ^ d)) α R) (i' : Fin m) (j : α),
      (P * X) i' j = X ⟨i'.1 ^^^ p, Nat.xor_lt_two_pow (by omega) hp⟩ j := by
    intro α X i' j
    let idx : Fin (2 ^ d) := ⟨i'.1 ^^^ p, Nat.xor_lt_two_pow (by omega) hp⟩
    rw [Matrix.mul_apply, Finset.sum_eq_single idx]
    · simp [P, idx]
    · intro k _ hk
      have hne : k.1 ≠ i'.1 ^^^ p := fun h => hk (Fin.ext h)
      simp [P, hne]
    · intro hmem; exact absurd (Finset.mem_univ idx) hmem
  have hzero21 : -P * A11 + A21 = 0 := by
    ext i' j
    simp only [Matrix.add_apply, Matrix.neg_mul, Matrix.neg_apply, Matrix.zero_apply]
    rw [hP_mul A11 i' j]
    have hfeq : f2Bilin A (2 ^ d + i'.1) j.1 = f2Bilin A (i'.1 ^^^ p) j.1 := by
      rw [two_pow_add_eq_xor d i'.1 (by omega), hbil.1, hbil.1, helim j.1 j.2, Bool.xor_comm]
    simp [A11, A21, bilinCharMat, hfeq]
  let S : Matrix (Fin m) (Fin m) R := -P * A12 + A22
  have hEM' : E * M' = Matrix.fromBlocks A11 A12 0 S := by
    rw [hM'_blocks]; dsimp only [E, S]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, hzero21]
  have hdet_prod : M.det = A11.det * S.det := by
    rw [hdet_M, ← one_mul M'.det, ← hdet_E, ← Matrix.det_mul, hEM', Matrix.det_fromBlocks_zero₂₁]
  have hS_entry : ∀ (i' j' : Fin m),
      S i' j' = if A d d = f2Bilin A p (2 ^ d) then 0
        else ((a - b) * diagSign A (2 ^ d)) *
          (if f2Bilin A i'.1 (2 ^ d) then (-1 : R) else 1) *
          (if f2Bilin A i'.1 j'.1 then (-1 : R) else 1) *
          (if f2Bilin A (2 ^ d) j'.1 then (-1 : R) else 1) := by
    intro i' j'
    dsimp only [S]
    simp only [Matrix.add_apply, Matrix.neg_mul, Matrix.neg_apply]
    rw [hP_mul A12 i' j']
    dsimp only [A22, A12, Matrix.of_apply]
    have h1 : f2Bilin A (2 ^ d + i'.1) (2 ^ d + j'.1) =
        xor (A d d) (xor (f2Bilin A i'.1 (2 ^ d)) (xor (f2Bilin A (2 ^ d) j'.1) (f2Bilin A i'.1 j'.1))) := by
      rw [two_pow_add_eq_xor d i'.1 (by omega), two_pow_add_eq_xor d j'.1 (by omega),
        hbil.1, hbil.2.1, hbil.2.1, f2Bilin_two_pow_two_pow]
      cases A d d <;> cases f2Bilin A i'.1 (2 ^ d) <;>
        cases f2Bilin A (2 ^ d) j'.1 <;> cases f2Bilin A i'.1 j'.1 <;> rfl
    have h2 : f2Bilin A (i'.1 ^^^ p) (2 ^ d + j'.1) =
        xor (f2Bilin A p (2 ^ d)) (xor (f2Bilin A i'.1 (2 ^ d)) (xor (f2Bilin A (2 ^ d) j'.1) (f2Bilin A i'.1 j'.1))) := by
      rw [two_pow_add_eq_xor d j'.1 (by omega), hbil.1, hbil.2.1, hbil.2.1, ← helim j'.1 (by omega)]
      cases f2Bilin A p (2 ^ d) <;> cases f2Bilin A i'.1 (2 ^ d) <;>
        cases f2Bilin A (2 ^ d) j'.1 <;> cases f2Bilin A i'.1 j'.1 <;> rfl
    rw [neg_add_eq_sub, h1, h2, bilin_diff_eval]
    by_cases hsing : A d d = f2Bilin A p (2 ^ d)
    · simp [hsing]
    · simp only [hsing, ↓reduceIte]
      unfold diagSign
      rw [bitXorSum_two_pow, sign_bool_mul, sign_bool_mul]
      ring
  refine ⟨?_, ?_⟩
  · intro hsing hm1
    have hS0 : S = 0 := by
      ext i' j'; rw [hS_entry i' j']; simp [hsing]
    rw [hdet_prod, hS0]
    have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    rw [Matrix.det_zero, mul_zero]
  · intro hns
    let c : R := (a - b) * diagSign A (2 ^ d)
    let dr : Fin m → R := fun i' => if f2Bilin A i'.1 (2 ^ d) then -1 else 1
    let dc : Fin m → R := fun j' => if f2Bilin A (2 ^ d) j'.1 then -1 else 1
    have hS_mat : S = c • (Matrix.diagonal dr * walshCharMat A m * Matrix.diagonal dc) := by
      ext i' j'
      rw [hS_entry i' j']
      simp only [hns, ↓reduceIte, Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal,
        Matrix.diagonal_mul, walshCharMat, bilinCharMat, Matrix.of_apply, c, dr, dc]
      ring
    rw [hdet_prod, hS_mat, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, Matrix.det_diagonal]
    have hprod_d : (Finset.univ.prod dr) * (Finset.univ.prod dc) =
        (Finset.univ : Finset (Fin m)).prod fun i =>
          if xor (f2Bilin A i.1 (2 ^ d)) (f2Bilin A (2 ^ d) i.1) then (-1 : R) else 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact (sign_bool_mul _ _).symm
    calc A11.det * (c ^ m * (Finset.univ.prod dr * (walshCharMat (R := R) A m).det * Finset.univ.prod dc))
        = A11.det * c ^ m * (Finset.univ.prod dr * Finset.univ.prod dc) * (walshCharMat (R := R) A m).det := by ring
      _ = A11.det * c ^ m *
          ((Finset.univ : Finset (Fin m)).prod fun i =>
            if xor (f2Bilin A i.1 (2 ^ d)) (f2Bilin A (2 ^ d) i.1) then (-1 : R) else 1) *
          (walshCharMat (R := R) A m).det := by rw [hprod_d]

/-! ## Section 3: Universal Symmetric Walsh & Two-Parameter `(a, b)` Determinant Laws -/

theorem walshCharMat_det_symmetric {R : Type*} [CommRing R]
    (A : ℕ → ℕ → Bool) (D : ℕ)
    (hsym : ∀ r s, A r s = A s r)
    (hpiv : ∀ d, d < D → ∃ p, p < 2 ^ d ∧
      (∀ j, j < 2 ^ d → f2Bilin A (2 ^ d) j = f2Bilin A p j) ∧
      A d d ≠ f2Bilin A p (2 ^ d)) :
    ∀ n, n ≤ 2 ^ D →
      Matrix.det (walshCharMat (R := R) A n) =
        (Finset.range n).prod fun k => diagSign A k * (2 : R) ^ popcount k := by
  have hbil_sym : ∀ i j, f2Bilin A i j = f2Bilin A j i := (f2Bilin_xor_left_right A).2.2 hsym
  induction D with
  | zero =>
    intro n hn
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · simp
    · simp [walshCharMat, bilinCharMat, f2Bilin_zero_left, diagSign_zero, popcount_zero]
  | succ D ih =>
    intro n hn
    have ih' := ih (fun d hd => hpiv d (by omega))
    by_cases hle : n ≤ 2 ^ D
    · exact ih' n hle
    · let m := n - 2 ^ D
      have hm_le : m ≤ 2 ^ D := by rw [Nat.pow_succ] at hn; omega
      have hn_eq : n = 2 ^ D + m := by omega
      rcases hpiv D (by omega) with ⟨p, hp, helim, hns⟩
      have hblk := (bilinCharMat_det_block_elimination (R := R) A 1 (-1) D m hm_le p hp helim).2 hns
      have hsym_prod : ((Finset.univ : Finset (Fin m)).prod fun i =>
          if xor (f2Bilin A i.1 (2 ^ D)) (f2Bilin A (2 ^ D) i.1) then (-1 : R) else 1) = 1 := by
        apply Finset.prod_eq_one; intro i _
        rw [hbil_sym i.1 (2 ^ D), Bool.xor_self]; rfl
      rw [hn_eq]
      change Matrix.det (bilinCharMat A (1 : R) (-1 : R) (2 ^ D + m)) = _
      rw [hblk, hsym_prod, mul_one]
      change (walshCharMat (R := R) A (2 ^ D)).det * ((1 - (-1 : R)) * diagSign A (2 ^ D)) ^ m *
        (walshCharMat (R := R) A m).det = _
      rw [ih' (2 ^ D) (le_refl _), ih' m hm_le, Finset.prod_range_add]
      have hfactor : ∀ k, k ∈ Finset.range m →
          diagSign (R := R) A (2 ^ D + k) * (2 : R) ^ popcount (2 ^ D + k) =
            ((1 - (-1 : R)) * diagSign A (2 ^ D)) * (diagSign A k * (2 : R) ^ popcount k) := by
        intro k hk
        have hklt : k < 2 ^ D := by have := Finset.mem_range.mp hk; omega
        rw [diagSign_two_pow_add A D k hklt, popcount_two_pow_add D k hklt, pow_add, pow_one]
        ring
      have hrhs : (Finset.range m).prod
          (fun k => diagSign (R := R) A (2 ^ D + k) * (2 : R) ^ popcount (2 ^ D + k)) =
          ((1 - (-1 : R)) * diagSign A (2 ^ D)) ^ m *
          (Finset.range m).prod (fun k => diagSign A k * (2 : R) ^ popcount k) := by
        rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      rw [hrhs]; ring

theorem bilinCharMat_det_symmetric {R : Type*} [CommRing R]
    (A : ℕ → ℕ → Bool) (a b : R) (D : ℕ)
    (hsym : ∀ r s, A r s = A s r)
    (hpiv : ∀ d, d < D → ∃ p, p < 2 ^ d ∧
      (∀ j, j < 2 ^ d → f2Bilin A (2 ^ d) j = f2Bilin A p j) ∧
      A d d ≠ f2Bilin A p (2 ^ d)) :
    ∀ n, 1 ≤ n → n ≤ 2 ^ D →
      Matrix.det (bilinCharMat A a b n) =
        a * (a - b) ^ (n - 1) *
          (Finset.Ico 1 n).prod fun k => diagSign A k * (2 : R) ^ (popcount k - 1) := by
  have hbil_sym : ∀ i j, f2Bilin A i j = f2Bilin A j i := (f2Bilin_xor_left_right A).2.2 hsym
  induction D with
  | zero =>
    intro n hn1 hn2
    have : n = 1 := by omega
    subst this
    simp [bilinCharMat, f2Bilin_zero_left]
  | succ D ih =>
    intro n hn1 hn2
    have ih' := ih (fun d hd => hpiv d (by omega))
    by_cases hle : n ≤ 2 ^ D
    · exact ih' n hn1 hle
    · let m := n - 2 ^ D
      have hm_le : m ≤ 2 ^ D := by rw [Nat.pow_succ] at hn2; omega
      have hn_eq : n = 2 ^ D + m := by omega
      rcases hpiv D (by omega) with ⟨p, hp, helim, hns⟩
      have hblk := (bilinCharMat_det_block_elimination (R := R) A a b D m hm_le p hp helim).2 hns
      have hsym_prod : ((Finset.univ : Finset (Fin m)).prod fun i =>
          if xor (f2Bilin A i.1 (2 ^ D)) (f2Bilin A (2 ^ D) i.1) then (-1 : R) else 1) = 1 := by
        apply Finset.prod_eq_one; intro i _
        rw [hbil_sym i.1 (2 ^ D), Bool.xor_self]; rfl
      have hW := walshCharMat_det_symmetric (R := R) A D hsym (fun d hd => hpiv d (by omega)) m hm_le
      rw [hn_eq, hblk, hsym_prod, mul_one, ih' (2 ^ D) (Nat.two_pow_pos D) (le_refl _), hW]
      have hsplit : Finset.Ico 1 (2 ^ D + m) = Finset.Ico 1 (2 ^ D) ∪ Finset.Ico (2 ^ D) (2 ^ D + m) := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_union]; have := Nat.two_pow_pos D; omega
      have hdisj : Disjoint (Finset.Ico 1 (2 ^ D)) (Finset.Ico (2 ^ D) (2 ^ D + m)) := by
        rw [Finset.disjoint_left]; intro k hk1 hk2
        simp only [Finset.mem_Ico] at hk1 hk2; omega
      rw [hsplit, Finset.prod_union hdisj]
      have hshift : (Finset.Ico (2 ^ D) (2 ^ D + m)).prod
          (fun k => diagSign (R := R) A k * (2 : R) ^ (popcount k - 1)) =
          (Finset.range m).prod (fun k => diagSign A (2 ^ D + k) * (2 : R) ^ (popcount (2 ^ D + k) - 1)) := by
        refine Finset.prod_bij (fun k _ => k - 2 ^ D) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_Ico] at hk; exact Finset.mem_range.mpr (by omega)
        · intro k1 hk1 k2 hk2 h; simp only [Finset.mem_Ico] at hk1 hk2; omega
        · intro k hk; simp only [Finset.mem_range] at hk
          exact ⟨2 ^ D + k, Finset.mem_Ico.mpr (by omega), by omega⟩
        · intro k hk; simp only [Finset.mem_Ico] at hk
          rw [show 2 ^ D + (k - 2 ^ D) = k by omega]
      rw [hshift]
      have hfactor : ∀ k, k ∈ Finset.range m →
          diagSign (R := R) A (2 ^ D + k) * (2 : R) ^ (popcount (2 ^ D + k) - 1) =
            diagSign A (2 ^ D) * (diagSign A k * (2 : R) ^ popcount k) := by
        intro k hk
        have hklt : k < 2 ^ D := by have := Finset.mem_range.mp hk; omega
        rw [diagSign_two_pow_add A D k hklt, popcount_two_pow_add D k hklt,
          show 1 + popcount k - 1 = popcount k by omega]
        ring
      have hrhs : (Finset.range m).prod
          (fun k => diagSign (R := R) A (2 ^ D + k) * (2 : R) ^ (popcount (2 ^ D + k) - 1)) =
          (diagSign A (2 ^ D)) ^ m *
          (Finset.range m).prod (fun k => diagSign A k * (2 : R) ^ popcount k) := by
        rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      rw [hrhs]
      have hexp : 2 ^ D + m - 1 = (2 ^ D - 1) + m := by have := Nat.two_pow_pos D; omega
      rw [hexp, pow_add, mul_pow]
      ring

/-! ## Section 4: Standard Walsh-Hadamard & Sierpinski-Lucas-Pascal All-`n` Laws -/

private theorem bitXorSum_const_true (n : ℕ) :
    bitXorSum (fun _ => true) n = decide (popcount n % 2 = 1) := by
  have aux : ∀ r n, bitXorSum.bitXorSumAux (fun _ => true) r n = decide (popcount n % 2 = 1) := by
    intro r n
    induction n using Nat.strongRecOn generalizing r with
    | ind n ih =>
      by_cases hn : n = 0
      · subst hn; simp [bitXorSumAux_zero, popcount_zero]
      · rw [bitXorSumAux_eq, popcount_eq n, ih (n / 2) (Nat.div_lt_self (by omega) (by omega)) (r + 1)]
        have hn2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
        have hp2 : popcount (n / 2) % 2 = 0 ∨ popcount (n / 2) % 2 = 1 := by omega
        rcases hn2 with hn2 | hn2 <;> rcases hp2 with hp2 | hp2 <;> (simp [hn2, hp2]; try omega)
  exact aux 0 n

theorem walshStandard_det {R : Type*} [CommRing R] (n : ℕ) :
    Matrix.det (walshCharMat (R := R) stdBitMat n) =
      (Finset.range n).prod fun k => (-2 : R) ^ popcount k := by
  have hsym : ∀ r s, stdBitMat r s = stdBitMat s r := by
    intro r s; unfold stdBitMat; simp [eq_comm]
  have hpiv : ∀ d, d < n → ∃ p, p < 2 ^ d ∧
      (∀ j, j < 2 ^ d → f2Bilin stdBitMat (2 ^ d) j = f2Bilin stdBitMat p j) ∧
      stdBitMat d d ≠ f2Bilin stdBitMat p (2 ^ d) := by
    intro d _
    refine ⟨0, Nat.two_pow_pos d, ?_, ?_⟩
    · intro j hj
      rw [f2Bilin_zero_left]; unfold f2Bilin
      rw [bitXorSum_two_pow]
      have h0 : bitXorSum (fun s => stdBitMat d s) j = bitXorSum (fun _ => false) j :=
        bitXorSum_congr_lt _ _ d j hj (fun s hs => by unfold stdBitMat; simp [show d ≠ s by omega])
      rw [h0]; exact bitXorSumAux_false 0 j
    · rw [f2Bilin_zero_left]; simp [stdBitMat]
  rw [walshCharMat_det_symmetric (R := R) stdBitMat n hsym hpiv n (le_of_lt Nat.lt_two_pow_self)]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold diagSign
  have hstd : (fun r => stdBitMat r r) = fun _ => true := by funext r; simp [stdBitMat]
  rw [hstd, bitXorSum_const_true]
  have hp : (-2 : R) ^ popcount k = (-1 : R) ^ popcount k * (2 : R) ^ popcount k := by
    rw [← mul_pow]; ring
  rw [hp]
  have hneg : (if decide (popcount k % 2 = 1) = true then (-1 : R) else 1) = (-1 : R) ^ popcount k := by
    by_cases h1 : popcount k % 2 = 1
    · simp only [h1, decide_true, ↓reduceIte]
      exact (Odd.neg_one_pow (Nat.odd_iff.mpr h1)).symm
    · have h0 : popcount k % 2 = 0 := by omega
      simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact (Even.neg_one_pow (Nat.even_iff.mpr h0)).symm
  rw [hneg]

/-! ### Exact All-`d` `𝔽₂`-Cholesky Pivot Proof for Sierpinski-Lucas-Pascal -/

private theorem land_sub_le {r d : ℕ} (h : (r &&& d) = r) : r ≤ d := by
  have : r &&& d ≤ d := Nat.and_le_right
  omega

private theorem sum_two_pow_lt (m : ℕ) : (Finset.range m).sum (fun k => 2 ^ k) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.pow_succ]
    generalize (Finset.range m).sum (fun k => 2 ^ k) = s at ih ⊢
    generalize 2 ^ m = p at ih ⊢
    omega

private theorem sierpinskiPivot_testBit (d r : ℕ) :
    (sierpinskiPivot d).testBit r = decide (r < d ∧ (r &&& d) = r) := by
  have hgen : ∀ (P : ℕ → Bool) (m r : ℕ),
      ((Finset.range m).sum fun k => if P k then 2 ^ k else 0).testBit r =
        if r < m then P r else false := by
    intro P m
    induction m with
    | zero => intro r; simp
    | succ m ih =>
      intro r
      rw [Finset.sum_range_succ]
      have hlt : ((Finset.range m).sum fun k => if P k then 2 ^ k else 0) < 2 ^ m := by
        have hle : ((Finset.range m).sum fun k => if P k then 2 ^ k else 0) ≤
            (Finset.range m).sum (fun k => 2 ^ k) :=
          Finset.sum_le_sum fun k _ => by cases P k <;> simp
        have hsum := sum_two_pow_lt m
        omega
      cases hPm : P m
      · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, ih r]
        by_cases hr : r < m
        · simp [hr, show r < m + 1 by omega]
        · by_cases hrm : r = m
          · subst hrm; simp [hPm]
          · simp [hr, show ¬ r < m + 1 by omega]
      · simp only [↓reduceIte]
        rw [add_comm, two_pow_add_eq_xor m _ hlt, Nat.testBit_xor, Nat.testBit_two_pow, ih r]
        by_cases hr : r < m
        · simp [hr, show m ≠ r by omega, show r < m + 1 by omega]
        · by_cases hrm : r = m
          · subst hrm; simp [hPm]
          · simp [hr, show m ≠ r by omega, show ¬ r < m + 1 by omega]
  have := hgen (fun k => decide ((k &&& d) = k)) d r
  unfold sierpinskiPivot
  simpa [decide_eq_true_eq] using this

private theorem sierpinskiPivot_lt (d : ℕ) : sierpinskiPivot d < 2 ^ d := by
  unfold sierpinskiPivot
  have hle : ((Finset.range d).sum fun r => if (r &&& d) = r then 2 ^ r else 0) ≤
      (Finset.range d).sum (fun r => 2 ^ r) :=
    Finset.sum_le_sum fun r _ => by split_ifs <;> [exact le_refl _; exact Nat.zero_le _]
  have hsum := sum_two_pow_lt d
  omega

private theorem bitXorSum_eq_card_mod_two (f : ℕ → Bool) (d n : ℕ) (hn : n < 2 ^ d) :
    bitXorSum f n = decide (((Finset.range d).filter (fun r => n.testBit r && f r)).card % 2 = 1) := by
  have aux : ∀ d r n, n < 2 ^ d →
      bitXorSum.bitXorSumAux f r n =
        decide (((Finset.range d).filter (fun k => n.testBit k && f (r + k))).card % 2 = 1) := by
    intro d
    induction d with
    | zero =>
      intro r n hn; have : n = 0 := by omega
      subst this; simp [bitXorSumAux_zero]
    | succ d ih =>
      intro r n hn
      rw [bitXorSumAux_eq f r n]
      have hlt : n / 2 < 2 ^ d := by rw [Nat.pow_succ] at hn; omega
      rw [ih (r + 1) (n / 2) hlt]
      have hcard : ((Finset.range (d + 1)).filter (fun k => n.testBit k && f (r + k))).card =
          (if n % 2 = 1 ∧ f r = true then 1 else 0) +
          ((Finset.range d).filter (fun k => (n / 2).testBit k && f (r + 1 + k))).card := by
        have hset : (Finset.range (d + 1)).filter (fun k => n.testBit k && f (r + k)) =
            (if n % 2 = 1 ∧ f r = true then {0} else ∅) ∪
            ((Finset.range d).filter (fun k => (n / 2).testBit k && f (r + 1 + k))).image (· + 1) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
          cases k with
          | zero =>
            simp only [Nat.testBit_zero, add_zero, Nat.zero_lt_succ, true_and,
              Nat.add_eq_zero_iff, one_ne_zero, and_false, exists_false, or_false]
            by_cases h1 : n % 2 = 1 <;> by_cases h2 : f r = true <;> simp [h1, h2]
          | succ k =>
            have h0 : ¬ (k + 1 ∈ (if n % 2 = 1 ∧ f r = true then ({0} : Finset ℕ) else ∅)) := by
              split_ifs <;> simp
            simp only [h0, false_or, Nat.add_right_cancel_iff, exists_eq_right,
              Nat.testBit_succ, show r + (k + 1) = r + 1 + k by omega,
              show k + 1 < d + 1 ↔ k < d by omega]
        rw [hset, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun _ _ h => by omega)]
        · congr 1; split_ifs <;> simp
        · rw [Finset.disjoint_left]; intro x hx1 hx2
          simp only [Finset.mem_image] at hx2
          rcases hx2 with ⟨y, _, rfl⟩
          split_ifs at hx1 <;> simp at hx1
      rw [hcard]
      generalize ((Finset.range d).filter (fun k => (n / 2).testBit k && f (r + 1 + k))).card = c
      by_cases h1 : n % 2 = 1 <;> cases hfr : f r <;> by_cases hc : c % 2 = 1 <;>
        (simp [h1, hc]; try omega)
  have h := aux d 0 n hn
  unfold bitXorSum
  simpa using h

private theorem subCount_mod_two (b d s : ℕ) :
    ((Finset.range (2 ^ b)).filter (fun r => (r &&& d) = r ∧ (r &&& s) = 0)).card % 2 = 1 ↔
      ∀ i, i < b → ¬ (d.testBit i = true ∧ s.testBit i = false) := by
  induction b generalizing d s with
  | zero =>
    simp only [Nat.pow_zero, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, iff_true]
    have h0 : (Finset.range 1).filter (fun r => (r &&& d) = r ∧ (r &&& s) = 0) = {0} := by
      ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · intro h; omega
      · rintro rfl; simp
    rw [h0]; simp
  | succ b ih =>
    have hsplit : ((Finset.range (2 ^ (b + 1))).filter (fun r => (r &&& d) = r ∧ (r &&& s) = 0)).card =
        (if d % 2 = 1 ∧ s % 2 = 0 then 2 else 1) *
          ((Finset.range (2 ^ b)).filter (fun r => (r &&& (d / 2)) = r ∧ (r &&& (s / 2)) = 0)).card := by
      let S0 := ((Finset.range (2 ^ b)).filter (fun r => (r &&& (d / 2)) = r ∧ (r &&& (s / 2)) = 0)).image (2 * ·)
      let S1 := ((Finset.range (2 ^ b)).filter (fun r => (r &&& (d / 2)) = r ∧ (r &&& (s / 2)) = 0)).image (fun r => 2 * r + 1)
      have hdisj : Disjoint S0 S1 := by
        rw [Finset.disjoint_left]; intro x hx0 hx1
        simp only [S0, S1, Finset.mem_image] at hx0 hx1
        rcases hx0 with ⟨a, _, rfl⟩; rcases hx1 with ⟨c, _, hc⟩; omega
      have hbit_and : ∀ r n : ℕ, (r &&& n) = r ↔
          (r % 2 = 1 → n % 2 = 1) ∧ ((r / 2) &&& (n / 2)) = r / 2 := by
        intro r n
        constructor
        · intro h
          refine ⟨?_, ?_⟩
          · intro hr1
            have h0 := congrArg (fun k => k.testBit 0) h
            rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero] at h0
            simp [hr1] at h0; exact h0
          · apply Nat.eq_of_testBit_eq; intro j
            have hj := congrArg (fun k => k.testBit (j + 1)) h
            rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, ← Nat.testBit_and] at hj
            exact hj
        · rintro ⟨h0, hhi⟩
          apply Nat.eq_of_testBit_eq; intro j
          cases j with
          | zero =>
            rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero]
            by_cases hr1 : r % 2 = 1
            · simp [hr1, h0 hr1]
            · simp [hr1]
          | succ j =>
            rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, ← Nat.testBit_and, hhi]
      have hbit_disj : ∀ r n : ℕ, (r &&& n) = 0 ↔
          ¬ (r % 2 = 1 ∧ n % 2 = 1) ∧ ((r / 2) &&& (n / 2)) = 0 := by
        intro r n
        constructor
        · intro h
          refine ⟨?_, ?_⟩
          · rintro ⟨hr1, hn1⟩
            have h0 := congrArg (fun k => k.testBit 0) h
            simp [hr1, hn1] at h0
          · apply Nat.eq_of_testBit_eq; intro j
            have hj := congrArg (fun k => k.testBit (j + 1)) h
            rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, ← Nat.testBit_and, Nat.zero_testBit] at hj
            rw [Nat.zero_testBit]; exact hj
        · rintro ⟨h0, hhi⟩
          apply Nat.eq_of_testBit_eq; intro j
          cases j with
          | zero =>
            rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero, Nat.zero_testBit]
            by_cases hr1 : r % 2 = 1 <;> by_cases hn1 : n % 2 = 1 <;> simp [hr1, hn1] at h0 ⊢
          | succ j =>
            rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, ← Nat.testBit_and, hhi,
              Nat.zero_testBit, Nat.zero_testBit]
      have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ]; omega
      by_cases hcond : d % 2 = 1 ∧ s % 2 = 0
      · have hset : (Finset.range (2 ^ (b + 1))).filter (fun r => (r &&& d) = r ∧ (r &&& s) = 0) = S0 ∪ S1 := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, S0, S1, Finset.mem_image, hpow]
          rw [hbit_and r d, hbit_disj r s]
          constructor
          · rintro ⟨hrlt, ⟨_, hsub⟩, ⟨_, hdj⟩⟩
            by_cases hrp : r % 2 = 0
            · left; exact ⟨r / 2, ⟨by omega, hsub, hdj⟩, by omega⟩
            · right; exact ⟨r / 2, ⟨by omega, hsub, hdj⟩, by omega⟩
          · rintro (⟨k, ⟨hklt, hsub, hdj⟩, rfl⟩ | ⟨k, ⟨hklt, hsub, hdj⟩, rfl⟩)
            · exact ⟨by omega, ⟨by omega, by simpa using hsub⟩, ⟨by omega, by simpa using hdj⟩⟩
            · refine ⟨by omega, ⟨fun _ => hcond.1, ?_⟩, ⟨fun h => by omega, ?_⟩⟩
              · simpa [show (2 * k + 1) / 2 = k by omega] using hsub
              · simpa [show (2 * k + 1) / 2 = k by omega] using hdj
        simp only [hcond, and_self, ↓reduceIte]
        rw [hset, Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ (fun _ _ h => by omega),
          Finset.card_image_of_injective _ (fun _ _ h => by omega)]
        omega
      · have hset : (Finset.range (2 ^ (b + 1))).filter (fun r => (r &&& d) = r ∧ (r &&& s) = 0) = S0 := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_range, S0, Finset.mem_image, hpow]
          rw [hbit_and r d, hbit_disj r s]
          constructor
          · rintro ⟨hrlt, ⟨h1, hsub⟩, ⟨h2, hdj⟩⟩
            have hr0 : r % 2 = 0 := by
              by_contra hne
              have hr1 : r % 2 = 1 := by omega
              have hd1 := h1 hr1
              have hs0 : s % 2 = 0 := by omega
              exact hcond ⟨hd1, hs0⟩
            exact ⟨r / 2, ⟨by omega, hsub, hdj⟩, by omega⟩
          · rintro ⟨k, ⟨hklt, hsub, hdj⟩, rfl⟩
            exact ⟨by omega, ⟨by omega, by simpa using hsub⟩, ⟨by omega, by simpa using hdj⟩⟩
        simp only [hcond, ↓reduceIte]
        rw [hset, Finset.card_image_of_injective _ (fun _ _ h => by omega), one_mul]
    rw [hsplit]
    by_cases hcond : d % 2 = 1 ∧ s % 2 = 0
    · simp only [hcond, and_self, ↓reduceIte, Nat.mul_mod_right, zero_ne_one, false_iff, not_forall, not_not]
      refine ⟨0, Nat.zero_lt_succ b, ?_, ?_⟩
      · simp [Nat.testBit_zero, hcond.1]
      · simp [Nat.testBit_zero, hcond.2]
    · simp only [hcond, ↓reduceIte, one_mul, ih (d / 2) (s / 2)]
      constructor
      · intro h i hi
        cases i with
        | zero =>
          rintro ⟨hd1, hs0⟩
          rw [Nat.testBit_zero] at hd1 hs0
          have hd1' : d % 2 = 1 := by simpa using hd1
          have hs0' : s % 2 = 0 := by
            have : s % 2 ≠ 1 := by simpa using hs0
            omega
          exact hcond ⟨hd1', hs0'⟩
        | succ i =>
          rw [Nat.testBit_succ, Nat.testBit_succ]
          exact h i (by omega)
      · intro h i hi
        have := h (i + 1) (by omega)
        rwa [Nat.testBit_succ, Nat.testBit_succ] at this

theorem sierpinskiBitMat_cholesky_pivots (d : ℕ) :
    sierpinskiPivot d < 2 ^ d ∧
    (∀ j, j < 2 ^ d → f2Bilin sierpinskiBitMat (2 ^ d) j = f2Bilin sierpinskiBitMat (sierpinskiPivot d) j) ∧
    sierpinskiBitMat d d ≠ f2Bilin sierpinskiBitMat (sierpinskiPivot d) (2 ^ d) := by
  have hlt := sierpinskiPivot_lt d
  have hcol : ∀ s, s ≤ d →
      f2Bilin sierpinskiBitMat (sierpinskiPivot d) (2 ^ s) =
        if s = d then !(sierpinskiBitMat d d) else sierpinskiBitMat d s := by
    intro s hsd
    unfold f2Bilin
    rw [bitXorSum_congr (fun r => bitXorSum_two_pow (fun t => sierpinskiBitMat r t) s),
      bitXorSum_eq_card_mod_two _ d (sierpinskiPivot d) hlt]
    have hflt_eq : (Finset.range d).filter (fun r => (sierpinskiPivot d).testBit r && sierpinskiBitMat r s) =
        ((Finset.range (2 ^ d)).filter (fun r => (r &&& d) = r ∧ (r &&& s) = 0)).erase d := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, sierpinskiPivot_testBit,
        sierpinskiBitMat, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨_, ⟨hrd, hsub⟩, hdj⟩
        exact ⟨by omega, Nat.lt_trans hrd Nat.lt_two_pow_self, hsub, hdj⟩
      · rintro ⟨hne, _, hsub, hdj⟩
        have hle := land_sub_le hsub
        exact ⟨by omega, ⟨by omega, hsub⟩, hdj⟩
    rw [hflt_eq]
    have hd_mem : d ∈ (Finset.range (2 ^ d)).filter (fun r => (r &&& d) = r ∧ (r &&& s) = 0) ↔
        sierpinskiBitMat d s = true := by
      simp [sierpinskiBitMat, Nat.lt_two_pow_self]
    have hcard_erase : (((Finset.range (2 ^ d)).filter (fun r => (r &&& d) = r ∧ (r &&& s) = 0)).erase d).card +
        (if sierpinskiBitMat d s then 1 else 0) =
        ((Finset.range (2 ^ d)).filter (fun r => (r &&& d) = r ∧ (r &&& s) = 0)).card := by
      by_cases hds : sierpinskiBitMat d s = true
      · simp only [hds, ↓reduceIte]
        exact Finset.card_erase_add_one (hd_mem.mpr hds)
      · simp [hds]
        exact congrArg Finset.card (Finset.erase_eq_of_notMem (fun hm => hds (hd_mem.mp hm)))
    by_cases heq : s = d
    · subst s
      simp only [↓reduceIte]
      have hodd : ((Finset.range (2 ^ d)).filter (fun r => (r &&& d) = r ∧ (r &&& d) = 0)).card % 2 = 1 := by
        rw [subCount_mod_two]; intro i _ ⟨h1, h2⟩; rw [h1] at h2; cases h2
      cases hdd : sierpinskiBitMat d d
      · simp only [hdd, Bool.false_eq_true, ↓reduceIte, add_zero] at hcard_erase
        simp only [Bool.not_false, decide_eq_true_eq]; omega
      · simp only [hdd, ↓reduceIte] at hcard_erase
        simp only [Bool.not_true, decide_eq_false_iff_not]; omega
    · simp only [heq, ↓reduceIte]
      have heven : ((Finset.range (2 ^ d)).filter (fun r => (r &&& d) = r ∧ (r &&& s) = 0)).card % 2 = 0 := by
        by_contra hne
        have hodd : ((Finset.range (2 ^ d)).filter (fun r => (r &&& d) = r ∧ (r &&& s) = 0)).card % 2 = 1 := by omega
        rw [subCount_mod_two] at hodd
        have hsub : (d &&& s) = d := by
          apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.testBit_and]
          by_cases hdi : d.testBit i = true
          · have hid : i < d := by
              by_contra hge
              have hlt2 : d < 2 ^ i :=
                Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega))
              rw [Nat.testBit_lt_two_pow hlt2] at hdi; cases hdi
            cases hsi : s.testBit i
            · exact absurd ⟨hdi, hsi⟩ (hodd i hid)
            · simp [hdi]
          · have hdif : d.testBit i = false := by cases h : d.testBit i <;> simp [h] at hdi ⊢
            simp [hdif]
        have hle := land_sub_le hsub
        omega
      cases hds : sierpinskiBitMat d s <;> simp [hds] at hcard_erase ⊢ <;> omega
  refine ⟨hlt, ?_, ?_⟩
  · intro j hj
    have hlin : ∀ (x y : ℕ), f2Bilin sierpinskiBitMat x y =
        bitXorSum (fun s => f2Bilin sierpinskiBitMat x (2 ^ s)) y := by
      intro x y
      unfold f2Bilin bitXorSum
      rw [bitXorSumAux_swap]
      congr 1; funext s
      have h1 : ∀ r', bitXorSum.bitXorSumAux (fun t => sierpinskiBitMat r' t) 0 (2 ^ s) =
          sierpinskiBitMat r' s := fun r' => by simpa using bitXorSumAux_two_pow (fun t => sierpinskiBitMat r' t) 0 s
      simp only [h1]
    rw [hlin (sierpinskiPivot d) j]
    unfold f2Bilin
    rw [bitXorSum_two_pow]
    exact bitXorSum_congr_lt _ _ d j hj (fun s hs => by
      have := hcol s (by omega)
      simp only [show s ≠ d by omega, ↓reduceIte] at this
      exact this.symm)
  · have := hcol d (le_refl d)
    simp only [↓reduceIte] at this
    rw [this]; cases sierpinskiBitMat d d <;> decide

theorem sierpinskiCharMat_det_all_n {R : Type*} [CommRing R] (n : ℕ) :
    Matrix.det (walshCharMat (R := R) sierpinskiBitMat n) =
      (-1 : R) ^ (n / 2) * (2 : R) ^ ((Finset.range n).sum popcount) := by
  have hsym : ∀ r s, sierpinskiBitMat r s = sierpinskiBitMat s r := by
    intro r s; unfold sierpinskiBitMat; rw [Nat.and_comm]
  have hpiv : ∀ d, d < n → ∃ p, p < 2 ^ d ∧
      (∀ j, j < 2 ^ d → f2Bilin sierpinskiBitMat (2 ^ d) j = f2Bilin sierpinskiBitMat p j) ∧
      sierpinskiBitMat d d ≠ f2Bilin sierpinskiBitMat p (2 ^ d) := fun d _ =>
    ⟨sierpinskiPivot d, sierpinskiBitMat_cholesky_pivots d⟩
  rw [walshCharMat_det_symmetric (R := R) sierpinskiBitMat n hsym hpiv n (le_of_lt Nat.lt_two_pow_self)]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hdiag : ∀ k, diagSign (R := R) sierpinskiBitMat k = if k % 2 = 1 then -1 else 1 := by
    intro k
    unfold diagSign
    have hbit0 : bitXorSum (fun r => sierpinskiBitMat r r) k = decide (k % 2 = 1) := by
      unfold bitXorSum
      rw [bitXorSumAux_eq]
      have hrest : bitXorSum.bitXorSumAux (fun r => sierpinskiBitMat r r) 1 (k / 2) = false := by
        have h0 : ∀ m n, 1 ≤ m → bitXorSum.bitXorSumAux (fun r => sierpinskiBitMat r r) m n = false := by
          intro m n hm
          induction n using Nat.strongRecOn generalizing m with
          | ind n ih =>
            by_cases hn : n = 0
            · subst hn; exact bitXorSumAux_zero _ m
            · rw [bitXorSumAux_eq, ih (n / 2) (Nat.div_lt_self (by omega) (by omega)) (m + 1) (by omega)]
              have hm0 : sierpinskiBitMat m m = false := by
                unfold sierpinskiBitMat; rw [Nat.and_self]; simp [show m ≠ 0 by omega]
              simp [hm0]
        exact h0 1 (k / 2) (by omega)
      rw [hrest]
      have h00 : sierpinskiBitMat 0 0 = true := by decide
      by_cases h1 : k % 2 = 1 <;> simp [h1, h00]
    rw [hbit0]
    by_cases h1 : k % 2 = 1 <;> simp [h1]
  rw [Finset.prod_congr rfl (fun k _ => hdiag k)]
  clear hpiv hsym hdiag
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    by_cases h1 : n % 2 = 1
    · simp only [h1, ↓reduceIte, show (n + 1) / 2 = n / 2 + 1 by omega, pow_succ]
    · simp only [h1, ↓reduceIte, show (n + 1) / 2 = n / 2 by omega, mul_one]

/-! ## Section 5: Conway Nimber Character Determinant Theorem (`n ≤ 256`) & Sharp Rank Collapse -/

private theorem nimMulLevel_lt (k a b : ℕ) (ha : a < 2 ^ (2 ^ k)) (hb : b < 2 ^ (2 ^ k)) :
    nimMulLevel k a b < 2 ^ (2 ^ k) := by
  induction k generalizing a b with
  | zero =>
    simp only [nimMulLevel, Nat.pow_zero, Nat.pow_one]
    have h1 : a % 2 ≤ 1 := by omega
    have h2 : b % 2 ≤ 1 := by omega
    have h3 : (a % 2) * (b % 2) ≤ 1 * 1 := Nat.mul_le_mul h1 h2
    omega
  | succ k ih =>
    simp only [nimMulLevel]
    have hhalf_pos : 1 ≤ 2 ^ k := Nat.two_pow_pos k
    have hbase_pos : 0 < 2 ^ (2 ^ k) := Nat.two_pow_pos (2 ^ k)
    have hpow2 : 2 ^ (2 ^ (k + 1)) = 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := by
      rw [Nat.pow_succ, ← Nat.pow_add]; congr 1; omega
    have ha0 : a % 2 ^ (2 ^ k) < 2 ^ (2 ^ k) := Nat.mod_lt a hbase_pos
    have hb0 : b % 2 ^ (2 ^ k) < 2 ^ (2 ^ k) := Nat.mod_lt b hbase_pos
    have ha1 : a / 2 ^ (2 ^ k) < 2 ^ (2 ^ k) := by rw [hpow2] at ha; exact Nat.div_lt_of_lt_mul ha
    have hb1 : b / 2 ^ (2 ^ k) < 2 ^ (2 ^ k) := by rw [hpow2] at hb; exact Nat.div_lt_of_lt_mul hb
    have hp0 := ih _ _ ha0 hb0
    have hp1 := ih _ _ ha1 hb1
    have hp2 := ih _ _ (Nat.xor_lt_two_pow ha0 ha1) (Nat.xor_lt_two_pow hb0 hb1)
    have hhalf_lt : 2 ^ (2 ^ k - 1) < 2 ^ (2 ^ k) := Nat.pow_lt_pow_right (by omega) (by omega)
    have hlo : (nimMulLevel k (a % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k) ^^^
        nimMulLevel k (nimMulLevel k (a / 2 ^ 2 ^ k) (b / 2 ^ 2 ^ k)) (2 ^ (2 ^ k - 1))) < 2 ^ (2 ^ k) :=
      Nat.xor_lt_two_pow hp0 (ih _ _ hp1 hhalf_lt)
    have hhi : (nimMulLevel k (a % 2 ^ 2 ^ k ^^^ a / 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k) ^^^
        nimMulLevel k (a % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k)) < 2 ^ (2 ^ k) :=
      Nat.xor_lt_two_pow hp2 hp0
    have hhi_mul : (nimMulLevel k (a % 2 ^ 2 ^ k ^^^ a / 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k) ^^^
        nimMulLevel k (a % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k)) * 2 ^ (2 ^ k) < 2 ^ (2 ^ (k + 1)) := by
      rw [hpow2]; exact Nat.mul_lt_mul_of_pos_right hhi hbase_pos
    exact Nat.xor_lt_two_pow hhi_mul (lt_of_lt_of_le hlo (by rw [hpow2]; exact Nat.le_mul_of_pos_left _ hbase_pos))

private theorem xor_mod_two_pow (x y m : ℕ) : (x ^^^ y) % 2 ^ m = (x % 2 ^ m) ^^^ (y % 2 ^ m) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < m <;> simp [hi]

private theorem xor_div_two_pow (x y m : ℕ) : (x ^^^ y) / 2 ^ m = (x / 2 ^ m) ^^^ (y / 2 ^ m) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_div_two_pow, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]

private theorem xor_mul_two_pow (x y m : ℕ) : (x ^^^ y) * 2 ^ m = (x * 2 ^ m) ^^^ (y * 2 ^ m) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.mul_comm (x ^^^ y) (2 ^ m), Nat.mul_comm x (2 ^ m), Nat.mul_comm y (2 ^ m),
    Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul]
  by_cases hi : m ≤ i
  · simp [hi, Nat.testBit_xor]
  · simp [hi]

private theorem nimMulLevel_xor_left (k a1 a2 b : ℕ) :
    nimMulLevel k (a1 ^^^ a2) b = nimMulLevel k a1 b ^^^ nimMulLevel k a2 b := by
  induction k generalizing a1 a2 b with
  | zero =>
    simp only [nimMulLevel]
    have hx := xor_mod_two_pow a1 a2 1
    simp only [Nat.pow_one] at hx
    rw [hx]
    have h1 : a1 % 2 = 0 ∨ a1 % 2 = 1 := by omega
    have h2 : a2 % 2 = 0 ∨ a2 % 2 = 1 := by omega
    have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases hb with hb | hb <;>
      simp [h1, h2, hb]
  | succ k ih =>
    simp only [nimMulLevel]
    rw [xor_mod_two_pow, xor_div_two_pow]
    have hmid : (a1 % 2 ^ 2 ^ k ^^^ a2 % 2 ^ 2 ^ k) ^^^ (a1 / 2 ^ 2 ^ k ^^^ a2 / 2 ^ 2 ^ k) =
        (a1 % 2 ^ 2 ^ k ^^^ a1 / 2 ^ 2 ^ k) ^^^ (a2 % 2 ^ 2 ^ k ^^^ a2 / 2 ^ 2 ^ k) := by
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_xor]
      cases (a1 % 2 ^ 2 ^ k).testBit i <;> cases (a2 % 2 ^ 2 ^ k).testBit i <;>
        cases (a1 / 2 ^ 2 ^ k).testBit i <;> cases (a2 / 2 ^ 2 ^ k).testBit i <;> rfl
    rw [hmid]
    have hp0 := ih (a1 % 2 ^ 2 ^ k) (a2 % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k)
    have hp1 := ih (a1 / 2 ^ 2 ^ k) (a2 / 2 ^ 2 ^ k) (b / 2 ^ 2 ^ k)
    have hp2 := ih (a1 % 2 ^ 2 ^ k ^^^ a1 / 2 ^ 2 ^ k) (a2 % 2 ^ 2 ^ k ^^^ a2 / 2 ^ 2 ^ k)
      (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k)
    have hlo_p1 := ih (nimMulLevel k (a1 / 2 ^ 2 ^ k) (b / 2 ^ 2 ^ k))
      (nimMulLevel k (a2 / 2 ^ 2 ^ k) (b / 2 ^ 2 ^ k)) (2 ^ (2 ^ k - 1))
    rw [hp0, hp1, hp2, hlo_p1]
    have hhi_eq : ((nimMulLevel k (a1 % 2 ^ 2 ^ k ^^^ a1 / 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k) ^^^
        nimMulLevel k (a2 % 2 ^ 2 ^ k ^^^ a2 / 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k)) ^^^
        (nimMulLevel k (a1 % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k) ^^^ nimMulLevel k (a2 % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k))) =
        (nimMulLevel k (a1 % 2 ^ 2 ^ k ^^^ a1 / 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k) ^^^
        nimMulLevel k (a1 % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k)) ^^^
        (nimMulLevel k (a2 % 2 ^ 2 ^ k ^^^ a2 / 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k) ^^^
        nimMulLevel k (a2 % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k)) := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_xor]
      generalize (nimMulLevel k (a1 % 2 ^ 2 ^ k ^^^ a1 / 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k)).testBit i = u1
      generalize (nimMulLevel k (a2 % 2 ^ 2 ^ k ^^^ a2 / 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k)).testBit i = u2
      generalize (nimMulLevel k (a1 % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k)).testBit i = v1
      generalize (nimMulLevel k (a2 % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k)).testBit i = v2
      cases u1 <;> cases u2 <;> cases v1 <;> cases v2 <;> rfl
    rw [hhi_eq, xor_mul_two_pow]
    apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_xor]
    generalize ((nimMulLevel k (a1 % 2 ^ 2 ^ k ^^^ a1 / 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k) ^^^
      nimMulLevel k (a1 % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k)) * 2 ^ 2 ^ k).testBit i = x1
    generalize ((nimMulLevel k (a2 % 2 ^ 2 ^ k ^^^ a2 / 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k) ^^^
      nimMulLevel k (a2 % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k)) * 2 ^ 2 ^ k).testBit i = x2
    generalize (nimMulLevel k (a1 % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k)).testBit i = y1
    generalize (nimMulLevel k (a2 % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k)).testBit i = y2
    generalize (nimMulLevel k (nimMulLevel k (a1 / 2 ^ 2 ^ k) (b / 2 ^ 2 ^ k)) (2 ^ (2 ^ k - 1))).testBit i = z1
    generalize (nimMulLevel k (nimMulLevel k (a2 / 2 ^ 2 ^ k) (b / 2 ^ 2 ^ k)) (2 ^ (2 ^ k - 1))).testBit i = z2
    cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> cases z1 <;> cases z2 <;> rfl

private theorem nimMulLevel_comm (k a b : ℕ) : nimMulLevel k a b = nimMulLevel k b a := by
  induction k generalizing a b with
  | zero => simp only [nimMulLevel, Nat.mul_comm]
  | succ k ih =>
    simp only [nimMulLevel]
    rw [ih (a % 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k), ih (a / 2 ^ 2 ^ k) (b / 2 ^ 2 ^ k),
      ih (a % 2 ^ 2 ^ k ^^^ a / 2 ^ 2 ^ k) (b % 2 ^ 2 ^ k ^^^ b / 2 ^ 2 ^ k)]

private theorem nimMulLevel_zero_left (k b : ℕ) : nimMulLevel k 0 b = 0 := by
  induction k generalizing b with
  | zero => simp [nimMulLevel]
  | succ k ih => simp [nimMulLevel, ih]

private theorem nimMul_pop_eq_f2Bilin (i j : ℕ) :
    decide (popcount (nimMul i j) % 2 = 1) = f2Bilin nimBitMat i j := by
  have hlin_left : ∀ (f : ℕ → Bool), f 0 = false →
      (∀ x y, f (x ^^^ y) = xor (f x) (f y)) →
      ∀ n, f n = bitXorSum (fun r => f (2 ^ r)) n := by
    intro f hf0 hfx n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hn : n = 0
      · subst hn; rw [hf0, bitXorSum_zero]
      · let d := Nat.log 2 n
        have hle : 2 ^ d ≤ n := Nat.pow_log_le_self 2 hn
        have hlt : n < 2 ^ (d + 1) := Nat.lt_pow_succ_log_self (by omega) n
        let m := n - 2 ^ d
        have hm_lt : m < 2 ^ d := by rw [Nat.pow_succ] at hlt; omega
        have hn_eq : n = 2 ^ d + m := by omega
        have hm_lt_n : m < n := by have := Nat.two_pow_pos d; omega
        rw [hn_eq, two_pow_add_eq_xor d m hm_lt, hfx, bitXorSum_xor, bitXorSum_two_pow, ih m hm_lt_n]
  have hL : decide (popcount (nimMul i j) % 2 = 1) =
      bitXorSum (fun r => decide (popcount (nimMul (2 ^ r) j) % 2 = 1)) i := by
    refine hlin_left (fun x => decide (popcount (nimMul x j) % 2 = 1)) ?_ ?_ i
    · simp [nimMul, nimMulLevel_zero_left, popcount_zero]
    · intro x y
      unfold nimMul
      rw [nimMulLevel_xor_left, popcount_xor_mod_two]
      have h1 : popcount (nimMulLevel 3 x j) % 2 = 0 ∨ popcount (nimMulLevel 3 x j) % 2 = 1 := by omega
      have h2 : popcount (nimMulLevel 3 y j) % 2 = 0 ∨ popcount (nimMulLevel 3 y j) % 2 = 1 := by omega
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> (simp [h1, h2]; try omega)
  have hR : ∀ r, decide (popcount (nimMul (2 ^ r) j) % 2 = 1) =
      bitXorSum (fun s => nimBitMat r s) j := by
    intro r
    refine hlin_left (fun y => decide (popcount (nimMul (2 ^ r) y) % 2 = 1)) ?_ ?_ j
    · rw [nimMul, nimMulLevel_comm, nimMulLevel_zero_left]; simp [popcount_zero]
    · intro x y
      unfold nimMul
      rw [nimMulLevel_comm 3 (2 ^ r) (x ^^^ y), nimMulLevel_xor_left,
        nimMulLevel_comm 3 x (2 ^ r), nimMulLevel_comm 3 y (2 ^ r), popcount_xor_mod_two]
      have h1 : popcount (nimMulLevel 3 (2 ^ r) x) % 2 = 0 ∨ popcount (nimMulLevel 3 (2 ^ r) x) % 2 = 1 := by omega
      have h2 : popcount (nimMulLevel 3 (2 ^ r) y) % 2 = 0 ∨ popcount (nimMulLevel 3 (2 ^ r) y) % 2 = 1 := by omega
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> (simp [h1, h2]; try omega)
  rw [hL]
  unfold f2Bilin
  exact bitXorSum_congr hR i

private theorem nimBitMat_symm (r s : ℕ) : nimBitMat r s = nimBitMat s r := by
  unfold nimBitMat nimMul
  rw [nimMulLevel_comm]

-- Computable 8-bit popcount and bitXorSum for instant kernel `decide` certification on `Fin 8 × Fin 8`
private def popcount8 (n : ℕ) : ℕ :=
  (List.range 8).foldl (fun acc i => acc + (n / 2 ^ i) % 2) 0

private def nimBitMat8Fast (r s : ℕ) : Bool :=
  decide (popcount8 (nimMul (2 ^ r) (2 ^ s)) % 2 = 1)

private def nimPivot8 : Fin 8 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 2
  | ⟨6, _⟩ => 55
  | ⟨7, _⟩ => 110

private def bitXorSum8 (f : ℕ → Bool) (n : ℕ) : Bool :=
  (List.range 8).foldl (fun acc r => xor acc (if (n / 2 ^ r) % 2 = 1 then f r else false)) false

private theorem list_foldl_congr {α β : Type*} (l : List β) (init : α)
    (f g : α → β → α) (h : ∀ acc x, x ∈ l → f acc x = g acc x) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [h init hd (by simp)]
    exact ih _ (fun acc x hx => h acc x (by simp [hx]))

private theorem popcount_eq_popcount8 (n : ℕ) (hn : n < 256) : popcount n = popcount8 n := by
  have haux : ∀ k n, n < 2 ^ k →
      popcount n = (List.range k).foldl (fun acc i => acc + (n / 2 ^ i) % 2) 0 := by
    intro k
    induction k with
    | zero =>
      intro n hn; have : n = 0 := by omega
      subst this; simp [popcount_zero]
    | succ k ih =>
      intro n hn
      rw [popcount_eq n]
      have hlt : n / 2 < 2 ^ k := by rw [Nat.pow_succ] at hn; omega
      rw [ih (n / 2) hlt]
      have hrange : List.range (k + 1) = 0 :: (List.range k).map (· + 1) := List.range_succ_eq_map
      rw [hrange, List.foldl_cons, List.foldl_map]
      simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add]
      have hfold_add : ∀ (a : ℕ) (l : List ℕ) (g : ℕ → ℕ),
          l.foldl (fun acc i => acc + g i) a = a + l.foldl (fun acc i => acc + g i) 0 := by
        intro a l g
        induction l generalizing a with
        | nil => simp
        | cons hd tl iht =>
          simp only [List.foldl_cons, Nat.zero_add]
          rw [iht (a + g hd), iht (g hd)]; omega
      conv => rhs; rw [hfold_add]
      congr 1
      apply list_foldl_congr; intro acc i _
      have hdiv : n / 2 ^ (i + 1) = (n / 2) / 2 ^ i := by
        rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      rw [hdiv]
  simpa [popcount8] using haux 8 n hn

private theorem nimBitMat_eq_fast (r s : ℕ) (hr : r < 8) (hs : s < 8) :
    nimBitMat r s = nimBitMat8Fast r s := by
  unfold nimBitMat nimBitMat8Fast
  have hr256 : 2 ^ r < 2 ^ (2 ^ 3) := Nat.pow_lt_pow_right (by omega) hr
  have hs256 : 2 ^ s < 2 ^ (2 ^ 3) := Nat.pow_lt_pow_right (by omega) hs
  have hlt : nimMul (2 ^ r) (2 ^ s) < 256 := nimMulLevel_lt 3 (2 ^ r) (2 ^ s) hr256 hs256
  rw [popcount_eq_popcount8 _ hlt]

private theorem bitXorSum_eq_bitXorSum8 (f : ℕ → Bool) (n : ℕ) (hn : n < 256) :
    bitXorSum f n = bitXorSum8 f n := by
  have haux : ∀ (r : ℕ) (k : ℕ) (n : ℕ), n < 2 ^ k →
      bitXorSum.bitXorSumAux f r n =
        (List.range k).foldl (fun acc i => xor acc (if (n / 2 ^ i) % 2 = 1 then f (r + i) else false)) false := by
    intro r k
    induction k generalizing r with
    | zero =>
      intro n hn; have : n = 0 := by omega
      subst this; simp [bitXorSumAux_zero]
    | succ k ih =>
      intro n hn
      rw [bitXorSumAux_eq f r n]
      have hlt : n / 2 < 2 ^ k := by rw [Nat.pow_succ] at hn; omega
      rw [ih (r + 1) (n / 2) hlt]
      have hrange : List.range (k + 1) = 0 :: (List.range k).map (· + 1) := List.range_succ_eq_map
      rw [hrange, List.foldl_cons, List.foldl_map]
      simp only [Nat.pow_zero, Nat.div_one, add_zero, Bool.false_xor]
      have hfold_xor : ∀ (a : Bool) (l : List ℕ) (g : ℕ → Bool),
          l.foldl (fun acc i => xor acc (g i)) a = xor a (l.foldl (fun acc i => xor acc (g i)) false) := by
        intro a l g
        induction l generalizing a with
        | nil => simp
        | cons hd tl iht =>
          simp only [List.foldl_cons, Bool.false_xor]
          rw [iht (xor a (g hd)), iht (g hd)]
          cases a <;> cases g hd <;> cases tl.foldl (fun acc i => xor acc (g i)) false <;> rfl
      conv => rhs; rw [hfold_xor]
      congr 1
      apply list_foldl_congr; intro acc i _
      have hdiv : n / 2 ^ (i + 1) = (n / 2) / 2 ^ i := by
        rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      rw [hdiv, show r + (i + 1) = r + 1 + i by omega]
  simpa [bitXorSum, bitXorSum8] using haux 0 8 n hn

private theorem nim_pivots_certified :
    ∀ d : Fin 8,
      nimPivot8 d < 2 ^ d.1 ∧
      (∀ s : Fin 8, s.1 < d.1 →
        nimBitMat8Fast d.1 s.1 = bitXorSum8 (fun r => nimBitMat8Fast r s.1) (nimPivot8 d)) ∧
      nimBitMat8Fast d.1 d.1 ≠ bitXorSum8 (fun r => nimBitMat8Fast r d.1) (nimPivot8 d) := by
  decide

theorem nimCharMat_det_256 {R : Type*} [CommRing R] (a b : R) (n : ℕ)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 256) :
    Matrix.det (Matrix.of fun i j : Fin n =>
      if popcount (nimMul i.1 j.1) % 2 = 1 then (-1 : R) else (1 : R)) =
      (Finset.range n).prod (fun k => diagSign nimBitMat k * (2 : R) ^ popcount k) ∧
    Matrix.det (Matrix.of fun i j : Fin n =>
      if popcount (nimMul i.1 j.1) % 2 = 1 then b else a) =
      a * (a - b) ^ (n - 1) *
        (Finset.Ico 1 n).prod (fun k => diagSign nimBitMat k * (2 : R) ^ (popcount k - 1)) := by
  have hpiv : ∀ d, d < 8 → ∃ p, p < 2 ^ d ∧
      (∀ j, j < 2 ^ d → f2Bilin nimBitMat (2 ^ d) j = f2Bilin nimBitMat p j) ∧
      nimBitMat d d ≠ f2Bilin nimBitMat p (2 ^ d) := by
    intro d hd
    have hcert := nim_pivots_certified ⟨d, hd⟩
    have hp_lt : nimPivot8 ⟨d, hd⟩ < 2 ^ d := hcert.1
    have hp256 : nimPivot8 ⟨d, hd⟩ < 256 :=
      lt_of_lt_of_le hp_lt (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : d ≤ 8))
    have hsum_eq : ∀ s, s < 8 →
        bitXorSum (fun r => nimBitMat r s) (nimPivot8 ⟨d, hd⟩) =
          bitXorSum8 (fun r => nimBitMat8Fast r s) (nimPivot8 ⟨d, hd⟩) := by
      intro s hs
      rw [bitXorSum_congr_lt _ _ d (nimPivot8 ⟨d, hd⟩) hp_lt (fun r hr => nimBitMat_eq_fast r s (by omega) hs),
        bitXorSum_eq_bitXorSum8 _ _ hp256]
    refine ⟨nimPivot8 ⟨d, hd⟩, hp_lt, ?_, ?_⟩
    · intro j hj
      unfold f2Bilin
      rw [bitXorSum_two_pow]
      have hlin : bitXorSum (fun r => bitXorSum (fun s => nimBitMat r s) j) (nimPivot8 ⟨d, hd⟩) =
          bitXorSum (fun s => bitXorSum (fun r => nimBitMat r s) (nimPivot8 ⟨d, hd⟩)) j := by
        unfold bitXorSum; exact bitXorSumAux_swap nimBitMat 0 0 (nimPivot8 ⟨d, hd⟩) j
      rw [hlin]
      exact bitXorSum_congr_lt _ _ d j hj (fun s hs => by
        rw [nimBitMat_eq_fast d s hd (by omega), hsum_eq s (by omega)]
        exact hcert.2.1 ⟨s, by omega⟩ hs)
    · unfold f2Bilin
      rw [bitXorSum_congr (fun r => bitXorSum_two_pow (fun s => nimBitMat r s) d),
        nimBitMat_eq_fast d d hd hd, hsum_eq d hd]
      exact hcert.2.2
  have hmat_eq : ∀ (x y : R),
      (Matrix.of fun i j : Fin n => if popcount (nimMul i.1 j.1) % 2 = 1 then y else x) =
        bilinCharMat nimBitMat x y n := by
    intro x y; ext i j
    simp only [bilinCharMat, Matrix.of_apply, ← nimMul_pop_eq_f2Bilin i.1 j.1]
    by_cases h : popcount (nimMul i.1 j.1) % 2 = 1 <;> simp [h]
  refine ⟨?_, ?_⟩
  · rw [hmat_eq (1 : R) (-1 : R)]
    exact walshCharMat_det_symmetric (R := R) nimBitMat 8 nimBitMat_symm hpiv n hn2
  · rw [hmat_eq a b]
    exact bilinCharMat_det_symmetric (R := R) nimBitMat a b 8 nimBitMat_symm hpiv n hn1 hn2

theorem clmulBitMat_rank_collapse {R : Type*} [CommRing R] (a b : R) (n : ℕ) (hn : 3 ≤ n) :
    Matrix.det (bilinCharMat clmulBitMat a b n) = 0 := by
  have hrow : bilinCharMat clmulBitMat a b n ⟨1, by omega⟩ =
      bilinCharMat clmulBitMat a b n ⟨2, by omega⟩ := by
    ext j
    simp only [bilinCharMat, Matrix.of_apply]
    have h1 : f2Bilin clmulBitMat 1 j.1 = bitXorSum (fun s => clmulBitMat 0 s) j.1 := by
      unfold f2Bilin
      have := bitXorSum_two_pow (fun r => bitXorSum (fun s => clmulBitMat r s) j.1) 0
      simpa using this
    have h2 : f2Bilin clmulBitMat 2 j.1 = bitXorSum (fun s => clmulBitMat 1 s) j.1 := by
      unfold f2Bilin
      have := bitXorSum_two_pow (fun r => bitXorSum (fun s => clmulBitMat r s) j.1) 1
      simpa using this
    rw [h1, h2]; rfl
  have hne : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
    intro h; have h' := congrArg Fin.val h; dsimp only at h'; omega
  exact Matrix.det_zero_of_row_eq hne hrow

end F2BilinearHadamard
