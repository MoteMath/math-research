/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Paley32Mxfp4.Defs

/-!
# Paley-32 vs Sylvester-32: Zero Subgroup Collapse at `k = 4` and `k = 8`

Pure Lean 4 `Init` (zero Mathlib, zero `native_decide`) proofs of:
- Theorem 2 (`paley32_orthogonality_and_zero_k4_collapse`)
- Theorem 3 (`paley32_vs_sylvester32_k8_l4_reduction`)
-/

namespace Paley32Mxfp4

/-! ### 1. Finite-Sum Helpers for `Nat` and `Int` -/

theorem sumFinNat_congr {n : Nat} (f g : Fin n → Nat) (h : ∀ i, f i = g i) :
    sumFinNat n f = sumFinNat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFinNat]
    rw [ih _ _ (fun i => h i.castSucc), h (Fin.last k)]

theorem sumFinInt_congr {n : Nat} (f g : Fin n → Int) (h : ∀ i, f i = g i) :
    sumFinInt n f = sumFinInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFinInt]
    rw [ih _ _ (fun i => h i.castSucc), h (Fin.last k)]

theorem sumFinInt_add {n : Nat} (f g : Fin n → Int) :
    sumFinInt n (fun i => f i + g i) = sumFinInt n f + sumFinInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFinInt]
    rw [ih]
    omega

theorem sumFinNat_add {n : Nat} (f g : Fin n → Nat) :
    sumFinNat n (fun i => f i + g i) = sumFinNat n f + sumFinNat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFinNat]
    rw [ih]
    omega

theorem sumFinNat_zero (n : Nat) : sumFinNat n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumFinNat, ih]

theorem sumFinInt_zero (n : Nat) : sumFinInt n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumFinInt, ih]

theorem sumFinInt_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFinInt n (fun i => c * f i) = c * sumFinInt n f := by
  induction n with
  | zero => simp [sumFinInt]
  | succ k ih =>
    simp only [sumFinInt]
    rw [ih]
    grind

theorem sumFinInt_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    sumFinInt n (fun i => f i * c) = sumFinInt n f * c := by
  induction n with
  | zero => simp [sumFinInt]
  | succ k ih =>
    simp only [sumFinInt]
    rw [ih]
    grind

theorem sumFinInt_le {n : Nat} (f g : Fin n → Int) (h : ∀ i, f i ≤ g i) :
    sumFinInt n f ≤ sumFinInt n g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    simp only [sumFinInt]
    have h1 := ih _ _ (fun i => h i.castSucc)
    have h2 := h (Fin.last k)
    omega

theorem sumFinNat_le {n : Nat} (f g : Fin n → Nat) (h : ∀ i, f i ≤ g i) :
    sumFinNat n f ≤ sumFinNat n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [sumFinNat]
    have h1 := ih _ _ (fun i => h i.castSucc)
    have h2 := h (Fin.last k)
    omega

theorem sumFinNat_toInt {n : Nat} (f : Fin n → Nat) :
    ((sumFinNat n f : Nat) : Int) = sumFinInt n (fun i => (f i : Int)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFinNat, sumFinInt]
    rw [← ih]
    omega

theorem sumFinInt_swap {m n : Nat} (f : Fin m → Fin n → Int) :
    sumFinInt m (fun i => sumFinInt n (fun j => f i j)) =
    sumFinInt n (fun j => sumFinInt m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumFinInt]
    exact (sumFinInt_zero n).symm
  | succ k ih =>
    simp only [sumFinInt]
    rw [ih (fun i j => f i.castSucc j), ← sumFinInt_add]

theorem sumFinNat_eq_single_add {n : Nat} (f : Fin n → Nat) (i0 : Fin n) :
    sumFinNat n f = f i0 + sumFinNat n (fun i => if i = i0 then 0 else f i) := by
  induction n with
  | zero => exact Fin.elim0 i0
  | succ k ih =>
    simp only [sumFinNat]
    by_cases hlast : i0 = Fin.last k
    · subst hlast
      have h1 : sumFinNat k (fun i : Fin k => if i.castSucc = Fin.last k then 0 else f i.castSucc) =
                sumFinNat k (fun i : Fin k => f i.castSucc) := by
        apply sumFinNat_congr
        intro i
        have hne : i.castSucc ≠ Fin.last k := by
          intro heq; have : i.castSucc.val = k := congrArg Fin.val heq; simp at this; omega
        simp [hne]
      rw [h1]
      simp only [↓reduceIte]
      omega
    · have hlt : i0.val < k := by
        have := i0.isLt
        have hne : i0.val ≠ k := fun hv => hlast (Fin.ext hv)
        omega
      let i0' : Fin k := ⟨i0.val, hlt⟩
      have hi0 : i0 = i0'.castSucc := Fin.ext rfl
      have hih := ih (fun i => f i.castSucc) i0'
      have hcongr : sumFinNat k (fun i : Fin k => if i.castSucc = i0 then 0 else f i.castSucc) =
                    sumFinNat k (fun i : Fin k => if i = i0' then 0 else f i.castSucc) := by
        apply sumFinNat_congr
        intro i
        have heq : (i.castSucc = i0) ↔ (i = i0') := by
          rw [hi0]
          constructor
          · intro h; have hv : i.castSucc.val = i0'.castSucc.val := congrArg Fin.val h; exact Fin.ext hv
          · intro h; rw [h]
        by_cases h : i = i0'
        · subst h; simp only [hi0, ↓reduceIte]
        · have h' : i.castSucc ≠ i0 := mt heq.mp h
          simp only [h', h, ↓reduceIte]
      have hne_last : Fin.last k ≠ i0 := Ne.symm hlast
      simp only [hne_last, ↓reduceIte]
      rw [hcongr, hih]
      have hval : f i0'.castSucc = f i0 := by rw [← hi0]
      rw [hval]
      omega

theorem sumFinNat_bijection {n : Nat} (π πinv : Fin n → Fin n)
    (h1 : ∀ x, πinv (π x) = x) (h2 : ∀ y, π (πinv y) = y) (f : Fin n → Nat) :
    sumFinNat n (fun i => f (π i)) = sumFinNat n f := by
  have hstep : ∀ (m : Nat), m ≤ n →
      sumFinNat n (fun i => if (π i).val < m then f (π i) else 0) =
      sumFinNat n (fun j => if j.val < m then f j else 0) := by
    intro m hm
    induction m with
    | zero =>
      have ha : sumFinNat n (fun i => if (π i).val < 0 then f (π i) else 0) = 0 := by
        rw [sumFinNat_congr _ (fun _ => 0) (fun _ => by simp), sumFinNat_zero]
      have hb : sumFinNat n (fun j => if j.val < 0 then f j else 0) = 0 := by
        rw [sumFinNat_congr _ (fun _ => 0) (fun _ => by simp), sumFinNat_zero]
      rw [ha, hb]
    | succ k ih =>
      let jm : Fin n := ⟨k, hm⟩
      let im : Fin n := πinv jm
      have him : π im = jm := h2 jm
      have hl := sumFinNat_eq_single_add (fun i => if (π i).val < k + 1 then f (π i) else 0) im
      have hr := sumFinNat_eq_single_add (fun j => if j.val < k + 1 then f j else 0) jm
      have hl_rest : sumFinNat n (fun i => if i = im then 0 else if (π i).val < k + 1 then f (π i) else 0) =
                     sumFinNat n (fun i => if (π i).val < k then f (π i) else 0) := by
        apply sumFinNat_congr
        intro i
        by_cases hi : i = im
        · subst hi
          simp only [↓reduceIte, him, jm]
          have : ¬ k < k := Nat.lt_irrefl k
          simp [this]
        · have hpi_ne : π i ≠ jm := by
            intro heq
            have : i = im := by
              calc i = πinv (π i) := (h1 i).symm
                   _ = πinv jm := by rw [heq]
            exact hi this
          have hval_ne : (π i).val ≠ k := fun hv => hpi_ne (Fin.ext hv)
          have hiff : ((π i).val < k + 1) ↔ ((π i).val < k) := by omega
          simp only [hi, ↓reduceIte]
          by_cases hlt : (π i).val < k
          · simp [hiff.mpr hlt, hlt]
          · simp [mt hiff.mp hlt, hlt]
      have hr_rest : sumFinNat n (fun j => if j = jm then 0 else if j.val < k + 1 then f j else 0) =
                     sumFinNat n (fun j => if j.val < k then f j else 0) := by
        apply sumFinNat_congr
        intro j
        by_cases hj : j = jm
        · subst hj
          simp only [↓reduceIte, jm]
          have : ¬ k < k := Nat.lt_irrefl k
          simp [this]
        · have hval_ne : j.val ≠ k := fun hv => hj (Fin.ext hv)
          have hiff : (j.val < k + 1) ↔ (j.val < k) := by omega
          simp only [hj, ↓reduceIte]
          by_cases hlt : j.val < k
          · simp [hiff.mpr hlt, hlt]
          · simp [mt hiff.mp hlt, hlt]
      rw [hl, hr, hl_rest, hr_rest, ih (by omega), him]
  have hfull := hstep n (Nat.le_refl n)
  have hL : sumFinNat n (fun i => if (π i).val < n then f (π i) else 0) = sumFinNat n (fun i => f (π i)) :=
    sumFinNat_congr _ _ (fun i => by simp [(π i).isLt])
  have hR : sumFinNat n (fun j => if j.val < n then f j else 0) = sumFinNat n f :=
    sumFinNat_congr _ _ (fun j => by simp [j.isLt])
  rw [hL, hR] at hfull
  exact hfull

/-! ### 2. Exact Orthogonality & Witnesses for Paley-32 and Sylvester-32 -/

theorem paley32_orthogonal : isOrthogonal paley32 32 := by
  funext i j
  revert i j
  decide

theorem sylvester32_orthogonal : isOrthogonal sylvester32 32 := by
  funext i j
  revert i j
  decide

theorem sylvester32_k4_witness :
    let y := matVec sylvester32 (supportVec [0, 1, 2, 3])
    countAbsEq y 4 = 8 ∧ countAbsEq y 0 = 24 ∧ sumFourthInt y = 2048 := by
  decide

set_option maxRecDepth 20000 in
theorem countAffinePlanes32_eq : countAffinePlanes32 = 1240 := by
  decide

/-! ### 3. Algebraic Proof that Every Affine 2-Plane in Sylvester-32 Hits `maxC4 = 8` -/

theorem xor_lt_32 {a b : Nat} (ha : a < 32) (hb : b < 32) : a ^^^ b < 32 :=
  Nat.xor_lt_two_pow (n := 5) ha hb

theorem sylvester32_xor_mul (r a b : Fin 32) :
    sylvester32 r a * sylvester32 r b = sylvester32 r ⟨a.val ^^^ b.val, xor_lt_32 a.isLt b.isLt⟩ := by
  have hbit : ∀ (x y : Fin 32), (popcount6 (x.val ^^^ y.val)) % 2 = (popcount6 x.val + popcount6 y.val) % 2 := by
    decide
  have hand : (r.val &&& (a.val ^^^ b.val)) = ((r.val &&& a.val) ^^^ (r.val &&& b.val)) :=
    Nat.and_xor_distrib_left
  have hlt1 : r.val &&& a.val < 32 := by
    have := Nat.and_le_left (n := r.val) (m := a.val); have := r.isLt; omega
  have hlt2 : r.val &&& b.val < 32 := by
    have := Nat.and_le_left (n := r.val) (m := b.val); have := r.isLt; omega
  have hp := hbit ⟨r.val &&& a.val, hlt1⟩ ⟨r.val &&& b.val, hlt2⟩
  simp only [sylvester32, sylvesterMat]
  rw [hand]
  have hmod : popcount6 ((r.val &&& a.val) ^^^ (r.val &&& b.val)) % 2 =
              (popcount6 (r.val &&& a.val) + popcount6 (r.val &&& b.val)) % 2 := hp
  rw [hmod]
  by_cases h1 : popcount6 (r.val &&& a.val) % 2 = 0 <;>
  by_cases h2 : popcount6 (r.val &&& b.val) % 2 = 0 <;>
  simp [h1, h2] <;> omega

theorem sylvester32_col_sum_zero (c : Fin 32) (hc : c.val ≠ 0) :
    sumFinInt 32 (fun r => sylvester32 r c) = 0 := by
  have h : ∀ c : Fin 32, c.val ≠ 0 → sumFinInt 32 (fun r => sylvester32 r c) = 0 := by decide
  exact h c hc

theorem nat_xor_eq_zero_iff (x y : Nat) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have ht : (x ^^^ y).testBit i = false := by rw [h]; simp
    rw [Nat.testBit_xor] at ht
    cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all
  · intro h; rw [h, Nat.xor_self]

theorem nat_xor_four_rearrange (x y z w : Nat) (h : x ^^^ y ^^^ z ^^^ w = 0) :
    x ^^^ w = (x ^^^ y) ^^^ (x ^^^ z) := by
  have h1 : (x ^^^ y) ^^^ (x ^^^ z) = y ^^^ z := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_xor]
    cases x.testBit i <;> cases y.testBit i <;> cases z.testBit i <;> rfl
  rw [h1]
  apply Nat.eq_of_testBit_eq; intro i
  have ht : (x ^^^ y ^^^ z ^^^ w).testBit i = false := by rw [h]; simp
  simp only [Nat.testBit_xor] at ht ⊢
  cases hx : x.testBit i <;> cases hy : y.testBit i <;>
  cases hz : z.testBit i <;> cases hw : w.testBit i <;> simp_all

theorem sylvester32_affine_plane_c4 (c0 c1 c2 c3 : Fin 32)
    (h01 : c0 < c1) (h12 : c1 < c2) (_h23 : c2 < c3)
    (hxor : c0.val ^^^ c1.val ^^^ c2.val ^^^ c3.val = 0)
    (s1 s2 s3 : Int) (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1) (hs3 : s3 = 1 ∨ s3 = -1) :
    c4ForSigns sylvester32 c0 c1 c2 c3 s1 s2 s3 = if s1 * s2 * s3 = 1 then 8 else 0 := by
  have ha_lt : c0.val ^^^ c1.val < 32 := xor_lt_32 c0.isLt c1.isLt
  have hb_lt : c0.val ^^^ c2.val < 32 := xor_lt_32 c0.isLt c2.isLt
  have hab_lt : (c0.val ^^^ c1.val) ^^^ (c0.val ^^^ c2.val) < 32 := xor_lt_32 ha_lt hb_lt
  let a : Fin 32 := ⟨c0.val ^^^ c1.val, ha_lt⟩
  let b : Fin 32 := ⟨c0.val ^^^ c2.val, hb_lt⟩
  let ab : Fin 32 := ⟨a.val ^^^ b.val, hab_lt⟩
  have ha_ne : a.val ≠ 0 := by
    intro h
    have heq : c0.val = c1.val := (nat_xor_eq_zero_iff c0.val c1.val).mp h
    exact Nat.ne_of_lt h01 heq
  have hb_ne : b.val ≠ 0 := by
    intro h
    have heq : c0.val = c2.val := (nat_xor_eq_zero_iff c0.val c2.val).mp h
    exact Nat.ne_of_lt (Nat.lt_trans h01 h12) heq
  have hab_ne : ab.val ≠ 0 := by
    intro h
    have heq1 : c0.val ^^^ c1.val = c0.val ^^^ c2.val := (nat_xor_eq_zero_iff a.val b.val).mp h
    have heq2 : c1.val = c2.val := by
      apply Nat.eq_of_testBit_eq; intro i
      have ht : (c0.val ^^^ c1.val).testBit i = (c0.val ^^^ c2.val).testBit i := by rw [heq1]
      simp only [Nat.testBit_xor] at ht
      cases h0 : c0.val.testBit i <;> cases h1 : c1.val.testBit i <;> cases h2 : c2.val.testBit i <;> simp_all
    exact Nat.ne_of_lt h12 heq2
  have hc3_xor : c0.val ^^^ c3.val = ab.val :=
    nat_xor_four_rearrange c0.val c1.val c2.val c3.val hxor
  have hprod : ∀ r : Fin 32,
      sylvester32 r c0 * sylvester32 r c1 = sylvester32 r a ∧
      sylvester32 r c0 * sylvester32 r c2 = sylvester32 r b ∧
      sylvester32 r c0 * sylvester32 r c3 = sylvester32 r ab ∧
      sylvester32 r a * sylvester32 r b = sylvester32 r ab := by
    intro r
    refine ⟨sylvester32_xor_mul r c0 c1, sylvester32_xor_mul r c0 c2, ?_, sylvester32_xor_mul r a b⟩
    have h := sylvester32_xor_mul r c0 c3
    have heq : (⟨c0.val ^^^ c3.val, xor_lt_32 c0.isLt c3.isLt⟩ : Fin 32) = ab := Fin.ext hc3_xor
    rw [heq] at h
    exact h
  have hpm : ∀ r c : Fin 32, sylvester32 r c = 1 ∨ sylvester32 r c = -1 := by
    intro r c; simp only [sylvester32, sylvesterMat]; split <;> simp
  have h4pm_pos : ∀ a0 a1 a2 a3 : Int,
      (a0 = 1 ∨ a0 = -1) → (a1 = 1 ∨ a1 = -1) → (a2 = 1 ∨ a2 = -1) → (a3 = 1 ∨ a3 = -1) →
      a0 * a1 * a2 * a3 = 1 →
      (4 : Int) * (if (a0 + a1 + a2 + a3).natAbs = 4 then 1 else 0) = (1 + a0 * a1) * (1 + a0 * a2) := by
    intro a0 a1 a2 a3 h0 h1 h2 h3 hp
    rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;>
    rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;> simp_all
  have h4pm_neg : ∀ a0 a1 a2 a3 : Int,
      (a0 = 1 ∨ a0 = -1) → (a1 = 1 ∨ a1 = -1) → (a2 = 1 ∨ a2 = -1) → (a3 = 1 ∨ a3 = -1) →
      a0 * a1 * a2 * a3 = -1 →
      (if (a0 + a1 + a2 + a3).natAbs = 4 then 1 else 0) = 0 := by
    intro a0 a1 a2 a3 h0 h1 h2 h3 hp
    rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;>
    rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;> simp_all
  have hpm_mul : ∀ x y : Int, (x = 1 ∨ x = -1) → (y = 1 ∨ y = -1) → (x * y = 1 ∨ x * y = -1) := by
    intro x y hx hy; rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp
  have hprod4_all : ∀ r : Fin 32,
      sylvester32 r c0 * sylvester32 r c1 * sylvester32 r c2 * sylvester32 r c3 = 1 := by
    intro r
    rcases hprod r with ⟨hp1, hp2, hp3, hp4⟩
    have hsq : sylvester32 r c0 * sylvester32 r c0 = 1 := by
      rcases hpm r c0 with h | h <;> simp [h]
    have hab_sq : sylvester32 r ab * sylvester32 r ab = 1 := by
      rcases hpm r ab with h | h <;> simp [h]
    calc sylvester32 r c0 * sylvester32 r c1 * sylvester32 r c2 * sylvester32 r c3
        = (sylvester32 r c0 * sylvester32 r c1) * (sylvester32 r c0 * sylvester32 r c2) *
          (sylvester32 r c0 * sylvester32 r c3) * (sylvester32 r c0 * sylvester32 r c0) := by
          have : sylvester32 r c0 * sylvester32 r c0 = 1 := hsq
          grind
      _ = sylvester32 r a * sylvester32 r b * sylvester32 r ab * 1 := by rw [hp1, hp2, hp3, hsq]
      _ = sylvester32 r ab * sylvester32 r ab := by rw [hp4]; omega
      _ = 1 := hab_sq
  by_cases hsign : s1 * s2 * s3 = 1
  · simp only [hsign, ↓reduceIte]
    have hterm : ∀ r : Fin 32,
        (4 : Int) * (if (sylvester32 r c0 + s1 * sylvester32 r c1 + s2 * sylvester32 r c2 + s3 * sylvester32 r c3).natAbs = 4 then 1 else 0) =
        (1 + s1 * sylvester32 r a) * (1 + s2 * sylvester32 r b) := by
      intro r
      have hp := h4pm_pos (sylvester32 r c0) (s1 * sylvester32 r c1) (s2 * sylvester32 r c2) (s3 * sylvester32 r c3)
        (hpm r c0) (hpm_mul s1 _ hs1 (hpm r c1)) (hpm_mul s2 _ hs2 (hpm r c2)) (hpm_mul s3 _ hs3 (hpm r c3))
        (by have := hprod4_all r; grind)
      rw [hp]
      rcases hprod r with ⟨hp1, hp2, _, _⟩
      rw [← hp1, ← hp2]
      grind
    have h4 : (4 : Int) * (c4ForSigns sylvester32 c0 c1 c2 c3 s1 s2 s3 : Int) =
              sumFinInt 32 (fun r => (1 + s1 * sylvester32 r a) * (1 + s2 * sylvester32 r b)) := by
      unfold c4ForSigns
      rw [sumFinNat_toInt, ← sumFinInt_mul_left]
      apply sumFinInt_congr
      intro r
      have ht := hterm r
      by_cases h4' : (sylvester32 r c0 + s1 * sylvester32 r c1 + s2 * sylvester32 r c2 + s3 * sylvester32 r c3).natAbs = 4
      · simp only [h4', ↓reduceIte] at ht ⊢; exact ht
      · simp only [h4', ↓reduceIte] at ht ⊢; exact ht
    have hexpand : sumFinInt 32 (fun r => (1 + s1 * sylvester32 r a) * (1 + s2 * sylvester32 r b)) = 32 := by
      have hcongr : ∀ r : Fin 32,
          (1 + s1 * sylvester32 r a) * (1 + s2 * sylvester32 r b) =
          1 + s1 * sylvester32 r a + s2 * sylvester32 r b + (s1 * s2) * sylvester32 r ab := by
        intro r
        have hp4 := (hprod r).2.2.2
        rw [← hp4]
        grind
      rw [sumFinInt_congr _ _ hcongr]
      rw [sumFinInt_add, sumFinInt_add, sumFinInt_add]
      rw [sumFinInt_mul_left, sumFinInt_mul_left, sumFinInt_mul_left]
      rw [sylvester32_col_sum_zero a ha_ne, sylvester32_col_sum_zero b hb_ne, sylvester32_col_sum_zero ab hab_ne]
      have h32 : sumFinInt 32 (fun _ => (1 : Int)) = 32 := by decide
      rw [h32]
      omega
    rw [hexpand] at h4
    omega
  · simp only [hsign, ↓reduceIte]
    unfold c4ForSigns
    have hsneg : s1 * s2 * s3 = -1 := by
      rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl <;> rcases hs3 with rfl | rfl <;> simp_all
    have hzero : ∀ r : Fin 32,
        (if (sylvester32 r c0 + s1 * sylvester32 r c1 + s2 * sylvester32 r c2 + s3 * sylvester32 r c3).natAbs = 4 then 1 else 0) = 0 := by
      intro r
      exact h4pm_neg (sylvester32 r c0) (s1 * sylvester32 r c1) (s2 * sylvester32 r c2) (s3 * sylvester32 r c3)
        (hpm r c0) (hpm_mul s1 _ hs1 (hpm r c1)) (hpm_mul s2 _ hs2 (hpm r c2)) (hpm_mul s3 _ hs3 (hpm r c3))
        (by have := hprod4_all r; grind)
    rw [sumFinNat_congr _ (fun _ => 0) hzero, sumFinNat_zero]

theorem sylvester32_affine_plane_maxC4 (c0 c1 c2 c3 : Fin 32)
    (h01 : c0 < c1) (h12 : c1 < c2) (h23 : c2 < c3)
    (hxor : c0.val ^^^ c1.val ^^^ c2.val ^^^ c3.val = 0) :
    maxC4 sylvester32 c0 c1 c2 c3 = 8 := by
  unfold maxC4
  rw [sylvester32_affine_plane_c4 c0 c1 c2 c3 h01 h12 h23 hxor 1 1 1 (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]
  rw [sylvester32_affine_plane_c4 c0 c1 c2 c3 h01 h12 h23 hxor (-1) 1 1 (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)]
  rw [sylvester32_affine_plane_c4 c0 c1 c2 c3 h01 h12 h23 hxor 1 (-1) 1 (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)]
  rw [sylvester32_affine_plane_c4 c0 c1 c2 c3 h01 h12 h23 hxor (-1) (-1) 1 (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)]
  rw [sylvester32_affine_plane_c4 c0 c1 c2 c3 h01 h12 h23 hxor 1 1 (-1) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)]
  rw [sylvester32_affine_plane_c4 c0 c1 c2 c3 h01 h12 h23 hxor (-1) 1 (-1) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)]
  rw [sylvester32_affine_plane_c4 c0 c1 c2 c3 h01 h12 h23 hxor 1 (-1) (-1) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)]
  rw [sylvester32_affine_plane_c4 c0 c1 c2 c3 h01 h12 h23 hxor (-1) (-1) (-1) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)]
  decide

/-! ### 4. Paley-32 `AGL(1, 31)` Automorphism Reduction & Exhaustive `k = 4` Zero-Collapse -/

def shift31 (t : Nat) (x : Fin 32) : Fin 32 :=
  if x.val = 0 then ⟨0, by omega⟩
  else ⟨1 + ((x.val - 1 + t) % 31), by have := Nat.mod_lt (x.val - 1 + t) (by omega : 0 < 31); omega⟩

def mul31 (a : Nat) (x : Fin 32) : Fin 32 :=
  if x.val = 0 then ⟨0, by omega⟩
  else ⟨1 + (((x.val - 1) * a) % 31), by have := Nat.mod_lt ((x.val - 1) * a) (by omega : 0 < 31); omega⟩

/-- Modular inverse modulo `31` (structural lookup). -/
def inv31 (d : Nat) : Nat :=
  match d % 31 with
  | 1 => 1 | 2 => 16 | 3 => 21 | 4 => 8 | 5 => 25 | 6 => 26 | 7 => 9 | 8 => 4
  | 9 => 7 | 10 => 28 | 11 => 17 | 12 => 13 | 13 => 12 | 14 => 20 | 15 => 29 | 16 => 2
  | 17 => 11 | 18 => 19 | 19 => 18 | 20 => 14 | 21 => 3 | 22 => 24 | 23 => 27 | 24 => 22
  | 25 => 5 | 26 => 6 | 27 => 23 | 28 => 10 | 29 => 15 | 30 => 30 | _ => 0

theorem paley32_shift31 (t : Fin 31) (r c : Fin 32) :
    paley32 (shift31 t.val r) (shift31 t.val c) = paley32 r c := by
  simp only [paley32, shift31]
  by_cases hr : r.val = 0
  · simp [hr]
  · by_cases hc : c.val = 0
    · simp [hr, hc]
    · simp only [hr, hc, ↓reduceIte]
      have hr1 : (1 + (r.val - 1 + t.val) % 31) ≠ 0 := by omega
      have hc1 : (1 + (c.val - 1 + t.val) % 31) ≠ 0 := by omega
      simp only [hr1, hc1, ↓reduceIte]
      have hd : (((1 + (r.val - 1 + t.val) % 31) - 1) + 31 - ((1 + (c.val - 1 + t.val) % 31) - 1)) % 31 =
                ((r.val - 1) + 31 - (c.val - 1)) % 31 := by
        have hrr := r.isLt; have hcc := c.isLt; have htt := t.isLt
        omega
      rw [hd]

theorem isQR31_mul (a d : Fin 31) (ha : isQR31 a.val = true) :
    isQR31 ((d.val * a.val) % 31) = isQR31 d.val := by
  revert a d ha
  decide

theorem paley32_mul31 (a : Fin 31) (ha : isQR31 a.val = true) (r c : Fin 32) :
    paley32 (mul31 a.val r) (mul31 a.val c) = paley32 r c := by
  have ha_ne : a.val ≠ 0 := by
    intro h0; rw [h0] at ha; exact absurd ha (by decide)
  simp only [paley32, mul31]
  by_cases hr : r.val = 0
  · simp [hr]
  · by_cases hc : c.val = 0
    · simp [hr, hc]
    · simp only [hr, hc, ↓reduceIte]
      have hr1 : (1 + ((r.val - 1) * a.val) % 31) ≠ 0 := by omega
      have hc1 : (1 + ((c.val - 1) * a.val) % 31) ≠ 0 := by omega
      simp only [hr1, hc1, ↓reduceIte]
      have hd : (((1 + ((r.val - 1) * a.val) % 31) - 1) + 31 - ((1 + ((c.val - 1) * a.val) % 31) - 1)) % 31 =
                ((((r.val - 1) + 31 - (c.val - 1)) % 31) * a.val) % 31 := by
        have h1 : ∀ (x y z : Fin 31),
            ((x.val * z.val) % 31 + 31 - (y.val * z.val) % 31) % 31 =
            (((x.val + 31 - y.val) % 31) * z.val) % 31 := by decide
        have hrr := r.isLt; have hcc := c.isLt
        have := h1 ⟨r.val - 1, by omega⟩ ⟨c.val - 1, by omega⟩ a
        simpa using this
      rw [hd]
      let d0 : Fin 31 := ⟨((r.val - 1) + 31 - (c.val - 1)) % 31, Nat.mod_lt _ (by omega)⟩
      have hzero : (d0.val * a.val) % 31 = 0 ↔ d0.val = 0 := by
        have hz : ∀ (x z : Fin 31), z.val ≠ 0 → ((x.val * z.val) % 31 = 0 ↔ x.val = 0) := by decide
        exact hz d0 a ha_ne
      change (if (d0.val * a.val) % 31 = 0 then (1 : Int) else if isQR31 ((d0.val * a.val) % 31) then 1 else -1) =
             (if d0.val = 0 then 1 else if isQR31 d0.val then 1 else -1)
      by_cases h0 : d0.val = 0
      · simp [h0]
      · simp only [mt hzero.mp h0, h0, ↓reduceIte, isQR31_mul a d0 ha]

theorem maxC4_row_aut {n : Nat} (H : IntMat n n) (π πinv : Fin n → Fin n)
    (h1 : ∀ x, πinv (π x) = x) (h2 : ∀ y, π (πinv y) = y)
    (hH : ∀ r c, H (π r) (π c) = H r c)
    (c0 c1 c2 c3 : Fin n) :
    maxC4 H (π c0) (π c1) (π c2) (π c3) = maxC4 H c0 c1 c2 c3 := by
  have hc4 : ∀ s1 s2 s3, c4ForSigns H (π c0) (π c1) (π c2) (π c3) s1 s2 s3 =
                          c4ForSigns H c0 c1 c2 c3 s1 s2 s3 := by
    intro s1 s2 s3
    unfold c4ForSigns
    have hEq := sumFinNat_bijection π πinv h1 h2
      (fun r => if (H r (π c0) + s1 * H r (π c1) + s2 * H r (π c2) + s3 * H r (π c3)).natAbs = 4 then 1 else 0)
    rw [← hEq]
    apply sumFinNat_congr
    intro r
    rw [hH r c0, hH r c1, hH r c2, hH r c3]
  unfold maxC4
  simp only [hc4]

theorem maxC4_swap23 {n : Nat} (H : IntMat n n) (c0 c1 c2 c3 : Fin n) :
    maxC4 H c0 c1 c3 c2 = maxC4 H c0 c1 c2 c3 := by
  have hcomm : ∀ s1 s2 s3, c4ForSigns H c0 c1 c3 c2 s1 s2 s3 = c4ForSigns H c0 c1 c2 c3 s1 s3 s2 := by
    intro s1 s2 s3
    unfold c4ForSigns
    apply sumFinNat_congr
    intro r
    have : H r c0 + s1 * H r c1 + s2 * H r c3 + s3 * H r c2 =
           H r c0 + s1 * H r c1 + s3 * H r c2 + s2 * H r c3 := by omega
    rw [this]
  unfold maxC4
  simp only [hcomm]
  omega

/-- Fast zero-bitwise sign indicator for `paley32` (`true` iff `paley32 r c = -1`). -/
def paleyNeg (r c : Nat) : Bool :=
  if r == 0 then false
  else if c == 0 then true
  else
    let d := (r + 31 - c) % 31
    if d == 0 then false else !isQR31 d

theorem paleyNeg_eq (r c : Fin 32) :
    paleyNeg r.val c.val = decide (paley32 r c = -1) := by
  simp only [paleyNeg, paley32]
  by_cases hr : r.val = 0
  · simp [hr]
  · by_cases hc : c.val = 0
    · simp [hr, hc]
    · have hr0 : (r.val == 0) = false := by simp [hr]
      have hc0 : (c.val == 0) = false := by simp [hc]
      simp only [hr, hc, hr0, hc0, ↓reduceIte]
      have hd : r.val + 31 - c.val = (r.val - 1) + 31 - (c.val - 1) := by omega
      rw [hd]
      by_cases hz : ((r.val - 1) + 31 - (c.val - 1)) % 31 = 0
      · simp [hz]
      · have hz0 : ((((r.val - 1) + 31 - (c.val - 1)) % 31) == 0) = false := by simp [hz]
        simp only [hz, hz0, ↓reduceIte]
        cases isQR31 (((r.val - 1) + 31 - (c.val - 1)) % 31) <;> decide

/-- Single-pass zero-bitwise 8-bucket `maxC4` evaluator for `paley32` (uses only C GMP `Nat` ops). -/
def c4Fast8 (c0 c1 c2 c3 : Nat) : Nat :=
  let rec go : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
    | 0, b0, b1, b2, b3, b4, b5, b6, b7 =>
      max (max (max b0 b1) (max b2 b3)) (max (max b4 b5) (max b6 b7))
    | r + 1, b0, b1, b2, b3, b4, b5, b6, b7 =>
      let p0 := paleyNeg r c0
      let d1 := paleyNeg r c1 != p0
      let d2 := paleyNeg r c2 != p0
      let d3 := paleyNeg r c3 != p0
      match d1, d2, d3 with
      | false, false, false => go r (b0 + 1) b1 b2 b3 b4 b5 b6 b7
      | true,  false, false => go r b0 (b1 + 1) b2 b3 b4 b5 b6 b7
      | false, true,  false => go r b0 b1 (b2 + 1) b3 b4 b5 b6 b7
      | true,  true,  false => go r b0 b1 b2 (b3 + 1) b4 b5 b6 b7
      | false, false, true  => go r b0 b1 b2 b3 (b4 + 1) b5 b6 b7
      | true,  false, true  => go r b0 b1 b2 b3 b4 (b5 + 1) b6 b7
      | false, true,  true  => go r b0 b1 b2 b3 b4 b5 (b6 + 1) b7
      | true,  true,  true  => go r b0 b1 b2 b3 b4 b5 b6 (b7 + 1)
  go 32 0 0 0 0 0 0 0 0

theorem paley32_pm (r c : Fin 32) : paley32 r c = 1 ∨ paley32 r c = -1 := by
  simp only [paley32]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · split
      · exact Or.inl rfl
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl

theorem nat_and1_and (a b : Nat) : (a &&& b) &&& 1 = (a &&& 1) &&& (b &&& 1) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> cases (1 : Nat).testBit i <;> rfl

theorem nat_and1_xor (a b : Nat) : (a ^^^ b) &&& 1 = (a &&& 1) ^^^ (b &&& 1) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases (1 : Nat).testBit i <;> rfl

theorem nat_and1_cases (a : Nat) : (a &&& 1) = 0 ∨ (a &&& 1) = 1 := by
  rw [Nat.and_one_is_mod]; omega

theorem c4Fast8_eq (c0 c1 c2 c3 : Fin 32) :
    c4Fast8 c0.val c1.val c2.val c3.val = maxC4 paley32 c0 c1 c2 c3 := by
  have hgo : ∀ (k : Nat) (hk : k ≤ 32) (b0 b1 b2 b3 b4 b5 b6 b7 : Nat),
      c4Fast8.go c0.val c1.val c2.val c3.val k b0 b1 b2 b3 b4 b5 b6 b7 =
      max (max (max
        (b0 + sumFinNat k (fun r => if (paley32 ⟨r.val, by omega⟩ c0 + 1 * paley32 ⟨r.val, by omega⟩ c1 + 1 * paley32 ⟨r.val, by omega⟩ c2 + 1 * paley32 ⟨r.val, by omega⟩ c3).natAbs = 4 then 1 else 0))
        (b1 + sumFinNat k (fun r => if (paley32 ⟨r.val, by omega⟩ c0 + (-1) * paley32 ⟨r.val, by omega⟩ c1 + 1 * paley32 ⟨r.val, by omega⟩ c2 + 1 * paley32 ⟨r.val, by omega⟩ c3).natAbs = 4 then 1 else 0)))
        (max
        (b2 + sumFinNat k (fun r => if (paley32 ⟨r.val, by omega⟩ c0 + 1 * paley32 ⟨r.val, by omega⟩ c1 + (-1) * paley32 ⟨r.val, by omega⟩ c2 + 1 * paley32 ⟨r.val, by omega⟩ c3).natAbs = 4 then 1 else 0))
        (b3 + sumFinNat k (fun r => if (paley32 ⟨r.val, by omega⟩ c0 + (-1) * paley32 ⟨r.val, by omega⟩ c1 + (-1) * paley32 ⟨r.val, by omega⟩ c2 + 1 * paley32 ⟨r.val, by omega⟩ c3).natAbs = 4 then 1 else 0))))
      (max (max
        (b4 + sumFinNat k (fun r => if (paley32 ⟨r.val, by omega⟩ c0 + 1 * paley32 ⟨r.val, by omega⟩ c1 + 1 * paley32 ⟨r.val, by omega⟩ c2 + (-1) * paley32 ⟨r.val, by omega⟩ c3).natAbs = 4 then 1 else 0))
        (b5 + sumFinNat k (fun r => if (paley32 ⟨r.val, by omega⟩ c0 + (-1) * paley32 ⟨r.val, by omega⟩ c1 + 1 * paley32 ⟨r.val, by omega⟩ c2 + (-1) * paley32 ⟨r.val, by omega⟩ c3).natAbs = 4 then 1 else 0)))
        (max
        (b6 + sumFinNat k (fun r => if (paley32 ⟨r.val, by omega⟩ c0 + 1 * paley32 ⟨r.val, by omega⟩ c1 + (-1) * paley32 ⟨r.val, by omega⟩ c2 + (-1) * paley32 ⟨r.val, by omega⟩ c3).natAbs = 4 then 1 else 0))
        (b7 + sumFinNat k (fun r => if (paley32 ⟨r.val, by omega⟩ c0 + (-1) * paley32 ⟨r.val, by omega⟩ c1 + (-1) * paley32 ⟨r.val, by omega⟩ c2 + (-1) * paley32 ⟨r.val, by omega⟩ c3).natAbs = 4 then 1 else 0)))) := by
    intro k
    induction k with
    | zero =>
      intro _ b0 b1 b2 b3 b4 b5 b6 b7
      simp [c4Fast8.go, sumFinNat]
    | succ r ih =>
      intro hr b0 b1 b2 b3 b4 b5 b6 b7
      let rr : Fin 32 := ⟨r, by omega⟩
      have hn0 : paleyNeg r c0.val = decide (paley32 rr c0 = -1) := paleyNeg_eq rr c0
      have hn1 : paleyNeg r c1.val = decide (paley32 rr c1 = -1) := paleyNeg_eq rr c1
      have hn2 : paleyNeg r c2.val = decide (paley32 rr c2 = -1) := paleyNeg_eq rr c2
      have hn3 : paleyNeg r c3.val = decide (paley32 rr c3 = -1) := paleyNeg_eq rr c3
      unfold c4Fast8.go
      dsimp only
      rw [hn0, hn1, hn2, hn3]
      rcases paley32_pm rr c0 with h0 | h0 <;>
      rcases paley32_pm rr c1 with h1 | h1 <;>
      rcases paley32_pm rr c2 with h2 | h2 <;>
      rcases paley32_pm rr c3 with h3 | h3
      all_goals
        have e0 : paley32 ⟨r, hr⟩ c0 = paley32 rr c0 := rfl
        have e1 : paley32 ⟨r, hr⟩ c1 = paley32 rr c1 := rfl
        have e2 : paley32 ⟨r, hr⟩ c2 = paley32 rr c2 := rfl
        have e3 : paley32 ⟨r, hr⟩ c3 = paley32 rr c3 := rfl
        simp [h0, h1, h2, h3]
        rw [ih (by omega)]
        simp only [sumFinNat, Fin.last, Fin.castSucc, Fin.val_castAdd, e0, e1, e2, e3, h0, h1, h2, h3]
        simp [Nat.add_comm, Nat.add_assoc]
  unfold c4Fast8 maxC4 c4ForSigns
  dsimp only
  rw [hgo 32 (Nat.le_refl 32) 0 0 0 0 0 0 0 0]
  simp only [Nat.zero_add]

/-- Kernel-checked exhaustive verification of all 870 `AGL(1, 31)` canonical representatives! -/
theorem paley32_case1A_all :
    ∀ w : Fin 32, 3 ≤ w.val → c4Fast8 0 1 2 w.val ≤ 5 := by
  decide

theorem paley32_case1B_all :
    ∀ w : Fin 32, 2 ≤ w.val → w.val ≠ 4 → c4Fast8 0 1 4 w.val ≤ 5 := by
  decide

theorem paley32_case2A_all :
    ∀ u v : Fin 32, 3 ≤ u.val → u.val < v.val → c4Fast8 1 2 u.val v.val ≤ 5 := by
  decide

theorem paley32_case2B_all :
    ∀ u v : Fin 32, 2 ≤ u.val → u.val < v.val → u.val ≠ 4 → v.val ≠ 4 →
      c4Fast8 1 4 u.val v.val ≤ 5 := by
  decide

theorem paley32_case1A (w : Fin 32) (hw : 3 ≤ w.val) :
    c4Fast8 0 1 2 w.val ≤ 5 :=
  paley32_case1A_all w hw

theorem paley32_case1B (w : Fin 32) (hw2 : 2 ≤ w.val) (hw4 : w.val ≠ 4) :
    c4Fast8 0 1 4 w.val ≤ 5 :=
  paley32_case1B_all w hw2 hw4

theorem paley32_case2A (u v : Fin 32) (hu : 3 ≤ u.val) (huv : u.val < v.val) :
    c4Fast8 1 2 u.val v.val ≤ 5 :=
  paley32_case2A_all u v hu huv

theorem paley32_case2B (u v : Fin 32) (hu : 2 ≤ u.val) (huv : u.val < v.val) (hu4 : u.val ≠ 4) (hv4 : v.val ≠ 4) :
    c4Fast8 1 4 u.val v.val ≤ 5 :=
  paley32_case2B_all u v hu huv hu4 hv4

theorem paley32_maxC4_le_5 (c0 c1 c2 c3 : Fin 32)
    (h01 : c0 < c1) (h12 : c1 < c2) (h23 : c2 < c3) :
    maxC4 paley32 c0 c1 c2 c3 ≤ 5 := by
  have hshift_inv : ∀ (t : Fin 31) (x : Fin 32),
      shift31 ((31 - t.val) % 31) (shift31 t.val x) = x ∧
      shift31 t.val (shift31 ((31 - t.val) % 31) x) = x := by
    decide
  have hmul_inv : ∀ (a : Fin 31), a.val ≠ 0 →
      (∀ x : Fin 32, mul31 (inv31 a.val) (mul31 a.val x) = x) ∧
      (∀ x : Fin 32, mul31 a.val (mul31 (inv31 a.val) x) = x) := by
    decide
  have hqr_scale : ∀ (d : Fin 31), d.val ≠ 0 →
      ∃ a : Fin 31, isQR31 a.val = true ∧ a.val ≠ 0 ∧
        ((d.val * a.val) % 31 = 1 ∨ (d.val * a.val) % 31 = 3) := by
    decide
  by_cases hc0 : c0.val = 0
  · have hc1_pos : 1 ≤ c1.val := by omega
    let t : Fin 31 := ⟨(31 - (c1.val - 1)) % 31, Nat.mod_lt _ (by omega)⟩
    have hst : maxC4 paley32 (shift31 t.val c0) (shift31 t.val c1) (shift31 t.val c2) (shift31 t.val c3) =
               maxC4 paley32 c0 c1 c2 c3 :=
      maxC4_row_aut paley32 (shift31 t.val) (shift31 ((31 - t.val) % 31))
        (fun x => (hshift_inv t x).1) (fun x => (hshift_inv t x).2)
        (paley32_shift31 t) c0 c1 c2 c3
    let c0' := shift31 t.val c0
    let c1' := shift31 t.val c1
    let c2' := shift31 t.val c2
    let c3' := shift31 t.val c3
    have hc0' : c0' = ⟨0, by omega⟩ := by
      apply Fin.ext; simp [c0', shift31, hc0]
    have hc1' : c1' = ⟨1, by omega⟩ := by
      apply Fin.ext
      have hc1_ne : c1.val ≠ 0 := by omega
      have hc1_lt := c1.isLt
      simp only [c1', shift31, hc1_ne, ↓reduceIte, t]
      omega
    have hshift_inj : ∀ x y : Fin 32, shift31 t.val x = shift31 t.val y → x = y := by
      intro x y hxy
      have := congrArg (shift31 ((31 - t.val) % 31)) hxy
      rw [(hshift_inv t x).1, (hshift_inv t y).1] at this
      exact this
    have hc2'_ge2 : 2 ≤ c2'.val := by
      have hne0 : c2' ≠ c0' := fun h => Nat.ne_of_lt (Nat.lt_trans h01 h12) (congrArg Fin.val (hshift_inj _ _ h)).symm
      have hne1 : c2' ≠ c1' := fun h => Nat.ne_of_lt h12 (congrArg Fin.val (hshift_inj _ _ h)).symm
      rw [hc0'] at hne0; rw [hc1'] at hne1
      have h0 : c2'.val ≠ 0 := fun hv => hne0 (Fin.ext hv)
      have h1 : c2'.val ≠ 1 := fun hv => hne1 (Fin.ext hv)
      omega
    let d : Fin 31 := ⟨c2'.val - 1, by have := c2'.isLt; omega⟩
    have hd_ne : d.val ≠ 0 := by simp [d]; omega
    rcases hqr_scale d hd_ne with ⟨a, ha_qr, ha_ne, ha_eq⟩
    have hmt : maxC4 paley32 (mul31 a.val c0') (mul31 a.val c1') (mul31 a.val c2') (mul31 a.val c3') =
               maxC4 paley32 c0' c1' c2' c3' :=
      maxC4_row_aut paley32 (mul31 a.val) (mul31 (inv31 a.val))
        (hmul_inv a ha_ne).1 (hmul_inv a ha_ne).2 (paley32_mul31 a ha_qr) c0' c1' c2' c3'
    have hmul_inj : ∀ x y : Fin 32, mul31 a.val x = mul31 a.val y → x = y := by
      intro x y hxy
      have := congrArg (mul31 (inv31 a.val)) hxy
      rw [(hmul_inv a ha_ne).1 x, (hmul_inv a ha_ne).1 y] at this
      exact this
    let w := mul31 a.val c3'
    have hm0 : mul31 a.val c0' = ⟨0, by omega⟩ := by rw [hc0']; rfl
    have hm1 : mul31 a.val c1' = ⟨1, by omega⟩ := by rw [hc1']; apply Fin.ext; simp [mul31]
    have hw_ne0 : w.val ≠ 0 := by
      intro h0
      have : mul31 a.val c3' = mul31 a.val c0' := by rw [hm0]; exact Fin.ext h0
      have hc30 : c3 = c0 := hshift_inj _ _ (hmul_inj _ _ this)
      have hlt : c0.val < c3.val := Nat.lt_trans (Nat.lt_trans h01 h12) h23
      exact Nat.ne_of_lt hlt (congrArg Fin.val hc30.symm)
    have hw_ne1 : w.val ≠ 1 := by
      intro h1
      have : mul31 a.val c3' = mul31 a.val c1' := by rw [hm1]; exact Fin.ext h1
      have hc31 : c3 = c1 := hshift_inj _ _ (hmul_inj _ _ this)
      have hlt : c1.val < c3.val := Nat.lt_trans h12 h23
      exact Nat.ne_of_lt hlt (congrArg Fin.val hc31.symm)
    rw [← hst, ← hmt, hm0, hm1]
    rcases ha_eq with h1 | h3
    · have hm2 : mul31 a.val c2' = ⟨2, by omega⟩ := by
        apply Fin.ext
        have hne0 : c2'.val ≠ 0 := by omega
        simp only [mul31, hne0, ↓reduceIte]
        have : ((c2'.val - 1) * a.val) % 31 = 1 := h1
        omega
      have hw_ne2 : w.val ≠ 2 := by
        intro h2
        have : mul31 a.val c3' = mul31 a.val c2' := by rw [hm2]; exact Fin.ext h2
        have hc32 : c3 = c2 := hshift_inj _ _ (hmul_inj _ _ this)
        exact Nat.ne_of_lt h23 (congrArg Fin.val hc32.symm)
      rw [hm2, ← c4Fast8_eq]
      exact paley32_case1A w (by omega)
    · have hm2 : mul31 a.val c2' = ⟨4, by omega⟩ := by
        apply Fin.ext
        have hne0 : c2'.val ≠ 0 := by omega
        simp only [mul31, hne0, ↓reduceIte]
        have : ((c2'.val - 1) * a.val) % 31 = 3 := h3
        omega
      have hw_ne4 : w.val ≠ 4 := by
        intro h4
        have : mul31 a.val c3' = mul31 a.val c2' := by rw [hm2]; exact Fin.ext h4
        have hc32 : c3 = c2 := hshift_inj _ _ (hmul_inj _ _ this)
        exact Nat.ne_of_lt h23 (congrArg Fin.val hc32.symm)
      rw [hm2, ← c4Fast8_eq]
      exact paley32_case1B w (by omega) hw_ne4
  · let t : Fin 31 := ⟨(31 - (c0.val - 1)) % 31, Nat.mod_lt _ (by omega)⟩
    have hst : maxC4 paley32 (shift31 t.val c0) (shift31 t.val c1) (shift31 t.val c2) (shift31 t.val c3) =
               maxC4 paley32 c0 c1 c2 c3 :=
      maxC4_row_aut paley32 (shift31 t.val) (shift31 ((31 - t.val) % 31))
        (fun x => (hshift_inv t x).1) (fun x => (hshift_inv t x).2)
        (paley32_shift31 t) c0 c1 c2 c3
    let c0' := shift31 t.val c0
    let c1' := shift31 t.val c1
    let c2' := shift31 t.val c2
    let c3' := shift31 t.val c3
    have hc0' : c0' = ⟨1, by omega⟩ := by
      apply Fin.ext
      have hc0_lt := c0.isLt
      simp only [c0', shift31, hc0, ↓reduceIte, t]
      omega
    have hshift_inj : ∀ x y : Fin 32, shift31 t.val x = shift31 t.val y → x = y := by
      intro x y hxy
      have := congrArg (shift31 ((31 - t.val) % 31)) hxy
      rw [(hshift_inv t x).1, (hshift_inv t y).1] at this
      exact this
    have hshift_nz : ∀ x : Fin 32, x.val ≠ 0 → (shift31 t.val x).val ≠ 0 := by
      intro x hx; simp [shift31, hx]
    have hc1'_ge2 : 2 ≤ c1'.val := by
      have hne0 : c1'.val ≠ 0 := hshift_nz c1 (by omega)
      have hne1 : c1' ≠ c0' := fun h => Nat.ne_of_lt h01 (congrArg Fin.val (hshift_inj _ _ h)).symm
      rw [hc0'] at hne1
      have h1 : c1'.val ≠ 1 := fun hv => hne1 (Fin.ext hv)
      omega
    let d : Fin 31 := ⟨c1'.val - 1, by have := c1'.isLt; omega⟩
    have hd_ne : d.val ≠ 0 := by simp [d]; omega
    rcases hqr_scale d hd_ne with ⟨a, ha_qr, ha_ne, ha_eq⟩
    have hmt : maxC4 paley32 (mul31 a.val c0') (mul31 a.val c1') (mul31 a.val c2') (mul31 a.val c3') =
               maxC4 paley32 c0' c1' c2' c3' :=
      maxC4_row_aut paley32 (mul31 a.val) (mul31 (inv31 a.val))
        (hmul_inv a ha_ne).1 (hmul_inv a ha_ne).2 (paley32_mul31 a ha_qr) c0' c1' c2' c3'
    have hmul_inj : ∀ x y : Fin 32, mul31 a.val x = mul31 a.val y → x = y := by
      intro x y hxy
      have := congrArg (mul31 (inv31 a.val)) hxy
      rw [(hmul_inv a ha_ne).1 x, (hmul_inv a ha_ne).1 y] at this
      exact this
    have hmul_nz : ∀ x : Fin 32, x.val ≠ 0 → (mul31 a.val x).val ≠ 0 := by
      intro x hx; simp [mul31, hx]
    let u := mul31 a.val c2'
    let v := mul31 a.val c3'
    have hm0 : mul31 a.val c0' = ⟨1, by omega⟩ := by rw [hc0']; apply Fin.ext; simp [mul31]
    have hu_ge2 : 2 ≤ u.val := by
      have h0 : u.val ≠ 0 := hmul_nz c2' (hshift_nz c2 (by omega))
      have hne1 : u ≠ mul31 a.val c0' := fun h =>
        Nat.ne_of_lt (Nat.lt_trans h01 h12) (congrArg Fin.val (hshift_inj _ _ (hmul_inj _ _ h))).symm
      rw [hm0] at hne1
      have h1 : u.val ≠ 1 := fun hv => hne1 (Fin.ext hv)
      omega
    have hv_ge2 : 2 ≤ v.val := by
      have h0 : v.val ≠ 0 := hmul_nz c3' (hshift_nz c3 (by omega))
      have hne1 : v ≠ mul31 a.val c0' := fun h =>
        Nat.ne_of_lt (Nat.lt_trans (Nat.lt_trans h01 h12) h23) (congrArg Fin.val (hshift_inj _ _ (hmul_inj _ _ h))).symm
      rw [hm0] at hne1
      have h1 : v.val ≠ 1 := fun hv => hne1 (Fin.ext hv)
      omega
    have huv_ne : u.val ≠ v.val := by
      intro h
      have hc23 : c2 = c3 := hshift_inj _ _ (hmul_inj _ _ (Fin.ext h))
      exact Nat.ne_of_lt h23 (congrArg Fin.val hc23)
    rw [← hst, ← hmt, hm0]
    rcases ha_eq with h1 | h3
    · have hm1 : mul31 a.val c1' = ⟨2, by omega⟩ := by
        apply Fin.ext
        have hne0 : c1'.val ≠ 0 := by omega
        simp only [mul31, hne0, ↓reduceIte]
        have : ((c1'.val - 1) * a.val) % 31 = 1 := h1
        omega
      have hu_ne2 : u.val ≠ 2 := by
        intro h2
        have : mul31 a.val c2' = mul31 a.val c1' := by rw [hm1]; exact Fin.ext h2
        exact Nat.ne_of_lt h12 (congrArg Fin.val (hshift_inj _ _ (hmul_inj _ _ this))).symm
      have hv_ne2 : v.val ≠ 2 := by
        intro h2
        have : mul31 a.val c3' = mul31 a.val c1' := by rw [hm1]; exact Fin.ext h2
        exact Nat.ne_of_lt (Nat.lt_trans h12 h23) (congrArg Fin.val (hshift_inj _ _ (hmul_inj _ _ this))).symm
      rw [hm1]
      by_cases hlt : u.val < v.val
      · rw [← c4Fast8_eq]
        exact paley32_case2A u v (by omega) hlt
      · rw [← maxC4_swap23, ← c4Fast8_eq]
        exact paley32_case2A v u (by omega) (by omega)
    · have hm1 : mul31 a.val c1' = ⟨4, by omega⟩ := by
        apply Fin.ext
        have hne0 : c1'.val ≠ 0 := by omega
        simp only [mul31, hne0, ↓reduceIte]
        have : ((c1'.val - 1) * a.val) % 31 = 3 := h3
        omega
      have hu_ne4 : u.val ≠ 4 := by
        intro h4
        have : mul31 a.val c2' = mul31 a.val c1' := by rw [hm1]; exact Fin.ext h4
        exact Nat.ne_of_lt h12 (congrArg Fin.val (hshift_inj _ _ (hmul_inj _ _ this))).symm
      have hv_ne4 : v.val ≠ 4 := by
        intro h4
        have : mul31 a.val c3' = mul31 a.val c1' := by rw [hm1]; exact Fin.ext h4
        exact Nat.ne_of_lt (Nat.lt_trans h12 h23) (congrArg Fin.val (hshift_inj _ _ (hmul_inj _ _ this))).symm
      rw [hm1]
      by_cases hlt : u.val < v.val
      · rw [← c4Fast8_eq]
        exact paley32_case2B u v (by omega) hlt hu_ne4 hv_ne4
      · rw [← maxC4_swap23, ← c4Fast8_eq]
        exact paley32_case2B v u (by omega) (by omega) hv_ne4 hu_ne4

theorem paley32_maxC4_witness :
    maxC4 paley32 ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨5, by omega⟩ = 5 := by
  rw [← c4Fast8_eq]
  decide

/-! ### 5. Proof of Theorem 2 -/

theorem paley32_orthogonality_and_zero_k4_collapse :
    isOrthogonal paley32 32 ∧
    isOrthogonal sylvester32 32 ∧
    (let y := matVec sylvester32 (supportVec [0, 1, 2, 3])
     countAbsEq y 4 = 8 ∧ countAbsEq y 0 = 24 ∧ sumFourthInt y = 2048) ∧
    countAffinePlanes32 = 1240 ∧
    (∀ c0 c1 c2 c3 : Fin 32, c0 < c1 → c1 < c2 → c2 < c3 →
      (c0.val ^^^ c1.val ^^^ c2.val ^^^ c3.val = 0) →
      maxC4 sylvester32 c0 c1 c2 c3 = 8) ∧
    (∀ c0 c1 c2 c3 : Fin 32, c0 < c1 → c1 < c2 → c2 < c3 →
      maxC4 paley32 c0 c1 c2 c3 ≤ 5) ∧
    (∃ c0 c1 c2 c3 : Fin 32, c0 < c1 ∧ c1 < c2 ∧ c2 < c3 ∧
      maxC4 paley32 c0 c1 c2 c3 = 5) := by
  refine ⟨paley32_orthogonal, sylvester32_orthogonal, sylvester32_k4_witness,
          countAffinePlanes32_eq, sylvester32_affine_plane_maxC4, paley32_maxC4_le_5, ?_⟩
  exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨5, by omega⟩,
         by decide, by decide, by decide, paley32_maxC4_witness⟩

/-! ### 6. Theorem 3: Transpose Duality & Universal `k = 8` Zero-Collapse + `ℓ_4^4 ≤ 12,544` -/

def neg31 (x : Fin 32) : Fin 32 :=
  if x.val = 0 then ⟨0, by omega⟩
  else ⟨1 + ((31 - (x.val - 1)) % 31), by have := Nat.mod_lt (31 - (x.val - 1)) (by omega : 0 < 31); omega⟩

def sign0 (x : Fin 32) : Int :=
  if x.val = 0 then -1 else 1

theorem paley32_transpose_equiv (r c : Fin 32) :
    paley32 c r = sign0 r * sign0 c * paley32 (neg31 r) (neg31 c) := by
  revert r c
  decide

theorem neg31_involutive (x : Fin 32) : neg31 (neg31 x) = x := by
  revert x
  decide

theorem paley32_transpose_maxC4_le_5 (r0 r1 r2 r3 : Fin 32)
    (h01 : r0 ≠ r1) (h02 : r0 ≠ r2) (h03 : r0 ≠ r3)
    (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3) :
    maxC4 (transpose paley32) r0 r1 r2 r3 ≤ 5 := by
  have hmaxC4_symm : ∀ (a b c d : Fin 32), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      maxC4 paley32 a b c d ≤ 5 := by
    have hswap01 : ∀ (H : IntMat 32 32) (a b c d : Fin 32), maxC4 H b a c d = maxC4 H a b c d := by
      intro H a b c d
      have h1 : ∀ s1 s2 s3, (s1 = 1 ∨ s1 = -1) →
          c4ForSigns H b a c d s1 s2 s3 = c4ForSigns H a b c d s1 (s1 * s2) (s1 * s3) := by
        intro s1 s2 s3 hs1
        unfold c4ForSigns
        apply sumFinNat_congr
        intro r
        rcases hs1 with rfl | rfl
        · have : H r b + 1 * H r a + s2 * H r c + s3 * H r d =
                 H r a + 1 * H r b + 1 * s2 * H r c + 1 * s3 * H r d := by grind
          rw [this]
        · have : (H r b + -1 * H r a + s2 * H r c + s3 * H r d) =
                 -(H r a + -1 * H r b + -1 * s2 * H r c + -1 * s3 * H r d) := by grind
          rw [this, Int.natAbs_neg]
      unfold maxC4
      dsimp only
      rw [h1 1 1 1 (Or.inl rfl), h1 (-1) 1 1 (Or.inr rfl),
          h1 1 (-1) 1 (Or.inl rfl), h1 (-1) (-1) 1 (Or.inr rfl),
          h1 1 1 (-1) (Or.inl rfl), h1 (-1) 1 (-1) (Or.inr rfl),
          h1 1 (-1) (-1) (Or.inl rfl), h1 (-1) (-1) (-1) (Or.inr rfl)]
      simp only [Int.one_mul, Int.neg_mul, Int.neg_neg]
      have hmax8 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Nat,
          max (max (max a0 a7) (max a2 a5)) (max (max a4 a3) (max a6 a1)) =
          max (max (max a0 a1) (max a2 a3)) (max (max a4 a5) (max a6 a7)) := by
        intro a0 a1 a2 a3 a4 a5 a6 a7
        have h1 : max (max (max a0 a7) (max a2 a5)) (max (max a4 a3) (max a6 a1)) =
                  max (max (max a0 a1) (max a2 a3)) (max (max a4 a5) (max a6 a7)) := by
          simp only [Nat.max_assoc]
          ac_rfl
        exact h1
      exact hmax8 _ _ _ _ _ _ _ _
    have hswap12 : ∀ (H : IntMat 32 32) (a b c d : Fin 32), maxC4 H a c b d = maxC4 H a b c d := by
      intro H a b c d
      have h1 : ∀ s1 s2 s3, c4ForSigns H a c b d s1 s2 s3 = c4ForSigns H a b c d s2 s1 s3 := by
        intro s1 s2 s3; unfold c4ForSigns; apply sumFinNat_congr; intro r
        have : H r a + s1 * H r c + s2 * H r b + s3 * H r d =
               H r a + s2 * H r b + s1 * H r c + s3 * H r d := by omega
        rw [this]
      unfold maxC4; dsimp only; simp only [h1]
      have hmax8 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Nat,
          max (max (max a0 a2) (max a1 a3)) (max (max a4 a6) (max a5 a7)) =
          max (max (max a0 a1) (max a2 a3)) (max (max a4 a5) (max a6 a7)) := by
        intro a0 a1 a2 a3 a4 a5 a6 a7
        have hL : max (max a0 a2) (max a1 a3) = max (max a0 a1) (max a2 a3) := by omega
        have hR : max (max a4 a6) (max a5 a7) = max (max a4 a5) (max a6 a7) := by omega
        rw [hL, hR]
      exact hmax8 _ _ _ _ _ _ _ _
    intro a b c d hab hac had hbc hbd hcd
    suffices hord2 : ∀ x y z w : Fin 32, x < y → x ≠ z → x ≠ w → y ≠ z → y ≠ w → z ≠ w →
        maxC4 paley32 x y z w ≤ 5 by
      by_cases h : a < b
      · exact hord2 a b c d h hac had hbc hbd hcd
      · rw [← hswap01]
        have hba : b < a := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (fun hv => hab (Fin.ext hv.symm))
        exact hord2 b a c d hba hbc hbd hac had hcd
    intro x y z w hxy hxz hxw hyz hyw hzw
    suffices hord3 : ∀ x y z w : Fin 32, x < y → z < w → x ≠ z → x ≠ w → y ≠ z → y ≠ w →
        maxC4 paley32 x y z w ≤ 5 by
      by_cases h : z < w
      · exact hord3 x y z w hxy h hxz hxw hyz hyw
      · rw [← maxC4_swap23]
        have hwz : w < z := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (fun hv => hzw (Fin.ext hv.symm))
        exact hord3 x y w z hxy hwz hxw hxz hyw hyz
    intro x y z w hxy hzw hxz hxw hyz hyw
    by_cases hyz' : y < z
    · exact paley32_maxC4_le_5 x y z w hxy hyz' hzw
    · have hzy : z < y := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hyz') (fun hv => hyz (Fin.ext hv.symm))
      by_cases hxz' : x < z
      · by_cases hyw' : y < w
        · rw [← hswap12]; exact paley32_maxC4_le_5 x z y w hxz' hzy hyw'
        · have hwy : w < y := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hyw') (fun hv => hyw (Fin.ext hv.symm))
          rw [← hswap12, ← maxC4_swap23]; exact paley32_maxC4_le_5 x z w y hxz' hzw hwy
      · have hzx : z < x := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hxz') (fun hv => hxz (Fin.ext hv.symm))
        by_cases hwx' : w < x
        · rw [← hswap12, ← hswap01, ← maxC4_swap23, ← hswap12]
          exact paley32_maxC4_le_5 z w x y hzw hwx' hxy
        · have hxw' : x < w := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hwx') (fun hv => hxw (Fin.ext hv))
          by_cases hwy' : w < y
          · rw [← hswap12, ← hswap01, ← maxC4_swap23]
            exact paley32_maxC4_le_5 z x w y hzx hxw' hwy'
          · have hyw' : y < w := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hwy') (fun hv => hyw (Fin.ext hv))
            rw [← hswap12, ← hswap01]
            exact paley32_maxC4_le_5 z x y w hzx hxy hyw'
  have hrel : ∀ s1 s2 s3, (s1 = 1 ∨ s1 = -1) → (s2 = 1 ∨ s2 = -1) → (s3 = 1 ∨ s3 = -1) →
      c4ForSigns (transpose paley32) r0 r1 r2 r3 s1 s2 s3 =
      c4ForSigns paley32 (neg31 r0) (neg31 r1) (neg31 r2) (neg31 r3)
        (s1 * sign0 r0 * sign0 r1) (s2 * sign0 r0 * sign0 r2) (s3 * sign0 r0 * sign0 r3) := by
    intro s1 s2 s3 _ _ _
    unfold c4ForSigns transpose
    have hbij := sumFinNat_bijection neg31 neg31 neg31_involutive neg31_involutive
      (fun c => if (paley32 c (neg31 r0) + (s1 * sign0 r0 * sign0 r1) * paley32 c (neg31 r1) +
                    (s2 * sign0 r0 * sign0 r2) * paley32 c (neg31 r2) +
                    (s3 * sign0 r0 * sign0 r3) * paley32 c (neg31 r3)).natAbs = 4 then 1 else 0)
    rw [← hbij]
    apply sumFinNat_congr
    intro c
    rw [paley32_transpose_equiv c r0, paley32_transpose_equiv c r1,
        paley32_transpose_equiv c r2, paley32_transpose_equiv c r3]
    have hs0 : ∀ x, sign0 x = 1 ∨ sign0 x = -1 := by intro x; unfold sign0; split <;> simp
    have hsq1 : ∀ x, sign0 x * sign0 x = 1 := by intro x; rcases hs0 x with h | h <;> simp [h]
    have hpm_abs : ∀ (u v : Int), (u = 1 ∨ u = -1) → (u * v).natAbs = v.natAbs := by
      intro u v hu; rcases hu with rfl | rfl
      · simp
      · have : -1 * v = -v := by omega
        rw [this, Int.natAbs_neg]
    have hfact : sign0 c * sign0 r0 * paley32 (neg31 c) (neg31 r0) +
                 s1 * (sign0 c * sign0 r1 * paley32 (neg31 c) (neg31 r1)) +
                 s2 * (sign0 c * sign0 r2 * paley32 (neg31 c) (neg31 r2)) +
                 s3 * (sign0 c * sign0 r3 * paley32 (neg31 c) (neg31 r3)) =
                 (sign0 c * sign0 r0) *
                 (paley32 (neg31 c) (neg31 r0) +
                  (s1 * sign0 r0 * sign0 r1) * paley32 (neg31 c) (neg31 r1) +
                  (s2 * sign0 r0 * sign0 r2) * paley32 (neg31 c) (neg31 r2) +
                  (s3 * sign0 r0 * sign0 r3) * paley32 (neg31 c) (neg31 r3)) := by
      have h0 := hsq1 r0
      grind
    rw [hfact, hpm_abs (sign0 c * sign0 r0) _ (by rcases hs0 c with h1 | h1 <;> rcases hs0 r0 with h2 | h2 <;> simp [h1, h2])]
  have hc4_le_max : ∀ (H : IntMat 32 32) (a b c d : Fin 32) (t1 t2 t3 : Int),
      (t1 = 1 ∨ t1 = -1) → (t2 = 1 ∨ t2 = -1) → (t3 = 1 ∨ t3 = -1) →
      c4ForSigns H a b c d t1 t2 t3 ≤ maxC4 H a b c d := by
    intro H a b c d t1 t2 t3 ht1 ht2 ht3
    unfold maxC4; dsimp only
    rcases ht1 with rfl | rfl <;> rcases ht2 with rfl | rfl <;> rcases ht3 with rfl | rfl <;> omega
  have hle_max : maxC4 (transpose paley32) r0 r1 r2 r3 ≤
                 maxC4 paley32 (neg31 r0) (neg31 r1) (neg31 r2) (neg31 r3) := by
    have hs0 : ∀ x, sign0 x = 1 ∨ sign0 x = -1 := by intro x; unfold sign0; split <;> simp
    have hpm3 : ∀ a b c : Int, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → (c = 1 ∨ c = -1) →
        (a * b * c = 1 ∨ a * b * c = -1) := by
      intro a b c ha hb hc; rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> simp
    have h1 : ∀ s1 s2 s3, (s1 = 1 ∨ s1 = -1) → (s2 = 1 ∨ s2 = -1) → (s3 = 1 ∨ s3 = -1) →
        c4ForSigns (transpose paley32) r0 r1 r2 r3 s1 s2 s3 ≤
        maxC4 paley32 (neg31 r0) (neg31 r1) (neg31 r2) (neg31 r3) := by
      intro s1 s2 s3 hs1 hs2 hs3
      rw [hrel s1 s2 s3 hs1 hs2 hs3]
      exact hc4_le_max paley32 _ _ _ _ _ _ _
        (hpm3 _ _ _ hs1 (hs0 r0) (hs0 r1))
        (hpm3 _ _ _ hs2 (hs0 r0) (hs0 r2))
        (hpm3 _ _ _ hs3 (hs0 r0) (hs0 r3))
    have m0 := h1 1 1 1 (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
    have m1 := h1 (-1) 1 1 (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
    have m2 := h1 1 (-1) 1 (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
    have m3 := h1 (-1) (-1) 1 (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
    have m4 := h1 1 1 (-1) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
    have m5 := h1 (-1) 1 (-1) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
    have m6 := h1 1 (-1) (-1) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
    have m7 := h1 (-1) (-1) (-1) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
    unfold maxC4; dsimp only
    unfold maxC4 at m0 m1 m2 m3 m4 m5 m6 m7
    dsimp only at m0 m1 m2 m3 m4 m5 m6 m7
    omega
  have hneg_inj : ∀ x y : Fin 32, neg31 x = neg31 y → x = y := by
    intro x y h; have := congrArg neg31 h; rw [neg31_involutive, neg31_involutive] at this; exact this
  exact Nat.le_trans hle_max (hmaxC4_symm (neg31 r0) (neg31 r1) (neg31 r2) (neg31 r3)
    (mt (hneg_inj _ _) h01) (mt (hneg_inj _ _) h02) (mt (hneg_inj _ _) h03)
    (mt (hneg_inj _ _) h12) (mt (hneg_inj _ _) h13) (mt (hneg_inj _ _) h23))

theorem int_eq_of_natAbs_eq {a : Int} {k : Nat} (h : a.natAbs = k) :
    a = (k : Int) ∨ a = -(k : Int) := by
  have := Int.natAbs_eq a
  omega

/-- Row-support duality lemma: if 3 distinct rows of `paley32` hit `|y_r| = 8` on an 8-sparse
    signed vector `x`, then EVERY 4th distinct row `r3` satisfies `|y_{r3}| ≤ 2`! -/
theorem paley32_three_peak8_forces_other_le_2 (x : Fin 32 → Int) (hx : isSignedSparse 8 x)
    (r0 r1 r2 r3 : Fin 32)
    (h01 : r0 ≠ r1) (h02 : r0 ≠ r2) (h03 : r0 ≠ r3)
    (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hp0 : (matVec paley32 x r0).natAbs = 8)
    (hp1 : (matVec paley32 x r1).natAbs = 8)
    (hp2 : (matVec paley32 x r2).natAbs = 8) :
    (matVec paley32 x r3).natAbs ≤ 2 := by
  have hpeak_align : ∀ r : Fin 32, (matVec paley32 x r).natAbs = 8 →
      ∃ s : Int, (s = 1 ∨ s = -1) ∧ ∀ j : Fin 32, x j ≠ 0 → paley32 r j = s * x j := by
    intro r hpr
    have hpos_all : ∀ s : Int, (s = 1 ∨ s = -1) → matVec paley32 x r = s * 8 →
        ∀ j0 : Fin 32, x j0 ≠ 0 → paley32 r j0 = s * x j0 := by
      intro s hs hval j0 hj0
      have hsum8 : sumFinInt 32 (fun j => s * (paley32 r j * x j)) = 8 := by
        rw [sumFinInt_mul_left]; change s * matVec paley32 x r = 8; rw [hval]
        rcases hs with rfl | rfl <;> omega
      have hterm_le : ∀ j : Fin 32, s * (paley32 r j * x j) ≤ (if x j = 0 then 0 else 1) := by
        intro j
        rcases hs with rfl | rfl <;> rcases paley32_pm r j with hp | hp <;>
        rcases hx.1 j with hx0 | hx0 | hx0 <;> simp [hp, hx0]
      have hterm_eq : s * (paley32 r j0 * x j0) = 1 := by
        apply Classical.byContradiction
        intro hne
        have hneg1 : s * (paley32 r j0 * x j0) ≤ -1 := by
          rcases hs with rfl | rfl <;> rcases paley32_pm r j0 with hp | hp <;>
          rcases hx.1 j0 with hx0 | hx0 | hx0 <;> simp_all
        have hsum_le : sumFinInt 32 (fun j => s * (paley32 r j * x j)) ≤
                       sumFinInt 32 (fun j => if j = j0 then -1 else if x j = 0 then 0 else 1) := by
          apply sumFinInt_le
          intro j
          by_cases h : j = j0
          · subst h; simp [hneg1]
          · simp [h, hterm_le j]
        have h2 : sumFinInt 32 (fun j => if j = j0 then (2 : Int) else 0) = 2 := by
          have hsng : ∀ k : Fin 32, sumFinInt 32 (fun j => if j = k then (2 : Int) else 0) = 2 := by decide
          exact hsng j0
        have h8 : sumFinInt 32 (fun j => if x j = 0 then (0 : Int) else 1) = 8 := by
          have h := sumFinNat_toInt (fun j : Fin 32 => if x j = 0 then 0 else 1)
          rw [hx.2] at h
          have hcongr : sumFinInt 32 (fun j => if x j = 0 then (0 : Int) else 1) =
                        sumFinInt 32 (fun j => ((if x j = 0 then 0 else 1 : Nat) : Int)) :=
            sumFinInt_congr _ _ (fun j => by split <;> rfl)
          rw [hcongr, ← h]; rfl
        have hdiff := sumFinInt_add
          (fun j : Fin 32 => if j = j0 then (-1 : Int) else if x j = 0 then 0 else 1)
          (fun j : Fin 32 => if j = j0 then (2 : Int) else 0)
        have hc : sumFinInt 32 (fun j : Fin 32 => (if j = j0 then (-1 : Int) else if x j = 0 then 0 else 1) +
                                                  (if j = j0 then (2 : Int) else 0)) =
                  sumFinInt 32 (fun j : Fin 32 => if x j = 0 then (0 : Int) else 1) := by
          apply sumFinInt_congr; intro j; by_cases h : j = j0
          · subst h; simp [hj0]
          · simp [h]
        rw [hc, h2, h8] at hdiff
        omega
      rcases hs with rfl | rfl <;> rcases paley32_pm r j0 with hp | hp <;>
      rcases hx.1 j0 with hx0 | hx0 | hx0 <;> simp_all
    rcases int_eq_of_natAbs_eq hpr with h8 | hm8
    · exact ⟨1, Or.inl rfl, hpos_all 1 (Or.inl rfl) (by omega)⟩
    · exact ⟨-1, Or.inr rfl, hpos_all (-1) (Or.inr rfl) (by omega)⟩
  rcases hpeak_align r0 hp0 with ⟨s0, hs0, ha0⟩
  rcases hpeak_align r1 hp1 with ⟨s1, hs1, ha1⟩
  rcases hpeak_align r2 hp2 with ⟨s2, hs2, ha2⟩
  let a := sumFinNat 32 (fun j => if x j ≠ 0 ∧ paley32 r3 j = x j then 1 else 0)
  let b := sumFinNat 32 (fun j => if x j ≠ 0 ∧ paley32 r3 j = -x j then 1 else 0)
  have hab_sum : a + b = 8 := by
    dsimp only [a, b]
    rw [← sumFinNat_add, ← hx.2]
    apply sumFinNat_congr
    intro j
    rcases paley32_pm r3 j with hp | hp <;> rcases hx.1 j with hx0 | hx0 | hx0 <;> simp [hp, hx0]
  have hy3 : matVec paley32 x r3 = (a : Int) - (b : Int) := by
    unfold matVec
    dsimp only [a, b]
    rw [sumFinNat_toInt, sumFinNat_toInt]
    have hadd := sumFinInt_add
      (fun j : Fin 32 => paley32 r3 j * x j)
      (fun j : Fin 32 => ((if x j ≠ 0 ∧ paley32 r3 j = -x j then 1 else 0 : Nat) : Int))
    have hc : sumFinInt 32 (fun j : Fin 32 => paley32 r3 j * x j +
                                              ((if x j ≠ 0 ∧ paley32 r3 j = -x j then 1 else 0 : Nat) : Int)) =
              sumFinInt 32 (fun j : Fin 32 => ((if x j ≠ 0 ∧ paley32 r3 j = x j then 1 else 0 : Nat) : Int)) := by
      apply sumFinInt_congr
      intro j
      rcases paley32_pm r3 j with hp | hp <;> rcases hx.1 j with hx0 | hx0 | hx0 <;> simp [hp, hx0]
    omega
  have hmax5 := paley32_transpose_maxC4_le_5 r0 r1 r2 r3 h01 h02 h03 h12 h13 h23
  have hle_c4 : ∀ (s3 : Int), (s3 = 1 ∨ s3 = -1) →
      sumFinNat 32 (fun j => if x j ≠ 0 ∧ paley32 r3 j = s3 * x j then 1 else 0) ≤
      c4ForSigns (transpose paley32) r0 r1 r2 r3 (s0 * s1) (s0 * s2) (s0 * s3) := by
    intro s3 hs3
    unfold c4ForSigns transpose
    apply sumFinNat_le
    intro j
    by_cases hj : x j ≠ 0 ∧ paley32 r3 j = s3 * x j
    · have hlhs : (if x j ≠ 0 ∧ paley32 r3 j = s3 * x j then 1 else 0) = 1 := by simp [hj]
      rw [hlhs]
      have h0 := ha0 j hj.1
      have h1 := ha1 j hj.1
      have h2 := ha2 j hj.1
      have h3 := hj.2
      rw [h0, h1, h2, h3]
      rcases hs0 with rfl | rfl <;> rcases hs1 with rfl | rfl <;>
      rcases hs2 with rfl | rfl <;> rcases hs3 with rfl | rfl <;>
      rcases hx.1 j with hx0 | hx0 | hx0 <;> simp_all
    · simp [hj]
  have hc4_le_max : ∀ t1 t2 t3, (t1 = 1 ∨ t1 = -1) → (t2 = 1 ∨ t2 = -1) → (t3 = 1 ∨ t3 = -1) →
      c4ForSigns (transpose paley32) r0 r1 r2 r3 t1 t2 t3 ≤
      maxC4 (transpose paley32) r0 r1 r2 r3 := by
    intro t1 t2 t3 ht1 ht2 ht3
    unfold maxC4
    dsimp only
    rcases ht1 with rfl | rfl <;> rcases ht2 with rfl | rfl <;> rcases ht3 with rfl | rfl <;> omega
  have ha_le : a ≤ 5 := by
    have h1 := hle_c4 1 (Or.inl rfl)
    have hcongr : a = sumFinNat 32 (fun j => if x j ≠ 0 ∧ paley32 r3 j = 1 * x j then 1 else 0) :=
      sumFinNat_congr _ _ (fun j => by simp)
    rw [hcongr]
    have h2 : c4ForSigns (transpose paley32) r0 r1 r2 r3 (s0 * s1) (s0 * s2) (s0 * 1) ≤
              maxC4 (transpose paley32) r0 r1 r2 r3 :=
      hc4_le_max _ _ _
        (by rcases hs0 with rfl | rfl <;> rcases hs1 with rfl | rfl <;> simp)
        (by rcases hs0 with rfl | rfl <;> rcases hs2 with rfl | rfl <;> simp)
        (by rcases hs0 with rfl | rfl <;> simp)
    omega
  have hb_le : b ≤ 5 := by
    have h1 := hle_c4 (-1) (Or.inr rfl)
    have hcongr : b = sumFinNat 32 (fun j => if x j ≠ 0 ∧ paley32 r3 j = (-1) * x j then 1 else 0) :=
      sumFinNat_congr _ _ (fun j => by simp)
    rw [hcongr]
    have h2 : c4ForSigns (transpose paley32) r0 r1 r2 r3 (s0 * s1) (s0 * s2) (s0 * (-1)) ≤
              maxC4 (transpose paley32) r0 r1 r2 r3 :=
      hc4_le_max _ _ _
        (by rcases hs0 with rfl | rfl <;> rcases hs1 with rfl | rfl <;> simp)
        (by rcases hs0 with rfl | rfl <;> rcases hs2 with rfl | rfl <;> simp)
        (by rcases hs0 with rfl | rfl <;> simp)
    omega
  rw [hy3]
  omega

theorem count_ge_1_exists {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : 1 ≤ sumFinNat n (fun i => if P i then 1 else 0)) :
    ∃ i0 : Fin n, P i0 := by
  apply Classical.byContradiction
  intro hnone
  have hz : sumFinNat n (fun i => if P i then 1 else 0) = 0 := by
    have h0 : ∀ i, (if P i then 1 else 0) = 0 := by
      intro i; have : ¬ P i := fun hp => hnone ⟨i, hp⟩; simp [this]
    rw [sumFinNat_congr _ (fun _ => 0) h0, sumFinNat_zero]
  omega

theorem count_ge_3_exists {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : 3 ≤ sumFinNat n (fun i => if P i then 1 else 0)) :
    ∃ r0 r1 r2 : Fin n, r0 ≠ r1 ∧ r0 ≠ r2 ∧ r1 ≠ r2 ∧ P r0 ∧ P r1 ∧ P r2 := by
  rcases count_ge_1_exists P (by omega) with ⟨r0, hp0⟩
  have h1 := sumFinNat_eq_single_add (fun i => if P i then 1 else 0) r0
  simp only [hp0, ↓reduceIte] at h1
  let P1 : Fin n → Prop := fun i => i ≠ r0 ∧ P i
  have hc1 : sumFinNat n (fun i => if i = r0 then 0 else if P i then 1 else 0) =
             sumFinNat n (fun i => if P1 i then 1 else 0) :=
    sumFinNat_congr _ _ (fun i => by by_cases hi : i = r0 <;> simp [P1, hi])
  rcases count_ge_1_exists P1 (by omega) with ⟨r1, h10, hp1⟩
  have h2 := sumFinNat_eq_single_add (fun i => if P1 i then 1 else 0) r1
  have hr1_p1 : P1 r1 := ⟨h10, hp1⟩
  simp only [hr1_p1, ↓reduceIte] at h2
  let P2 : Fin n → Prop := fun i => i ≠ r1 ∧ P1 i
  have hc2 : sumFinNat n (fun i => if i = r1 then 0 else if P1 i then 1 else 0) =
             sumFinNat n (fun i => if P2 i then 1 else 0) :=
    sumFinNat_congr _ _ (fun i => by by_cases hi : i = r1 <;> simp [P2, hi])
  rcases count_ge_1_exists P2 (by omega) with ⟨r2, h21, h20, hp2⟩
  exact ⟨r0, r1, r2, Ne.symm h10, Ne.symm h20, Ne.symm h21, hp0, hp1, hp2⟩

theorem count_ge_4_exists {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : 4 ≤ sumFinNat n (fun i => if P i then 1 else 0)) :
    ∃ r0 r1 r2 r3 : Fin n,
      r0 ≠ r1 ∧ r0 ≠ r2 ∧ r0 ≠ r3 ∧ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ∧
      P r0 ∧ P r1 ∧ P r2 ∧ P r3 := by
  rcases count_ge_3_exists P (by omega) with ⟨r0, r1, r2, h01, h02, h12, hp0, hp1, hp2⟩
  have s0 := sumFinNat_eq_single_add (fun i => if P i then 1 else 0) r0
  have s1 := sumFinNat_eq_single_add (fun i => if i = r0 then 0 else if P i then 1 else 0) r1
  have s2 := sumFinNat_eq_single_add (fun i => if i = r1 then 0 else if i = r0 then 0 else if P i then 1 else 0) r2
  simp only [hp0, hp1, hp2, Ne.symm h01, Ne.symm h02, Ne.symm h12, ↓reduceIte] at s0 s1 s2
  let P3 : Fin n → Prop := fun i => i ≠ r2 ∧ i ≠ r1 ∧ i ≠ r0 ∧ P i
  have hc3 : sumFinNat n (fun i => if i = r2 then 0 else if i = r1 then 0 else if i = r0 then 0 else if P i then 1 else 0) =
             sumFinNat n (fun i => if P3 i then 1 else 0) :=
    sumFinNat_congr _ _ (fun i => by
      by_cases h2 : i = r2 <;> by_cases h1 : i = r1 <;> by_cases h0 : i = r0 <;> simp [P3, h2, h1, h0])
  rcases count_ge_1_exists P3 (by omega) with ⟨r3, h32, h31, h30, hp3⟩
  exact ⟨r0, r1, r2, r3, h01, h02, Ne.symm h30, h12, Ne.symm h31, Ne.symm h32, hp0, hp1, hp2, hp3⟩

theorem sumSqInt_matVec_of_orthogonal {n : Nat} (H : IntMat n n) (c : Int)
    (hH : isOrthogonal H c) (x : Fin n → Int) :
    sumSqInt (matVec H x) = c * sumSqInt x := by
  unfold sumSqInt matVec
  have hexp : sumFinInt n (fun i => sumFinInt n (fun j => H i j * x j) * sumFinInt n (fun k => H i k * x k)) =
              sumFinInt n (fun j => sumFinInt n (fun k => (sumFinInt n (fun i => H i j * H i k)) * (x j * x k))) := by
    have h1 : sumFinInt n (fun i => sumFinInt n (fun j => H i j * x j) * sumFinInt n (fun k => H i k * x k)) =
              sumFinInt n (fun i => sumFinInt n (fun j => sumFinInt n (fun k => (H i j * H i k) * (x j * x k)))) := by
      apply sumFinInt_congr; intro i
      rw [← sumFinInt_mul_right]
      apply sumFinInt_congr; intro j
      rw [← sumFinInt_mul_left]
      apply sumFinInt_congr; intro k
      grind
    rw [h1, sumFinInt_swap]
    apply sumFinInt_congr; intro j
    rw [sumFinInt_swap]
    apply sumFinInt_congr; intro k
    rw [sumFinInt_mul_right]
  rw [hexp]
  have hdiag : ∀ j k : Fin n, sumFinInt n (fun i => H i j * H i k) = if j = k then c else 0 := by
    intro j k
    have h := congrFun (congrFun hH j) k
    simp only [matMul, transpose, scaleMat, idMat] at h
    by_cases hjk : j = k
    · simp [hjk] at h ⊢; omega
    · simp [hjk] at h ⊢; exact h
  have hsimp : sumFinInt n (fun j => sumFinInt n (fun k => (sumFinInt n (fun i => H i j * H i k)) * (x j * x k))) =
               sumFinInt n (fun j => c * (x j * x j)) := by
    apply sumFinInt_congr; intro j
    have hcongr : sumFinInt n (fun k => (sumFinInt n (fun i => H i j * H i k)) * (x j * x k)) =
                  sumFinInt n (fun k => if k = j then c * (x j * x j) else 0) := by
      apply sumFinInt_congr; intro k
      rw [hdiag j k]
      by_cases hjk : j = k
      · subst hjk; simp
      · have hkj : k ≠ j := Ne.symm hjk; simp [hjk, hkj]
    rw [hcongr]
    have hsingle : ∀ (m : Nat) (k0 : Fin m) (v : Int),
        sumFinInt m (fun k => if k = k0 then v else 0) = v := by
      intro m k0 v; induction m with
      | zero => exact Fin.elim0 k0
      | succ p ihp =>
        simp only [sumFinInt]
        by_cases hl : k0 = Fin.last p
        · subst hl
          have hz : sumFinInt p (fun k : Fin p => if k.castSucc = Fin.last p then v else 0) = 0 := by
            have h0 : ∀ k : Fin p, (if k.castSucc = Fin.last p then v else 0) = 0 := by
              intro k; have hne : k.castSucc ≠ Fin.last p := by
                intro h; have : k.castSucc.val = p := congrArg Fin.val h; simp at this; omega
              simp [hne]
            rw [sumFinInt_congr _ (fun _ => 0) h0, sumFinInt_zero]
          simp [hz]
        · have hlt : k0.val < p := by
            have := k0.isLt; have hne : k0.val ≠ p := fun hv => hl (Fin.ext hv); omega
          let k0' : Fin p := ⟨k0.val, hlt⟩
          have hk0 : k0 = k0'.castSucc := Fin.ext rfl
          have hne_l : Fin.last p ≠ k0 := Ne.symm hl
          simp only [hne_l, ↓reduceIte]
          have hc : sumFinInt p (fun k : Fin p => if k.castSucc = k0 then v else 0) =
                    sumFinInt p (fun k : Fin p => if k = k0' then v else 0) := by
            apply sumFinInt_congr; intro k
            have hiff : (k.castSucc = k0) ↔ (k = k0') := by
              rw [hk0]; constructor
              · intro h; have hv : k.castSucc.val = k0'.castSucc.val := congrArg Fin.val h; exact Fin.ext hv
              · intro h; rw [h]
            by_cases h : k = k0'
            · subst h; simp [hk0]
            · simp [mt hiff.mp h, h]
          rw [hc, ihp k0']
          omega
    exact hsingle n j (c * (x j * x j))
  rw [hsimp, sumFinInt_mul_left]

theorem paley32_k8_coord_even_le8 (x : Fin 32 → Int) (hx : isSignedSparse 8 x) (r : Fin 32) :
    (matVec paley32 x r).natAbs = 0 ∨ (matVec paley32 x r).natAbs = 2 ∨
    (matVec paley32 x r).natAbs = 4 ∨ (matVec paley32 x r).natAbs = 6 ∨
    (matVec paley32 x r).natAbs = 8 := by
  let a := sumFinNat 32 (fun j => if x j ≠ 0 ∧ paley32 r j = x j then 1 else 0)
  let b := sumFinNat 32 (fun j => if x j ≠ 0 ∧ paley32 r j = -x j then 1 else 0)
  have hab : a + b = 8 := by
    dsimp only [a, b]
    rw [← sumFinNat_add, ← hx.2]
    apply sumFinNat_congr; intro j
    rcases paley32_pm r j with hp | hp <;> rcases hx.1 j with hx0 | hx0 | hx0 <;> simp [hp, hx0]
  have hy : matVec paley32 x r = (a : Int) - (b : Int) := by
    unfold matVec; dsimp only [a, b]; rw [sumFinNat_toInt, sumFinNat_toInt]
    have hadd := sumFinInt_add
      (fun j : Fin 32 => paley32 r j * x j)
      (fun j : Fin 32 => ((if x j ≠ 0 ∧ paley32 r j = -x j then 1 else 0 : Nat) : Int))
    have hc : sumFinInt 32 (fun j : Fin 32 => paley32 r j * x j +
                                              ((if x j ≠ 0 ∧ paley32 r j = -x j then 1 else 0 : Nat) : Int)) =
              sumFinInt 32 (fun j : Fin 32 => ((if x j ≠ 0 ∧ paley32 r j = x j then 1 else 0 : Nat) : Int)) := by
      apply sumFinInt_congr; intro j
      rcases paley32_pm r j with hp | hp <;> rcases hx.1 j with hx0 | hx0 | hx0 <;> simp [hp, hx0]
    omega
  rw [hy]
  omega

theorem paley32_k8_universal_bound (x : Fin 32 → Int) (hx : isSignedSparse 8 x) :
    countAbsEq (matVec paley32 x) 8 ≤ 3 ∧ sumFourthInt (matVec paley32 x) ≤ 12544 := by
  have hn8_le3 : countAbsEq (matVec paley32 x) 8 ≤ 3 := by
    apply Classical.byContradiction
    intro hgt
    have hge4 : 4 ≤ sumFinNat 32 (fun r => if (matVec paley32 x r).natAbs = 8 then 1 else 0) := by
      unfold countAbsEq at hgt; omega
    rcases count_ge_4_exists (fun r => (matVec paley32 x r).natAbs = 8) hge4 with
      ⟨r0, r1, r2, r3, h01, h02, h03, h12, h13, h23, hp0, hp1, hp2, hp3⟩
    have hle2 := paley32_three_peak8_forces_other_le_2 x hx r0 r1 r2 r3 h01 h02 h03 h12 h13 h23 hp0 hp1 hp2
    omega
  have hsq256 : sumSqInt (matVec paley32 x) = 256 := by
    have h1 := sumSqInt_matVec_of_orthogonal paley32 32 paley32_orthogonal x
    have hxsq : sumSqInt x = 8 := by
      unfold sumSqInt
      have h := sumFinNat_toInt (fun j : Fin 32 => if x j = 0 then 0 else 1)
      rw [hx.2] at h
      have hcongr : sumFinInt 32 (fun i => x i * x i) =
                    sumFinInt 32 (fun j => ((if x j = 0 then 0 else 1 : Nat) : Int)) := by
        apply sumFinInt_congr; intro j
        rcases hx.1 j with h0 | h0 | h0 <;> simp [h0]
      rw [hcongr, ← h]; rfl
    rw [hxsq] at h1
    exact h1
  constructor
  · exact hn8_le3
  · by_cases hn8_3 : countAbsEq (matVec paley32 x) 8 = 3
    · rcases count_ge_3_exists (fun r => (matVec paley32 x r).natAbs = 8)
        (by unfold countAbsEq at hn8_3; omega) with
        ⟨r0, r1, r2, h01, h02, h12, hp0, hp1, hp2⟩
      have hother_le2 : ∀ r : Fin 32, (matVec paley32 x r).natAbs ≠ 8 → (matVec paley32 x r).natAbs ≤ 2 := by
        intro r hne8
        have hr0 : r0 ≠ r := fun h => hne8 (h ▸ hp0)
        have hr1 : r1 ≠ r := fun h => hne8 (h ▸ hp1)
        have hr2 : r2 ≠ r := fun h => hne8 (h ▸ hp2)
        exact paley32_three_peak8_forces_other_le_2 x hx r0 r1 r2 r h01 h02 hr0 h12 hr1 hr2 hp0 hp1 hp2
      have hpoint : ∀ r : Fin 32,
          matVec paley32 x r * matVec paley32 x r * matVec paley32 x r * matVec paley32 x r ≤
          4 * (matVec paley32 x r * matVec paley32 x r) +
          3840 * ((if (matVec paley32 x r).natAbs = 8 then 1 else 0 : Nat) : Int) := by
        intro r
        by_cases h8 : (matVec paley32 x r).natAbs = 8
        · rcases int_eq_of_natAbs_eq h8 with h | h <;> simp [h]
        · have hle2 := hother_le2 r h8
          have ha := Int.natAbs_eq (matVec paley32 x r)
          have hy2 : matVec paley32 x r = -2 ∨ matVec paley32 x r = -1 ∨
                     matVec paley32 x r = 0 ∨ matVec paley32 x r = 1 ∨ matVec paley32 x r = 2 := by omega
          rcases hy2 with h | h | h | h | h <;> simp [h]
      have hsum := sumFinInt_le _ _ hpoint
      rw [sumFinInt_add, sumFinInt_mul_left, sumFinInt_mul_left, ← sumFinNat_toInt] at hsum
      change sumFourthInt (matVec paley32 x) ≤ 4 * sumSqInt (matVec paley32 x) + 3840 * (countAbsEq (matVec paley32 x) 8 : Int) at hsum
      rw [hsq256, hn8_3] at hsum
      omega
    · by_cases hn8_2 : countAbsEq (matVec paley32 x) 8 = 2
      · have hn6_le3 : countAbsEq (matVec paley32 x) 6 ≤ 3 := by
          have hlow : ∀ r : Fin 32,
              64 * ((if (matVec paley32 x r).natAbs = 8 then 1 else 0 : Nat) : Int) +
              36 * ((if (matVec paley32 x r).natAbs = 6 then 1 else 0 : Nat) : Int) ≤
              matVec paley32 x r * matVec paley32 x r := by
            intro r
            rcases paley32_k8_coord_even_le8 x hx r with h | h | h | h | h <;>
            rcases int_eq_of_natAbs_eq h with hy | hy <;> simp [hy]
          have hsum := sumFinInt_le _ _ hlow
          rw [sumFinInt_add, sumFinInt_mul_left, sumFinInt_mul_left, ← sumFinNat_toInt, ← sumFinNat_toInt] at hsum
          change 64 * (countAbsEq (matVec paley32 x) 8 : Int) + 36 * (countAbsEq (matVec paley32 x) 6 : Int) ≤
                 sumSqInt (matVec paley32 x) at hsum
          rw [hsq256, hn8_2] at hsum
          omega
        have hpoint : ∀ r : Fin 32,
            matVec paley32 x r * matVec paley32 x r * matVec paley32 x r * matVec paley32 x r ≤
            16 * (matVec paley32 x r * matVec paley32 x r) +
            3072 * ((if (matVec paley32 x r).natAbs = 8 then 1 else 0 : Nat) : Int) +
            720 * ((if (matVec paley32 x r).natAbs = 6 then 1 else 0 : Nat) : Int) := by
          intro r
          rcases paley32_k8_coord_even_le8 x hx r with h | h | h | h | h <;>
          rcases int_eq_of_natAbs_eq h with hy | hy <;> simp [hy]
        have hsum := sumFinInt_le _ _ hpoint
        rw [sumFinInt_add, sumFinInt_add, sumFinInt_mul_left, sumFinInt_mul_left, sumFinInt_mul_left,
            ← sumFinNat_toInt, ← sumFinNat_toInt] at hsum
        change sumFourthInt (matVec paley32 x) ≤
               16 * sumSqInt (matVec paley32 x) +
               3072 * (countAbsEq (matVec paley32 x) 8 : Int) +
               720 * (countAbsEq (matVec paley32 x) 6 : Int) at hsum
        rw [hsq256, hn8_2] at hsum
        omega
      · have hn8_le1 : countAbsEq (matVec paley32 x) 8 ≤ 1 := by omega
        have hpoint : ∀ r : Fin 32,
            matVec paley32 x r * matVec paley32 x r * matVec paley32 x r * matVec paley32 x r ≤
            36 * (matVec paley32 x r * matVec paley32 x r) +
            1792 * ((if (matVec paley32 x r).natAbs = 8 then 1 else 0 : Nat) : Int) := by
          intro r
          rcases paley32_k8_coord_even_le8 x hx r with h | h | h | h | h <;>
          rcases int_eq_of_natAbs_eq h with hy | hy <;> simp [hy]
        have hsum := sumFinInt_le _ _ hpoint
        rw [sumFinInt_add, sumFinInt_mul_left, sumFinInt_mul_left, ← sumFinNat_toInt] at hsum
        change sumFourthInt (matVec paley32 x) ≤
               36 * sumSqInt (matVec paley32 x) +
               1792 * (countAbsEq (matVec paley32 x) 8 : Int) at hsum
        rw [hsq256] at hsum
        omega

theorem sylvester32_k8_witness :
    let yS := matVec sylvester32 (supportVec [0, 1, 2, 3, 4, 5, 6, 7])
    countAbsEq yS 8 = 4 ∧ countAbsEq yS 0 = 28 ∧ sumFourthInt yS = 16384 := by
  decide

theorem paley32_k8_witness :
    let yP := matVec paley32 (supportVec [0, 1, 2, 3, 8, 19, 22, 30])
    countAbsEq yP 8 = 3 ∧ sumFourthInt yP = 12544 := by
  decide

theorem paley32_vs_sylvester32_k8_l4_reduction :
    (let yS := matVec sylvester32 (supportVec [0, 1, 2, 3, 4, 5, 6, 7])
     countAbsEq yS 8 = 4 ∧ countAbsEq yS 0 = 28 ∧ sumFourthInt yS = 16384) ∧
    (∀ x : Fin 32 → Int, isSignedSparse 8 x →
      countAbsEq (matVec paley32 x) 8 ≤ 3 ∧
      sumFourthInt (matVec paley32 x) ≤ 12544) ∧
    (let yP := matVec paley32 (supportVec [0, 1, 2, 3, 8, 19, 22, 30])
     countAbsEq yP 8 = 3 ∧ sumFourthInt yP = 12544) ∧
    ((12544 : Rat) / 16384 = 49 / 64) := by
  exact ⟨sylvester32_k8_witness, paley32_k8_universal_bound, paley32_k8_witness, by grind⟩

end Paley32Mxfp4
