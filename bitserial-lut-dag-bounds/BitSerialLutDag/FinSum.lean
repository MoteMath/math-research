/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitSerialLutDag.Defs

/-!
# Finite Sums, `ceilLog2`, Support Bounds, and Finite Pigeonhole (`BitSerialLutDag.FinSum`)
-/

namespace BitSerialLutDag

/-! ## `finSumInt` Algebraic Lemmas -/

theorem finSumAuxInt_congr {n : Nat} {f g : Fin n → Int}
    (h : ∀ i, f i = g i) : ∀ (k : Nat) (hk : k ≤ n),
    finSumAuxInt f k hk = finSumAuxInt g k hk
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [finSumAuxInt, finSumAuxInt_congr h k (Nat.le_of_succ_le hk), h]

theorem finSumInt_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    finSumInt f = finSumInt g :=
  finSumAuxInt_congr h n (Nat.le_refl n)

theorem finSumAuxInt_zero {n : Nat} : ∀ (k : Nat) (hk : k ≤ n),
    finSumAuxInt (fun _ : Fin n => (0 : Int)) k hk = 0
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [finSumAuxInt, finSumAuxInt_zero k (Nat.le_of_succ_le hk)]
    omega

theorem finSumInt_zero {n : Nat} :
    finSumInt (fun _ : Fin n => (0 : Int)) = 0 :=
  finSumAuxInt_zero n (Nat.le_refl n)

theorem finSumAuxInt_add {n : Nat} (f g : Fin n → Int) : ∀ (k : Nat) (hk : k ≤ n),
    finSumAuxInt (fun i => f i + g i) k hk = finSumAuxInt f k hk + finSumAuxInt g k hk
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [finSumAuxInt, finSumAuxInt_add f g k (Nat.le_of_succ_le hk)]
    omega

theorem finSumInt_add {n : Nat} (f g : Fin n → Int) :
    finSumInt (fun i => f i + g i) = finSumInt f + finSumInt g :=
  finSumAuxInt_add f g n (Nat.le_refl n)

theorem finSumAuxInt_sub {n : Nat} (f g : Fin n → Int) : ∀ (k : Nat) (hk : k ≤ n),
    finSumAuxInt (fun i => f i - g i) k hk = finSumAuxInt f k hk - finSumAuxInt g k hk
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [finSumAuxInt, finSumAuxInt_sub f g k (Nat.le_of_succ_le hk)]
    omega

theorem finSumInt_sub {n : Nat} (f g : Fin n → Int) :
    finSumInt (fun i => f i - g i) = finSumInt f - finSumInt g :=
  finSumAuxInt_sub f g n (Nat.le_refl n)

theorem finSumAuxInt_mul_left {n : Nat} (c : Int) (f : Fin n → Int) : ∀ (k : Nat) (hk : k ≤ n),
    finSumAuxInt (fun i => c * f i) k hk = c * finSumAuxInt f k hk
  | 0, _ => by simp [finSumAuxInt]
  | k + 1, hk => by
    simp only [finSumAuxInt, finSumAuxInt_mul_left c f k (Nat.le_of_succ_le hk), Int.mul_add]

theorem finSumInt_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    finSumInt (fun i => c * f i) = c * finSumInt f :=
  finSumAuxInt_mul_left c f n (Nat.le_refl n)

theorem finSumAuxInt_mul_right {n : Nat} (f : Fin n → Int) (c : Int) : ∀ (k : Nat) (hk : k ≤ n),
    finSumAuxInt (fun i => f i * c) k hk = finSumAuxInt f k hk * c
  | 0, _ => by simp [finSumAuxInt]
  | k + 1, hk => by
    simp only [finSumAuxInt, finSumAuxInt_mul_right f c k (Nat.le_of_succ_le hk), Int.add_mul]

theorem finSumInt_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    finSumInt (fun i => f i * c) = finSumInt f * c :=
  finSumAuxInt_mul_right f c n (Nat.le_refl n)

theorem finSumAuxInt_swap {m n : Nat} (f : Fin m → Fin n → Int) :
    ∀ (k : Nat) (hk : k ≤ m),
      finSumAuxInt (fun i => finSumInt (fun j => f i j)) k hk =
        finSumInt (fun j => finSumAuxInt (fun i => f i j) k hk)
  | 0, _ => by
    simp only [finSumAuxInt, finSumInt_zero]
  | k + 1, hk => by
    simp only [finSumAuxInt, finSumAuxInt_swap f k (Nat.le_of_succ_le hk)]
    rw [← finSumInt_add]

theorem finSumInt_swap {m n : Nat} (f : Fin m → Fin n → Int) :
    finSumInt (fun i => finSumInt (fun j => f i j)) =
      finSumInt (fun j => finSumInt (fun i => f i j)) :=
  finSumAuxInt_swap f m (Nat.le_refl m)

theorem finSumAuxInt_ofNat {n : Nat} (f : Fin n → Nat) : ∀ (k : Nat) (hk : k ≤ n),
    finSumAuxInt (fun i => (f i : Int)) k hk = (finSumAuxNat f k hk : Int)
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [finSumAuxInt, finSumAuxNat, finSumAuxInt_ofNat f k (Nat.le_of_succ_le hk)]
    omega

theorem finSumInt_ofNat {n : Nat} (f : Fin n → Nat) :
    finSumInt (fun i => (f i : Int)) = (finSumNat f : Int) :=
  finSumAuxInt_ofNat f n (Nat.le_refl n)

theorem finSumAuxInt_unit_zero {g : Nat} (x : Fin g → Int) (m : Nat) :
    ∀ (k : Nat) (hk : k ≤ g), k ≤ m →
      finSumAuxInt (fun j => unitVec g m j * x j) k hk = 0
  | 0, _, _ => rfl
  | k + 1, hk, hkm => by
    have hlt : k ≠ m := by omega
    rw [finSumAuxInt, finSumAuxInt_unit_zero x m k (Nat.le_of_succ_le hk) (by omega)]
    simp [unitVec, hlt]

theorem finSumAuxInt_unit {g : Nat} (x : Fin g → Int) (m : Nat) (hm : m < g) :
    ∀ (k : Nat) (hk : k ≤ g), m < k →
      finSumAuxInt (fun j => unitVec g m j * x j) k hk = x ⟨m, hm⟩
  | 0, _, hmk => by omega
  | k + 1, hk, hmk => by
    by_cases heq : k = m
    · subst heq
      rw [finSumAuxInt, finSumAuxInt_unit_zero x k k (Nat.le_of_succ_le hk) (Nat.le_refl k)]
      simp [unitVec]
    · have hlt : m < k := by omega
      rw [finSumAuxInt, finSumAuxInt_unit x m hm k (Nat.le_of_succ_le hk) hlt]
      simp [unitVec, heq]

theorem dotInt_unitVec {g : Nat} (x : Fin g → Int) (m : Nat) (hm : m < g) :
    dotInt (unitVec g m) x = x ⟨m, hm⟩ :=
  finSumAuxInt_unit x m hm g (Nat.le_refl g) hm

theorem finSumAuxInt_bound {n : Nat} (f : Fin n → Int) (B : Int)
    (hB : ∀ i, -B ≤ f i ∧ f i ≤ B) : ∀ (k : Nat) (hk : k ≤ n),
    -(k : Int) * B ≤ finSumAuxInt f k hk ∧ finSumAuxInt f k hk ≤ (k : Int) * B
  | 0, _ => by simp [finSumAuxInt]
  | k + 1, hk => by
    have ih := finSumAuxInt_bound f B hB k (Nat.le_of_succ_le hk)
    have hi := hB ⟨k, hk⟩
    simp only [finSumAuxInt]
    constructor
    · have h1 : -((k + 1 : Nat) : Int) * B = -(k : Int) * B + (-B) := by
        have hcast : -((k + 1 : Nat) : Int) = -(k : Int) + (-1) := by omega
        rw [hcast, Int.add_mul]
        omega
      omega
    · have h2 : ((k + 1 : Nat) : Int) * B = (k : Int) * B + B := by
        have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
        rw [hcast, Int.add_mul]
        omega
      omega

theorem finSumInt_bound {n : Nat} (f : Fin n → Int) (B : Int)
    (hB : ∀ i, -B ≤ f i ∧ f i ≤ B) :
    -(n : Int) * B ≤ finSumInt f ∧ finSumInt f ≤ (n : Int) * B :=
  finSumAuxInt_bound f B hB n (Nat.le_refl n)

/-! ## `finSumNat` & Support Lemmas -/

theorem finSumAuxNat_congr {n : Nat} {f g : Fin n → Nat}
    (h : ∀ i, f i = g i) : ∀ (k : Nat) (hk : k ≤ n),
    finSumAuxNat f k hk = finSumAuxNat g k hk
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [finSumAuxNat, finSumAuxNat_congr h k (Nat.le_of_succ_le hk), h]

theorem finSumNat_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    finSumNat f = finSumNat g :=
  finSumAuxNat_congr h n (Nat.le_refl n)

theorem finSumAuxNat_le {n : Nat} {f g : Fin n → Nat}
    (h : ∀ i, f i ≤ g i) : ∀ (k : Nat) (hk : k ≤ n),
    finSumAuxNat f k hk ≤ finSumAuxNat g k hk
  | 0, _ => Nat.le_refl 0
  | k + 1, hk => by
    simp only [finSumAuxNat]
    exact Nat.add_le_add (finSumAuxNat_le h k (Nat.le_of_succ_le hk)) (h ⟨k, hk⟩)

theorem finSumNat_le {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    finSumNat f ≤ finSumNat g :=
  finSumAuxNat_le h n (Nat.le_refl n)

theorem finSumAuxNat_add {n : Nat} (f g : Fin n → Nat) : ∀ (k : Nat) (hk : k ≤ n),
    finSumAuxNat (fun i => f i + g i) k hk = finSumAuxNat f k hk + finSumAuxNat g k hk
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [finSumAuxNat, finSumAuxNat_add f g k (Nat.le_of_succ_le hk)]
    omega

theorem finSumNat_add {n : Nat} (f g : Fin n → Nat) :
    finSumNat (fun i => f i + g i) = finSumNat f + finSumNat g :=
  finSumAuxNat_add f g n (Nat.le_refl n)

theorem finSumAuxNat_const {n : Nat} (c : Nat) : ∀ (k : Nat) (hk : k ≤ n),
    finSumAuxNat (fun _ : Fin n => c) k hk = k * c
  | 0, _ => by simp [finSumAuxNat]
  | k + 1, hk => by
    simp only [finSumAuxNat, finSumAuxNat_const c k (Nat.le_of_succ_le hk), Nat.succ_mul]

theorem finSumNat_const {n : Nat} (c : Nat) :
    finSumNat (fun _ : Fin n => c) = n * c :=
  finSumAuxNat_const c n (Nat.le_refl n)

theorem finSumAuxNat_unit_zero {g : Nat} (m : Nat) :
    ∀ (k : Nat) (hk : k ≤ g), k ≤ m →
      finSumAuxNat (fun j : Fin g => if unitVec g m j ≠ 0 then 1 else 0) k hk = 0
  | 0, _, _ => rfl
  | k + 1, hk, hkm => by
    have hlt : k ≠ m := by omega
    rw [finSumAuxNat, finSumAuxNat_unit_zero m k (Nat.le_of_succ_le hk) (by omega)]
    simp [unitVec, hlt]

theorem finSumAuxNat_unit {g : Nat} (m : Nat) (hm : m < g) :
    ∀ (k : Nat) (hk : k ≤ g), m < k →
      finSumAuxNat (fun j : Fin g => if unitVec g m j ≠ 0 then 1 else 0) k hk = 1
  | 0, _, hmk => by omega
  | k + 1, hk, hmk => by
    by_cases heq : k = m
    · subst heq
      rw [finSumAuxNat, finSumAuxNat_unit_zero k k (Nat.le_of_succ_le hk) (Nat.le_refl k)]
      simp [unitVec]
    · have hlt : m < k := by omega
      rw [finSumAuxNat, finSumAuxNat_unit m hm k (Nat.le_of_succ_le hk) hlt]
      simp [unitVec, heq]

theorem supportSize_unitVec {g : Nat} (m : Nat) (hm : m < g) :
    supportSize (unitVec g m) = 1 :=
  finSumAuxNat_unit m hm g (Nat.le_refl g) hm

theorem supportSize_lincomb_le {g : Nat} (c1 c2 : Int) (u v : Fin g → Int) :
    supportSize (fun j => c1 * u j + c2 * v j) ≤ supportSize u + supportSize v := by
  unfold supportSize
  rw [← finSumNat_add]
  apply finSumNat_le
  intro j
  by_cases hu : u j = 0 <;> by_cases hv : v j = 0
  · simp [hu, hv]
  · simp only [hu, hv, Int.mul_zero, Int.zero_add, ne_eq, not_true_eq_false, ↓reduceIte,
      not_false_eq_true, Nat.zero_add]
    split <;> omega
  · simp only [hu, hv, Int.mul_zero, Int.add_zero, ne_eq, not_false_eq_true, ↓reduceIte,
      not_true_eq_false, Nat.add_zero]
    split <;> omega
  · by_cases hsum : c1 * u j + c2 * v j = 0 <;> simp [hu, hv, hsum]

theorem supportSize_of_full {g : Nat} {w : Fin g → Int} (hw : isFullSupport w) :
    supportSize w = g := by
  unfold supportSize
  have h1 : finSumNat (fun j : Fin g => if w j ≠ 0 then 1 else 0) =
      finSumNat (fun _ : Fin g => 1) := by
    apply finSumNat_congr
    intro j
    simp [hw j]
  rw [h1, finSumNat_const, Nat.mul_one]

/-! ## `ceilLog2` Exact Characterization -/

theorem ceilLog2Aux_le_of_pow : ∀ (fuel n d : Nat),
    n ≤ fuel → 1 ≤ n → n ≤ 2 ^ d → ceilLog2Aux fuel n ≤ d
  | 0, n, _, hnf, hn1, _ => by omega
  | fuel + 1, n, d, hnf, hn1, hpow => by
    unfold ceilLog2Aux
    split
    · exact Nat.zero_le d
    · rename_i hgt
      have hn2 : 2 ≤ n := by omega
      cases d with
      | zero =>
        simp only [Nat.pow_zero] at hpow
        omega
      | succ d' =>
        have hpow' : (n + 1) / 2 ≤ 2 ^ d' := by
          have : 2 ^ (d' + 1) = 2 * 2 ^ d' := by rw [Nat.pow_succ]; omega
          omega
        have hle := ceilLog2Aux_le_of_pow fuel ((n + 1) / 2) d' (by omega) (by omega) hpow'
        omega

theorem le_pow_ceilLog2Aux : ∀ (fuel n : Nat),
    n ≤ fuel → 1 ≤ n → n ≤ 2 ^ ceilLog2Aux fuel n
  | 0, n, hnf, hn1 => by omega
  | fuel + 1, n, hnf, hn1 => by
    unfold ceilLog2Aux
    split
    · omega
    · rename_i hgt
      have ih := le_pow_ceilLog2Aux fuel ((n + 1) / 2) (by omega) (by omega)
      rw [Nat.pow_add, Nat.pow_one]
      omega

theorem le_pow_ceilLog2 {n : Nat} (hn : 1 ≤ n) : n ≤ 2 ^ ceilLog2 n :=
  le_pow_ceilLog2Aux n n (Nat.le_refl n) hn

theorem ceilLog2_le_of_le_pow {n d : Nat} (hn : 1 ≤ n) (hpow : n ≤ 2 ^ d) :
    ceilLog2 n ≤ d :=
  ceilLog2Aux_le_of_pow n n d (Nat.le_refl n) hn hpow

theorem ceilLog2_values :
    ceilLog2 2 = 1 ∧ ceilLog2 3 = 2 ∧ ceilLog2 4 = 2 ∧ ceilLog2 5 = 3 := by
  decide

/-! ## Finite Pigeonhole Principle -/

theorem fin_pigeonhole_zero : ∀ {B A : Nat} (f : Fin A → Nat),
    (∀ a1 a2, f a1 = f a2 → a1 = a2) →
    (∀ a, f a < B) →
    A ≤ B
  | 0, A, f, _, hlt => by
    cases A with
    | zero => exact Nat.le_refl 0
    | succ A' =>
      have := hlt ⟨0, Nat.zero_lt_succ A'⟩
      omega
  | B + 1, A, f, hinj, hlt => by
    by_cases hex : ∃ a : Fin A, f a = B
    · rcases hex with ⟨a0, ha0⟩
      cases A with
      | zero => exact Fin.elim0 a0
      | succ A' =>
        let skip : Fin A' → Fin (A' + 1) := fun i =>
          if h : i.val < a0.val then ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
          else ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        have hskip_inj : ∀ i1 i2, skip i1 = skip i2 → i1 = i2 := by
          intro i1 i2 heq
          apply Fin.ext
          dsimp [skip] at heq
          split at heq <;> split at heq
          · exact Fin.mk.inj heq
          · have hval := Fin.mk.inj heq; omega
          · have hval := Fin.mk.inj heq; omega
          · have hval := Fin.mk.inj heq; omega
        have hskip_ne : ∀ i, skip i ≠ a0 := by
          intro i heq
          dsimp [skip] at heq
          split at heq
          · have hval := Fin.mk.inj heq; omega
          · have hval := Fin.mk.inj heq; omega
        have hlt' : ∀ i : Fin A', f (skip i) < B := by
          intro i
          have h1 := hlt (skip i)
          have h2 : f (skip i) ≠ B := by
            intro heq
            have : skip i = a0 := hinj (skip i) a0 (heq.trans ha0.symm)
            exact hskip_ne i this
          omega
        have hinj' : ∀ i1 i2, f (skip i1) = f (skip i2) → i1 = i2 := by
          intro i1 i2 heq
          exact hskip_inj i1 i2 (hinj (skip i1) (skip i2) heq)
        have hle := fin_pigeonhole_zero (B := B) (fun i => f (skip i)) hinj' hlt'
        omega
    · have hlt' : ∀ a : Fin A, f a < B := by
        intro a
        have h1 := hlt a
        have h2 : f a ≠ B := fun heq => hex ⟨a, heq⟩
        omega
      have hle := fin_pigeonhole_zero (B := B) f hinj hlt'
      omega

theorem fin_pigeonhole_interval {A lo hi : Nat} (f : Fin A → Nat)
    (hinj : ∀ a1 a2, f a1 = f a2 → a1 = a2)
    (hbound : ∀ a, lo ≤ f a ∧ f a < hi) :
    A ≤ hi - lo := by
  apply fin_pigeonhole_zero (B := hi - lo) (fun a => f a - lo)
  · intro a1 a2 heq
    have h1 := (hbound a1).1
    have h2 := (hbound a2).1
    apply hinj a1 a2
    omega
  · intro a
    have h := hbound a
    omega

end BitSerialLutDag
