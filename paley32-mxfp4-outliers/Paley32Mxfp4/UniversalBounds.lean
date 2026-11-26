/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Paley32Mxfp4.Defs

/-!
# Universal Bounds: Orthogonal `k`-Sparse PAPR Lower Bound & OCP MXFP4 Bulk-Crush Threshold

Pure Lean 4 `Init` (zero Mathlib, zero `native_decide`) proofs of:
- Theorem 1 (`universal_orthogonal_k_sparse_papr_lower_bound`)
- Theorem 6 (`mxfp4_e8m0_bulk_crush_threshold_exact`)
-/

namespace Paley32Mxfp4

/-! ### 1. Elementary `Rat` Order and Finite-Sum Helpers -/

theorem rat_sub_nonneg {a b : Rat} (h : b ≤ a) : (0 : Rat) ≤ a - b := by
  have := Rat.add_le_add_right (c := -b) |>.mpr h
  grind

theorem rat_le_of_sub_nonneg {a b : Rat} (h : (0 : Rat) ≤ a - b) : b ≤ a := by
  have := Rat.add_le_add_right (c := b) |>.mpr h
  grind

theorem rat_sub_pos {a b : Rat} (h : b < a) : (0 : Rat) < a - b := by
  have h1 : (0 : Rat) ≤ a - b := rat_sub_nonneg (Rat.le_of_lt h)
  have hne : a - b ≠ 0 := by
    intro h0
    have heq : a = b := by grind
    exact Rat.ne_of_gt h heq
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_lt_of_sub_pos {a b : Rat} (h : (0 : Rat) < a - b) : b < a := by
  have h1 : b ≤ a := rat_le_of_sub_nonneg (Rat.le_of_lt h)
  have hne : b ≠ a := by
    intro h0
    have : a - b = 0 := by grind
    exact Rat.ne_of_gt h this
  exact Rat.lt_of_le_of_ne h1 hne

theorem rat_mul_pos {a b : Rat} (ha : (0 : Rat) < a) (hb : (0 : Rat) < b) :
    (0 : Rat) < a * b := by
  have h1 : (0 : Rat) ≤ a * b := Rat.mul_nonneg (Rat.le_of_lt ha) (Rat.le_of_lt hb)
  have hne : a * b ≠ 0 := by
    intro h0
    cases Rat.mul_eq_zero.mp h0 with
    | inl h => exact Rat.ne_of_gt ha h
    | inr h => exact Rat.ne_of_gt hb h
  exact Rat.lt_of_le_of_ne h1 (Ne.symm hne)

theorem rat_mul_le_mul_of_nonneg_left {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    c * a ≤ c * b := by
  apply rat_le_of_sub_nonneg
  have h1 : (0 : Rat) ≤ b - a := rat_sub_nonneg h
  have h2 : (0 : Rat) ≤ c * (b - a) := Rat.mul_nonneg hc h1
  have eq : c * b - c * a = c * (b - a) := by grind
  rw [eq]
  exact h2

theorem rat_mul_le_mul_of_nonneg_right {a b c : Rat} (h : a ≤ b) (hc : (0 : Rat) ≤ c) :
    a * c ≤ b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact rat_mul_le_mul_of_nonneg_left h hc

theorem rat_mul_lt_mul_of_pos_left {a b c : Rat} (h : a < b) (hc : (0 : Rat) < c) :
    c * a < c * b := by
  apply rat_lt_of_sub_pos
  have h1 : (0 : Rat) < b - a := rat_sub_pos h
  have h2 : (0 : Rat) < c * (b - a) := rat_mul_pos hc h1
  have eq : c * b - c * a = c * (b - a) := by grind
  rw [eq]
  exact h2

theorem rat_add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  have h3 : a + c ≤ b + c := (Rat.add_le_add_right (c := c)).mpr h1
  have h4 : b + c ≤ b + d := by
    rw [Rat.add_comm b c, Rat.add_comm b d]
    exact (Rat.add_le_add_right (c := b)).mpr h2
  exact Rat.le_trans h3 h4

theorem rat_add_lt_add_of_lt_of_le {a b c d : Rat} (h1 : a < b) (h2 : c ≤ d) :
    a + c < b + d := by
  have hle : a + c ≤ b + d := rat_add_le_add (Rat.le_of_lt h1) h2
  have hne : a + c ≠ b + d := by
    intro heq
    have hba : (0 : Rat) < b - a := rat_sub_pos h1
    have hdc : (0 : Rat) ≤ d - c := rat_sub_nonneg h2
    have hsum : (b - a) + (d - c) = 0 := by grind
    have hle0 : b - a ≤ 0 := by
      have : b - a = -(d - c) := by grind
      rw [this]
      have := Rat.add_le_add_right (c := -(d - c)) |>.mpr hdc
      grind
    exact Rat.not_le.mpr hba hle0
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have hle : a ≤ c := Rat.le_trans (Rat.le_of_lt h1) h2
  have hne : a ≠ c := by
    intro heq
    subst heq
    exact Rat.not_le.mpr h1 h2
  exact Rat.lt_of_le_of_ne hle hne

theorem rat_natCast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have h1 : (0 : Rat) ≤ 1 := by decide
    have h2 : (0 : Rat) + 0 ≤ (k : Rat) + 1 := rat_add_le_add ih h1
    have h0 : (0 : Rat) + 0 = 0 := by grind
    rw [h0] at h2
    have hcast : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
    rw [hcast]
    exact h2

theorem rat_natCast_pos {n : Nat} (hn : 0 < n) : (0 : Rat) < (n : Rat) := by
  match n, hn with
  | k + 1, _ =>
    have h1 : (0 : Rat) < 1 := by decide
    have hk : (0 : Rat) ≤ (k : Rat) := rat_natCast_nonneg k
    have h2 : (0 : Rat) + 0 < 1 + (k : Rat) := rat_add_lt_add_of_lt_of_le h1 hk
    have hcast : ((k + 1 : Nat) : Rat) = 1 + (k : Rat) := by grind
    have h0 : (0 : Rat) + 0 = 0 := by grind
    rw [h0] at h2
    rw [hcast]
    exact h2

theorem rat_natCast_le_natCast {a b : Nat} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := by
  have hd : b = a + (b - a) := (Nat.add_sub_of_le h).symm
  have hdiff : (0 : Rat) ≤ ((b - a : Nat) : Rat) := rat_natCast_nonneg (b - a)
  have hadd : (a : Rat) + 0 ≤ (a : Rat) + ((b - a : Nat) : Rat) :=
    rat_add_le_add Rat.le_refl hdiff
  have heq : (a : Rat) + ((b - a : Nat) : Rat) = (b : Rat) := by
    have : ((a + (b - a) : Nat) : Rat) = (a : Rat) + ((b - a : Nat) : Rat) := by grind
    rw [← this, ← hd]
  have ha0 : (a : Rat) + 0 = (a : Rat) := by grind
  rw [ha0, heq] at hadd
  exact hadd

theorem sumFinRat_congr {n : Nat} (f g : Fin n → Rat) (h : ∀ i, f i = g i) :
    sumFinRat n f = sumFinRat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFinRat]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc) (fun i => h i.castSucc), h (Fin.last k)]

theorem sumFinRat_const (n : Nat) (c : Rat) :
    sumFinRat n (fun _ => c) = (n : Rat) * c := by
  induction n with
  | zero =>
    simp only [sumFinRat]
    grind
  | succ k ih =>
    simp only [sumFinRat]
    rw [ih]
    grind

theorem sumFinRat_add {n : Nat} (f g : Fin n → Rat) :
    sumFinRat n (fun i => f i + g i) = sumFinRat n f + sumFinRat n g := by
  induction n with
  | zero => simp only [sumFinRat]; grind
  | succ k ih =>
    simp only [sumFinRat]
    rw [ih]
    grind

theorem sumFinRat_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    sumFinRat n (fun i => c * f i) = c * sumFinRat n f := by
  induction n with
  | zero => simp [sumFinRat]
  | succ k ih =>
    simp only [sumFinRat]
    rw [ih]
    grind

theorem sumFinRat_le {n : Nat} (f g : Fin n → Rat) (h : ∀ i, f i ≤ g i) :
    sumFinRat n f ≤ sumFinRat n g := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    simp only [sumFinRat]
    exact rat_add_le_add (ih _ _ (fun i => h i.castSucc)) (h (Fin.last k))

theorem sumFinRat_swap {m n : Nat} (f : Fin m → Fin n → Rat) :
    sumFinRat m (fun i => sumFinRat n (fun j => f i j)) =
    sumFinRat n (fun j => sumFinRat m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumFinRat]
    have h0 := sumFinRat_const n 0
    have : (n : Rat) * 0 = 0 := by grind
    rw [this] at h0
    exact h0.symm
  | succ k ih =>
    simp only [sumFinRat]
    rw [ih (fun i j => f i.castSucc j)]
    rw [← sumFinRat_add]

/-- Splitting a `Fin n` sum at an arbitrary index `i0`. -/
theorem sumFinRat_eq_single_add {n : Nat} (f : Fin n → Rat) (i0 : Fin n) :
    sumFinRat n f = f i0 + sumFinRat n (fun i => if i = i0 then 0 else f i) := by
  induction n with
  | zero => exact Fin.elim0 i0
  | succ k ih =>
    simp only [sumFinRat]
    by_cases hlast : i0 = Fin.last k
    · subst hlast
      have h1 : sumFinRat k (fun i : Fin k => if i.castSucc = Fin.last k then (0 : Rat) else f i.castSucc) =
                sumFinRat k (fun i : Fin k => f i.castSucc) := by
        apply sumFinRat_congr
        intro i
        have hne : i.castSucc ≠ Fin.last k := by
          intro heq
          have : i.val = k := congrArg Fin.val heq
          omega
        simp [hne]
      rw [h1]
      simp only [↓reduceIte]
      grind
    · have hlt : i0.val < k := by
        have := i0.isLt
        have hne : i0.val ≠ k := fun hv => hlast (Fin.ext hv)
        omega
      let i0' : Fin k := ⟨i0.val, hlt⟩
      have hi0 : i0 = i0'.castSucc := Fin.ext rfl
      have hih := ih (fun i => f i.castSucc) i0'
      have hcongr : sumFinRat k (fun i : Fin k => if i.castSucc = i0 then (0 : Rat) else f i.castSucc) =
                    sumFinRat k (fun i : Fin k => if i = i0' then (0 : Rat) else f i.castSucc) := by
        apply sumFinRat_congr
        intro i
        have heq : (i.castSucc = i0) ↔ (i = i0') := by
          rw [hi0]
          constructor
          · intro h
            have hv : i.castSucc.val = i0'.castSucc.val := congrArg Fin.val h
            exact Fin.ext hv
          · intro h; rw [h]
        by_cases h : i = i0'
        · subst h
          simp only [hi0, ↓reduceIte]
        · have h' : i.castSucc ≠ i0 := mt heq.mp h
          simp only [h', h, ↓reduceIte]
      have hne_last : Fin.last k ≠ i0 := Ne.symm hlast
      simp only [hne_last, ↓reduceIte]
      rw [hcongr, hih]
      have hval : f i0'.castSucc = f i0 := by rw [← hi0]
      rw [hval]
      grind

/-- If every term is `≤ c` and the sum equals `n * c`, then every term equals `c`. -/
theorem sumFinRat_eq_of_le_of_sum_eq {n : Nat} (f : Fin n → Rat) (c : Rat)
    (hle : ∀ i, f i ≤ c) (hsum : sumFinRat n f = (n : Rat) * c) :
    ∀ i, f i = c := by
  intro i0
  apply Classical.byContradiction
  intro hne
  have hlt : f i0 < c := Rat.lt_of_le_of_ne (hle i0) hne
  have hrest : sumFinRat n (fun i => if i = i0 then 0 else f i) ≤
               sumFinRat n (fun i => if i = i0 then 0 else c) := by
    apply sumFinRat_le
    intro i
    by_cases h : i = i0
    · simp [h]
    · simp [h]; exact hle i
  have h1 := sumFinRat_eq_single_add f i0
  have h2 := sumFinRat_eq_single_add (fun _ : Fin n => c) i0
  rw [sumFinRat_const] at h2
  have hlt_sum : sumFinRat n f < (n : Rat) * c := by
    rw [h1, h2]
    exact rat_add_lt_add_of_lt_of_le hlt hrest
  rw [hsum] at hlt_sum
  exact Rat.lt_irrefl hlt_sum

/-- Pigeonhole for `sumFinRat`: if `n > 0` and `n * c ≤ sumFinRat n f`, then `∃ i, c ≤ f i`. -/
theorem sumFinRat_exists_ge {n : Nat} (hn : 0 < n) (f : Fin n → Rat) (c : Rat)
    (hsum : (n : Rat) * c ≤ sumFinRat n f) :
    ∃ i : Fin n, c ≤ f i := by
  apply Classical.byContradiction
  intro hall
  have hlt : ∀ i : Fin n, f i < c := by
    intro i
    apply Classical.byContradiction
    intro hge
    exact hall ⟨i, Rat.not_lt.mp hge⟩
  have i0 : Fin n := ⟨0, hn⟩
  have hrest : sumFinRat n (fun i => if i = i0 then 0 else f i) ≤
               sumFinRat n (fun i => if i = i0 then 0 else c) := by
    apply sumFinRat_le
    intro i
    by_cases h : i = i0
    · simp [h]
    · simp [h]; exact Rat.le_of_lt (hlt i)
  have h1 := sumFinRat_eq_single_add f i0
  have h2 := sumFinRat_eq_single_add (fun _ : Fin n => c) i0
  rw [sumFinRat_const] at h2
  have hlt_sum : sumFinRat n f < (n : Rat) * c := by
    rw [h1, h2]
    exact rat_add_lt_add_of_lt_of_le (hlt i0) hrest
  exact Rat.not_lt.mpr hsum hlt_sum

/-! ### 2. Bijection & Cyclic-Shift Invariance of `sumFinRat` -/

/-- Swap two indices in `Fin n`. -/
def swapFin {n : Nat} (a b : Fin n) (x : Fin n) : Fin n :=
  if x = a then b else if x = b then a else x

theorem swapFin_involutive {n : Nat} (a b x : Fin n) :
    swapFin a b (swapFin a b x) = x := by
  unfold swapFin
  by_cases hxa : x = a
  · subst hxa
    by_cases hab : x = b
    · subst hab; simp
    · have hba : b ≠ x := Ne.symm hab
      simp [hba]
  · by_cases hxb : x = b
    · subst hxb; simp [hxa]
    · simp [hxa, hxb]

theorem swapFin_injective {n : Nat} (a b : Fin n) : isInjective (swapFin a b) := by
  intro x y h
  have := congrArg (swapFin a b) h
  rw [swapFin_involutive, swapFin_involutive] at this
  exact this

theorem sumFinRat_swapFin {n : Nat} (a b : Fin n) (f : Fin n → Rat) :
    sumFinRat n (fun x => f (swapFin a b x)) = sumFinRat n f := by
  by_cases hab : a = b
  · subst hab
    apply sumFinRat_congr
    intro x
    unfold swapFin
    by_cases h : x = a <;> simp [h]
  · have h1 := sumFinRat_eq_single_add (fun x => f (swapFin a b x)) a
    have h2 := sumFinRat_eq_single_add (fun x => if x = a then 0 else f (swapFin a b x)) b
    have h3 := sumFinRat_eq_single_add f a
    have h4 := sumFinRat_eq_single_add (fun x => if x = a then 0 else f x) b
    have hba : b ≠ a := Ne.symm hab
    have ha_val : swapFin a b a = b := by simp [swapFin]
    have hb_val : swapFin a b b = a := by simp [swapFin, hba]
    have hrem : sumFinRat n (fun x => if x = b then 0 else if x = a then 0 else f (swapFin a b x)) =
                sumFinRat n (fun x => if x = b then 0 else if x = a then 0 else f x) := by
      apply sumFinRat_congr
      intro x
      by_cases hxb : x = b
      · simp [hxb]
      · by_cases hxa : x = a
        · simp [hxa]
        · simp [hxb, hxa, swapFin]
    rw [h1, h2, h3, h4, ha_val, hb_val]
    simp only [hba, ↓reduceIte]
    rw [hrem]
    grind

/-- Cyclic shift by `1` on `Fin n`. -/
def shiftOne {n : Nat} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

theorem sumFinRat_tele_shift {r : Nat} (u : Fin (r + 1) → Rat) :
    sumFinRat r (fun i : Fin r => u ⟨i.val + 1, by omega⟩) + u ⟨0, by omega⟩ =
    sumFinRat (r + 1) u := by
  induction r with
  | zero =>
    simp only [sumFinRat]
    have h0 : (⟨0, by omega⟩ : Fin 1) = Fin.last 0 := Fin.ext rfl
    rw [h0]
  | succ t iht =>
    have hsub := iht (fun i : Fin (t + 1) => u i.castSucc)
    change sumFinRat (t + 1) (fun i : Fin (t + 1) => u ⟨i.val + 1, by omega⟩) + u ⟨0, by omega⟩ =
           sumFinRat (t + 1) (fun i : Fin (t + 1) => u i.castSucc) + u (Fin.last (t + 1))
    rw [← hsub]
    simp only [sumFinRat]
    have h1 : sumFinRat t (fun i : Fin t => u ⟨i.castSucc.val + 1, by omega⟩) =
              sumFinRat t (fun i : Fin t => u (⟨i.val + 1, by omega⟩ : Fin (t + 1)).castSucc) := by
      apply sumFinRat_congr; intro i; rfl
    have h2 : (⟨(Fin.last t).val + 1, by omega⟩ : Fin (t + 2)) = Fin.last (t + 1) := by
      apply Fin.ext; simp [Fin.last]
    have h3 : (⟨0, by omega⟩ : Fin (t + 1)).castSucc = (⟨0, by omega⟩ : Fin (t + 2)) := rfl
    rw [h1, h2, h3]
    grind

theorem sumFinRat_shiftOne {n : Nat} (hn : 0 < n) (f : Fin n → Rat) :
    sumFinRat n (fun i => f (shiftOne hn i)) = sumFinRat n f := by
  match n, hn with
  | k + 1, _ =>
    change sumFinRat k (fun i : Fin k => f ⟨(i.castSucc.val + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩) +
           f ⟨((Fin.last k).val + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩ =
           sumFinRat (k + 1) f
    have hlast_val : (⟨((Fin.last k).val + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
                     ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [Fin.last]
    have hlhs : sumFinRat k (fun i : Fin k => f ⟨(i.castSucc.val + 1) % (k + 1), Nat.mod_lt _ (by omega)⟩) =
                sumFinRat k (fun i : Fin k => f ⟨i.val + 1, by omega⟩) := by
      apply sumFinRat_congr
      intro i
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hlhs, hlast_val]
    exact sumFinRat_tele_shift f

/-- Cyclic shift by `d` on `Fin n`. -/
def shiftBy {n : Nat} (hn : 0 < n) (d : Nat) (i : Fin n) : Fin n :=
  ⟨(i.val + d) % n, Nat.mod_lt _ hn⟩

theorem sumFinRat_shiftBy {n : Nat} (hn : 0 < n) (d : Nat) (f : Fin n → Rat) :
    sumFinRat n (fun i => f (shiftBy hn d i)) = sumFinRat n f := by
  induction d with
  | zero =>
    apply sumFinRat_congr
    intro i
    congr 1
    apply Fin.ext
    simp [shiftBy, Nat.mod_eq_of_lt i.isLt]
  | succ d ih =>
    have hcomp : ∀ i : Fin n, shiftBy hn (d + 1) i = shiftBy hn d (shiftOne hn i) := by
      intro i
      apply Fin.ext
      simp only [shiftBy, shiftOne]
      rw [Nat.mod_add_mod]
      congr 1
      omega
    have h1 : sumFinRat n (fun i => f (shiftBy hn (d + 1) i)) =
              sumFinRat n (fun i => f (shiftBy hn d (shiftOne hn i))) :=
      sumFinRat_congr _ _ (fun i => by rw [hcomp i])
    rw [h1, sumFinRat_shiftOne hn (fun i => f (shiftBy hn d i)), ih]

/-- Cyclic `k`-support starting at `r : Fin n`. -/
def cycSupport {n k : Nat} (hn : 0 < n) (r : Fin n) (t : Fin k) : Fin n :=
  ⟨(r.val + t.val) % n, Nat.mod_lt _ hn⟩

theorem cycSupport_injective {n k : Nat} (hn : 0 < n) (hkn : k ≤ n) (r : Fin n) :
    isInjective (cycSupport (k := k) hn r) := by
  intro a b hab
  have hv : (r.val + a.val) % n = (r.val + b.val) % n := congrArg Fin.val hab
  have ha := a.isLt
  have hb := b.isLt
  have hr := r.isLt
  apply Fin.ext
  by_cases h1 : r.val + a.val < n
  · rw [Nat.mod_eq_of_lt h1] at hv
    by_cases h2 : r.val + b.val < n
    · rw [Nat.mod_eq_of_lt h2] at hv; omega
    · have hlt2 : r.val + b.val - n < n := by omega
      have hmod2 : (r.val + b.val) % n = r.val + b.val - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
      rw [hmod2] at hv; omega
  · have hlt1 : r.val + a.val - n < n := by omega
    have hmod1 : (r.val + a.val) % n = r.val + a.val - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt1]
    rw [hmod1] at hv
    by_cases h2 : r.val + b.val < n
    · rw [Nat.mod_eq_of_lt h2] at hv; omega
    · have hlt2 : r.val + b.val - n < n := by omega
      have hmod2 : (r.val + b.val) % n = r.val + b.val - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
      rw [hmod2] at hv; omega

/-- Cyclic-shift double counting: summing `∑_{t < k} f((r + t) % n)` over `r < n` equals `k * ∑_j f j`. -/
theorem sumFinRat_cycSupport_double_count {n k : Nat} (hn : 0 < n) (f : Fin n → Rat) :
    sumFinRat n (fun r => sumFinRat k (fun t => f (cycSupport hn r t))) =
    (k : Rat) * sumFinRat n f := by
  rw [sumFinRat_swap]
  have hinner : ∀ t : Fin k,
      sumFinRat n (fun r => f (cycSupport hn r t)) = sumFinRat n f := by
    intro t
    exact sumFinRat_shiftBy hn t.val f
  rw [sumFinRat_congr _ (fun _ => sumFinRat n f) hinner, sumFinRat_const]

/-! ### 3. Indicator-Support Sum Extraction for `Fin n` -/

def inRangeDec {k n : Nat} (S : Fin k → Fin n) (j : Fin n) : Bool :=
  let rec go (t : Nat) : Bool :=
    if ht : t < k then
      if S ⟨t, ht⟩ = j then true else go (t + 1)
    else false
  go 0

theorem inRangeDec_go_eq_true {k n : Nat} (S : Fin k → Fin n) (j : Fin n) (start : Nat) :
    inRangeDec.go S j start = true ↔ ∃ t : Fin k, start ≤ t.val ∧ S t = j := by
  induction hk : k - start generalizing start with
  | zero =>
    have hge : ¬ start < k := by omega
    unfold inRangeDec.go
    simp only [hge, ↓reduceDIte, Bool.false_eq_true, false_iff]
    rintro ⟨t, ht1, _⟩
    have := t.isLt
    omega
  | succ d ih =>
    have hlt : start < k := by omega
    unfold inRangeDec.go
    simp only [hlt, ↓reduceDIte]
    by_cases heq : S ⟨start, hlt⟩ = j
    · simp only [heq, ↓reduceIte, true_iff]
      exact ⟨⟨start, hlt⟩, Nat.le_refl _, heq⟩
    · simp only [heq, ↓reduceIte]
      rw [ih (start + 1) (by omega)]
      constructor
      · rintro ⟨t, ht1, ht2⟩
        exact ⟨t, by omega, ht2⟩
      · rintro ⟨t, ht1, ht2⟩
        have hne : t.val ≠ start := by
          intro h
          have : t = ⟨start, hlt⟩ := Fin.ext h
          rw [this] at ht2
          exact heq ht2
        exact ⟨t, by omega, ht2⟩

theorem inRangeDec_eq_true {k n : Nat} (S : Fin k → Fin n) (j : Fin n) :
    inRangeDec S j = true ↔ ∃ t : Fin k, S t = j := by
  unfold inRangeDec
  rw [inRangeDec_go_eq_true]
  constructor
  · rintro ⟨t, _, ht⟩; exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩; exact ⟨t, Nat.zero_le _, ht⟩

/-- Summing a function supported on an injective image `S : Fin k → Fin n` equals summing over `Fin k`. -/
theorem sumFinRat_supported_on_inj {k n : Nat} (S : Fin k → Fin n) (hS : isInjective S)
    (g : Fin n → Rat) :
    sumFinRat n (fun j => if inRangeDec S j then g j else 0) =
    sumFinRat k (fun t => g (S t)) := by
  induction k with
  | zero =>
    simp only [sumFinRat]
    have hzero : ∀ j : Fin n, (if inRangeDec S j then g j else 0) = 0 := by
      intro j
      have hf : inRangeDec S j = false := by
        cases h : inRangeDec S j with
        | false => rfl
        | true =>
          rcases (inRangeDec_eq_true S j).mp h with ⟨t, _⟩
          exact Fin.elim0 t
      simp [hf]
    rw [sumFinRat_congr _ (fun _ => (0 : Rat)) hzero, sumFinRat_const]
    grind
  | succ m ih =>
    let S' : Fin m → Fin n := fun t => S t.castSucc
    have hS' : isInjective S' := by
      intro a b hab
      have h1 := hS a.castSucc b.castSucc hab
      have hv : a.castSucc.val = b.castSucc.val := congrArg Fin.val h1
      exact Fin.ext hv
    let jlast : Fin n := S (Fin.last m)
    have hnot_in : ∀ t : Fin m, S' t ≠ jlast := by
      intro t heq
      have := hS t.castSucc (Fin.last m) heq
      have : t.val = m := congrArg Fin.val this
      omega
    have hsplit := sumFinRat_eq_single_add (fun j => if inRangeDec S j then g j else 0) jlast
    have hjlast_in : inRangeDec S jlast = true :=
      (inRangeDec_eq_true S jlast).mpr ⟨Fin.last m, rfl⟩
    have hrest : ∀ j : Fin n,
        (if j = jlast then (0 : Rat) else if inRangeDec S j then g j else 0) =
        (if inRangeDec S' j then g j else 0) := by
      intro j
      by_cases hjj : j = jlast
      · subst hjj
        have hf : inRangeDec S' jlast = false := by
          cases h : inRangeDec S' jlast with
          | false => rfl
          | true =>
            rcases (inRangeDec_eq_true S' jlast).mp h with ⟨t, ht⟩
            exact absurd ht (hnot_in t)
        simp [hf]
      · simp only [hjj, ↓reduceIte]
        have hiff : inRangeDec S j = inRangeDec S' j := by
          cases h1 : inRangeDec S j with
          | true =>
            rcases (inRangeDec_eq_true S j).mp h1 with ⟨t, ht⟩
            have hlt : t.val < m := by
              have hne : t ≠ Fin.last m := by
                intro heq; subst heq; exact hjj ht.symm
              have hne_v : t.val ≠ m := fun hv => hne (Fin.ext hv)
              have := t.isLt
              omega
            have h2 : inRangeDec S' j = true :=
              (inRangeDec_eq_true S' j).mpr ⟨⟨t.val, hlt⟩, ht⟩
            exact h2.symm
          | false =>
            cases h2 : inRangeDec S' j with
            | false => rfl
            | true =>
              rcases (inRangeDec_eq_true S' j).mp h2 with ⟨t, ht⟩
              have h1' : inRangeDec S j = true :=
                (inRangeDec_eq_true S j).mpr ⟨t.castSucc, ht⟩
              rw [h1] at h1'
              exact absurd h1' (by decide)
        rw [hiff]
    rw [hsplit, hjlast_in]
    simp only [↓reduceIte]
    rw [sumFinRat_congr _ _ hrest, ih S' hS']
    simp only [sumFinRat]
    grind

/-! ### 4. Proof of Theorem 1: Universal Orthogonal `k`-Sparse PAPR Lower Bound -/

theorem universal_orthogonal_k_sparse_papr_lower_bound
    (n k : Nat) (hk1 : 1 ≤ k) (hkn : k ≤ n) (U : RatMat n n)
    (hUtU : isOrthogonalRat U (n : Rat))
    (hUUt : isOrthogonalRat (transposeRat U) (n : Rat)) :
    (∃ (i : Fin n) (S : Fin k → Fin n),
      isInjective S ∧
      (k : Rat) ≤ sumFinRat k (fun t => U i (S t) * U i (S t)) ∧
      ∃ x : Fin n → Rat,
        (∀ j : Fin n, (∀ t : Fin k, S t ≠ j) → x j = 0) ∧
        (0 : Rat) < sumSqRat x ∧
        (k : Rat) * sumSqRat x ≤ matVecRat U x i * matVecRat U x i) ∧
    (k < n →
      ((∀ (i : Fin n) (S : Fin k → Fin n), isInjective S →
          sumFinRat k (fun t => U i (S t) * U i (S t)) ≤ (k : Rat)) ↔
       (∀ i j : Fin n, U i j * U i j = 1))) := by
  have hn : 0 < n := by omega
  let _ := hUtU
  -- Row squared-norm identity from `U U^T = n I`: `∀ i, ∑_j U i j^2 = n`
  have hrow_norm : ∀ i : Fin n, sumFinRat n (fun j => U i j * U i j) = (n : Rat) := by
    intro i
    have hdiag := congrFun (congrFun hUUt i) i
    simp only [matMulRat, transposeRat, scaleMatRat, idMatRat, ↓reduceIte] at hdiag
    have : (n : Rat) * 1 = (n : Rat) := by grind
    rw [this] at hdiag
    exact hdiag
  constructor
  · -- Part (a): Existence of `(i, S)` and `k`-sparse vector `x` with `(U x)_i^2 ≥ k * ‖x‖_2^2`
    let i0 : Fin n := ⟨0, hn⟩
    have hdc := sumFinRat_cycSupport_double_count (k := k) hn (fun j => U i0 j * U i0 j)
    rw [hrow_norm i0] at hdc
    have hsum_ge : (n : Rat) * (k : Rat) ≤
        sumFinRat n (fun r => sumFinRat k (fun t => U i0 (cycSupport hn r t) * U i0 (cycSupport hn r t))) := by
      rw [hdc]
      have : (n : Rat) * (k : Rat) = (k : Rat) * (n : Rat) := by grind
      rw [this]
      exact Rat.le_refl
    rcases sumFinRat_exists_ge hn _ (k : Rat) hsum_ge with ⟨r0, hr0⟩
    let S : Fin k → Fin n := cycSupport hn r0
    have hS_inj : isInjective S := cycSupport_injective hn hkn r0
    refine ⟨i0, S, hS_inj, hr0, ?_⟩
    let x : Fin n → Rat := fun j => if inRangeDec S j then U i0 j else 0
    refine ⟨x, ?_, ?_, ?_⟩
    · intro j hj
      have hf : inRangeDec S j = false := by
        cases h : inRangeDec S j with
        | false => rfl
        | true =>
          rcases (inRangeDec_eq_true S j).mp h with ⟨t, ht⟩
          exact absurd ht (hj t)
      simp [x, hf]
    · have hxsq : sumSqRat x = sumFinRat k (fun t => U i0 (S t) * U i0 (S t)) := by
        unfold sumSqRat
        have hcongr : ∀ j : Fin n, x j * x j = if inRangeDec S j then U i0 j * U i0 j else 0 := by
          intro j
          by_cases h : inRangeDec S j = true
          · simp [x, h]
          · have hf : inRangeDec S j = false := by cases h' : inRangeDec S j <;> simp_all
            simp [x, hf]
        rw [sumFinRat_congr _ _ hcongr]
        exact sumFinRat_supported_on_inj S hS_inj (fun j => U i0 j * U i0 j)
      rw [hxsq]
      exact rat_lt_of_lt_of_le (rat_natCast_pos (by omega)) hr0
    · have hxsq : sumSqRat x = sumFinRat k (fun t => U i0 (S t) * U i0 (S t)) := by
        unfold sumSqRat
        have hcongr : ∀ j : Fin n, x j * x j = if inRangeDec S j then U i0 j * U i0 j else 0 := by
          intro j
          by_cases h : inRangeDec S j = true
          · simp [x, h]
          · have hf : inRangeDec S j = false := by cases h' : inRangeDec S j <;> simp_all
            simp [x, hf]
        rw [sumFinRat_congr _ _ hcongr]
        exact sumFinRat_supported_on_inj S hS_inj (fun j => U i0 j * U i0 j)
      have hux : matVecRat U x i0 = sumSqRat x := by
        unfold matVecRat
        rw [hxsq]
        have hcongr : ∀ j : Fin n, U i0 j * x j = if inRangeDec S j then U i0 j * U i0 j else 0 := by
          intro j
          by_cases h : inRangeDec S j = true
          · simp [x, h]
          · have hf : inRangeDec S j = false := by cases h' : inRangeDec S j <;> simp_all
            simp [x, hf]
        rw [sumFinRat_congr _ _ hcongr]
        exact sumFinRat_supported_on_inj S hS_inj (fun j => U i0 j * U i0 j)
      rw [hux]
      have hxnonneg : (0 : Rat) ≤ sumSqRat x := by
        rw [hxsq]
        exact Rat.le_trans (rat_natCast_nonneg k) hr0
      have hge : (k : Rat) ≤ sumSqRat x := by rw [hxsq]; exact hr0
      exact rat_mul_le_mul_of_nonneg_right hge hxnonneg
  · -- Part (b): Flatness / Hadamard equality characterization for `1 ≤ k < n`
    intro hklt
    constructor
    · intro hbound i
      -- First prove `U i j1^2 = U i j2^2` for all `j1 j2 : Fin n`
      have hconst : ∀ j1 j2 : Fin n, U i j1 * U i j1 = U i j2 * U i j2 := by
        intro j1 j2
        by_cases heq : j1 = j2
        · rw [heq]
        · -- Construct involution-composed bijection `τ` with `τ 0 = j1` and `τ k = j2`
          let z0 : Fin n := ⟨0, hn⟩
          let zk : Fin n := ⟨k, hklt⟩
          let τ1 : Fin n → Fin n := swapFin z0 j1
          let j2' : Fin n := τ1 j2
          let τ2 : Fin n → Fin n := swapFin zk j2'
          let τ : Fin n → Fin n := fun x => τ1 (τ2 x)
          have hτ_inj : isInjective τ := by
            intro a b hab
            exact swapFin_injective zk j2' a b (swapFin_injective z0 j1 _ _ hab)
          have hj2'_ne_z0 : j2' ≠ z0 := by
            intro h
            have : j2 = j1 := by
              have h1 := congrArg τ1 h
              simp only [j2', τ1, swapFin_involutive] at h1
              have h2 : swapFin z0 j1 z0 = j1 := by simp [swapFin]
              rw [h2] at h1
              exact h1
            exact heq this.symm
          have hzk_ne_z0 : zk ≠ z0 := by
            intro h
            have : k = 0 := congrArg Fin.val h
            omega
          have hτ0 : τ z0 = j1 := by
            have h1 : τ2 z0 = z0 := by
              simp [τ2, swapFin, Ne.symm hzk_ne_z0, Ne.symm hj2'_ne_z0]
            simp [τ, h1, τ1, swapFin]
          have hτk : τ zk = j2 := by
            have h1 : τ2 zk = j2' := by simp [τ2, swapFin]
            simp [τ, h1, j2', τ1, swapFin_involutive]
          -- Apply cyclic-shift double counting to `g x := U i (τ x)^2`
          let g : Fin n → Rat := fun x => U i (τ x) * U i (τ x)
          have hg_sum : sumFinRat n g = (n : Rat) := by
            have h1 := sumFinRat_swapFin zk j2' (fun y => U i (τ1 y) * U i (τ1 y))
            have h2 := sumFinRat_swapFin z0 j1 (fun y => U i y * U i y)
            exact Eq.trans h1 (Eq.trans h2 (hrow_norm i))
          have hdc := sumFinRat_cycSupport_double_count (k := k) hn g
          rw [hg_sum] at hdc
          have hle_all : ∀ r : Fin n,
              sumFinRat k (fun t => g (cycSupport hn r t)) ≤ (k : Rat) := by
            intro r
            have hinj : isInjective (fun t : Fin k => τ (cycSupport hn r t)) := by
              intro a b hab
              exact cycSupport_injective hn hkn r a b (hτ_inj _ _ hab)
            exact hbound i (fun t : Fin k => τ (cycSupport hn r t)) hinj
          have hsum_eq : sumFinRat n (fun r => sumFinRat k (fun t => g (cycSupport hn r t))) =
                         (n : Rat) * (k : Rat) := by
            rw [hdc]; grind
          have heq_all := sumFinRat_eq_of_le_of_sum_eq _ (k : Rat) hle_all hsum_eq
          -- Compare `r = 0` and `r = 1`!
          have hr0 := heq_all z0
          have hr1 := heq_all ⟨1, by omega⟩
          -- Prove `sum(r = 0) + g k = g 0 + sum(r = 1)`
          have hdiff : sumFinRat k (fun t => g (cycSupport hn z0 t)) + g zk =
                       g z0 + sumFinRat k (fun t => g (cycSupport hn ⟨1, by omega⟩ t)) := by
            have htele : ∀ (m : Nat) (hm : m ≤ k),
                sumFinRat m (fun t : Fin m => g ⟨t.val, by omega⟩) + g ⟨m, by omega⟩ =
                g z0 + sumFinRat m (fun t : Fin m => g ⟨t.val + 1, by omega⟩) := by
              intro m hm
              induction m with
              | zero =>
                simp only [sumFinRat]
                grind
              | succ p ihp =>
                simp only [sumFinRat]
                have hsub := ihp (by omega)
                have h1 : sumFinRat p (fun t : Fin p => g ⟨t.castSucc.val, by omega⟩) =
                          sumFinRat p (fun t : Fin p => g ⟨t.val, by omega⟩) := by
                  apply sumFinRat_congr; intro t; rfl
                have h2 : sumFinRat p (fun t : Fin p => g ⟨t.castSucc.val + 1, by omega⟩) =
                          sumFinRat p (fun t : Fin p => g ⟨t.val + 1, by omega⟩) := by
                  apply sumFinRat_congr; intro t; rfl
                rw [h1, h2]
                have hl1 : (⟨(Fin.last p).val, by omega⟩ : Fin n) = ⟨p, by omega⟩ := rfl
                have hl2 : (⟨(Fin.last p).val + 1, by omega⟩ : Fin n) = ⟨p + 1, by omega⟩ := rfl
                rw [hl1, hl2]
                grind
            have h0c : sumFinRat k (fun t => g (cycSupport hn z0 t)) =
                       sumFinRat k (fun t : Fin k => g ⟨t.val, by omega⟩) := by
              apply sumFinRat_congr
              intro t
              congr 1; apply Fin.ext
              simp only [cycSupport, z0, Nat.zero_add]
              exact Nat.mod_eq_of_lt (by omega)
            have h1c : sumFinRat k (fun t => g (cycSupport hn ⟨1, by omega⟩ t)) =
                       sumFinRat k (fun t : Fin k => g ⟨t.val + 1, by omega⟩) := by
              apply sumFinRat_congr
              intro t
              congr 1; apply Fin.ext
              simp only [cycSupport]
              have hlt' : 1 + t.val < n := by omega
              rw [Nat.mod_eq_of_lt hlt']
              omega
            rw [h0c, h1c]
            exact htele k (Nat.le_refl k)
          rw [hr0, hr1] at hdiff
          have hgk0 : g z0 = g zk := by grind
          simp only [g, hτ0, hτk] at hgk0
          exact hgk0
      -- Now `∑_j U i j^2 = n` and all `U i j^2` are equal, so each equals `1`!
      intro j
      have hsum_j : sumFinRat n (fun j' => U i j' * U i j') = (n : Rat) * (U i j * U i j) := by
        rw [sumFinRat_congr _ (fun _ => U i j * U i j) (fun j' => hconst j' j), sumFinRat_const]
      rw [hrow_norm i] at hsum_j
      have hn_ne : (n : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hn)
      have hmul : (n : Rat) * (U i j * U i j - 1) = 0 := by grind
      cases Rat.mul_eq_zero.mp hmul with
      | inl h => exact absurd h hn_ne
      | inr h => grind
    · intro hflat i S _
      have hcongr : sumFinRat k (fun t => U i (S t) * U i (S t)) = sumFinRat k (fun _ => (1 : Rat)) :=
        sumFinRat_congr _ _ (fun t => hflat i (S t))
      rw [hcongr, sumFinRat_const]
      have : (k : Rat) * 1 = (k : Rat) := by grind
      rw [this]
      exact Rat.le_refl

/-! ### 5. Proof of Theorem 6: Exact OCP MXFP4 E8M0 Bulk-Crush Threshold & Bit-Budget Dominance -/

theorem rat_inv_pos_of_pos {a : Rat} (ha : (0 : Rat) < a) : (0 : Rat) < 1 / a := by
  apply Classical.byContradiction
  intro hnot
  have hle : 1 / a ≤ 0 := Rat.not_lt.mp hnot
  have hmul := rat_mul_le_mul_of_nonneg_right hle (Rat.le_of_lt ha)
  have hne : a ≠ 0 := Rat.ne_of_gt ha
  have e1 : (1 / a) * a = 1 := by grind
  have e2 : (0 : Rat) * a = 0 := by grind
  rw [e1, e2] at hmul
  exact Rat.not_le.mpr (by decide : (0 : Rat) < 1) hmul

theorem mxfp4_e8m0_bulk_crush_threshold_exact :
    (∀ (B k : Nat) (M S : Rat), 1 ≤ k → k < B → (0 : Rat) ≤ M →
      ((k : Rat) * M) / 6 ≤ S →
      (576 * ((B - k : Nat) : Rat) < ((k : Rat) * (k : Rat)) * (M * M) →
        ((B - k : Nat) : Rat) < (S / 4) * (S / 4)) ∧
      (((k : Rat) * (k : Rat)) * (M * M) = 576 * ((B - k : Nat) : Rat) →
        S = ((k : Rat) * M) / 6 →
        (S / 4) * (S / 4) = ((B - k : Nat) : Rat))) ∧
    ((576 * ((32 - 4 : Nat) : Rat)) / (4 * 4) = 1008 ∧
     (31 : Rat) * 31 < 1008 ∧ (1008 : Rat) < 32 * 32) ∧
    (∀ k : Nat, mxfp4HybridBits 32 k 5 < mxfp6BlockBits 32 ↔ k ≤ 3) ∧
    (∀ k : Nat, mxfp4HybridBits 64 k 6 < mxfp6BlockBits 64 ↔ k ≤ 5) ∧
    (∀ k : Nat, mxfp4HybridBits 16 k 4 < mxfp6BlockBits 16 ↔ k ≤ 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B k M S hk1 _ hM hS
    have hk_nonneg : (0 : Rat) ≤ (k : Rat) := rat_natCast_nonneg k
    have hkM_nonneg : (0 : Rat) ≤ (k : Rat) * M := Rat.mul_nonneg hk_nonneg hM
    have hinv6 : (0 : Rat) < (1 / 6 : Rat) := rat_inv_pos_of_pos (by decide)
    have hinv4 : (0 : Rat) < (1 / 4 : Rat) := rat_inv_pos_of_pos (by decide)
    have hinv576 : (0 : Rat) < (1 / 576 : Rat) := rat_inv_pos_of_pos (by decide)
    have hkm6_nonneg : (0 : Rat) ≤ ((k : Rat) * M) / 6 := by
      have : ((k : Rat) * M) / 6 = ((k : Rat) * M) * (1 / 6) := by grind
      rw [this]
      exact Rat.mul_nonneg hkM_nonneg (Rat.le_of_lt hinv6)
    have hS_nonneg : (0 : Rat) ≤ S := Rat.le_trans hkm6_nonneg hS
    constructor
    · intro hlt
      have h1 := rat_mul_lt_mul_of_pos_left hlt hinv576
      have hlhs : (1 / 576 : Rat) * (576 * ((B - k : Nat) : Rat)) = ((B - k : Nat) : Rat) := by grind
      have hrhs : (1 / 576 : Rat) * (((k : Rat) * (k : Rat)) * (M * M)) =
                  ((((k : Rat) * M) / 6) / 4) * ((((k : Rat) * M) / 6) / 4) := by grind
      rw [hlhs, hrhs] at h1
      have hS4 : (((k : Rat) * M) / 6) / 4 ≤ S / 4 := by
        have := rat_mul_le_mul_of_nonneg_right hS (Rat.le_of_lt hinv4)
        have e1 : (((k : Rat) * M) / 6) * (1 / 4) = (((k : Rat) * M) / 6) / 4 := by grind
        have e2 : S * (1 / 4) = S / 4 := by grind
        rw [e1, e2] at this
        exact this
      have hkm24_nonneg : (0 : Rat) ≤ (((k : Rat) * M) / 6) / 4 := by
        have : (((k : Rat) * M) / 6) / 4 = (((k : Rat) * M) / 6) * (1 / 4) := by grind
        rw [this]
        exact Rat.mul_nonneg hkm6_nonneg (Rat.le_of_lt hinv4)
      have hS4_nonneg : (0 : Rat) ≤ S / 4 := Rat.le_trans hkm24_nonneg hS4
      have hsq : ((((k : Rat) * M) / 6) / 4) * ((((k : Rat) * M) / 6) / 4) ≤ (S / 4) * (S / 4) :=
        Rat.le_trans
          (rat_mul_le_mul_of_nonneg_right hS4 hkm24_nonneg)
          (rat_mul_le_mul_of_nonneg_left hS4 hS4_nonneg)
      exact rat_lt_of_lt_of_le h1 hsq
    · intro heq hSeq
      rw [hSeq]
      have h1 : ((((k : Rat) * M) / 6) / 4) * ((((k : Rat) * M) / 6) / 4) =
                (((k : Rat) * (k : Rat)) * (M * M)) / 576 := by grind
      rw [h1, heq]
      grind
  · refine ⟨by grind, ?_, ?_⟩
    · have h1 : (31 : Rat) * 31 = 961 := by grind
      rw [h1]; decide
    · have h2 : (32 : Rat) * 32 = 1024 := by grind
      rw [h2]; decide
  · intro k; simp only [mxfp4HybridBits, mxfp6BlockBits]; omega
  · intro k; simp only [mxfp4HybridBits, mxfp6BlockBits]; omega
  · intro k; simp only [mxfp4HybridBits, mxfp6BlockBits]; omega

end Paley32Mxfp4
