/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeltanetWyStability.Defs

/-!
# Pure-`Init` Rational, Finite-Sum, Vector, and Matrix Algebra
-/

namespace DeltanetWyStability

/-! ### Basic `Rat` order and arithmetic helpers -/

theorem rat_mul_nonneg {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  have h := Rat.mul_le_mul_of_nonneg_left hb ha
  simpa using h

theorem rat_mul_pos {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have h := Rat.mul_lt_mul_of_pos_left hb ha
  simpa using h

theorem rat_sq_nonneg (x : Rat) : 0 ≤ x * x := by
  rcases @Rat.le_total 0 x with h | h
  · exact rat_mul_nonneg h h
  · have h' : 0 ≤ -x := by grind
    have hsq := rat_mul_nonneg h' h'
    have heq : (-x) * (-x) = x * x := by grind
    rw [← heq]
    exact hsq

theorem rat_mul_le_mul_of_nonneg_right {a b c : Rat} (hab : a ≤ b) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  rw [Rat.mul_comm a c, Rat.mul_comm b c]
  exact Rat.mul_le_mul_of_nonneg_left hab hc

theorem rat_mul_le_mul_nonneg {a b c d : Rat}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hab : a ≤ b) (hcd : c ≤ d) :
    a * c ≤ b * d := by
  have h1 : a * c ≤ b * c := rat_mul_le_mul_of_nonneg_right hab hc
  have hb : 0 ≤ b := Rat.le_trans ha hab
  have h2 : b * c ≤ b * d := Rat.mul_le_mul_of_nonneg_left hcd hb
  exact Rat.le_trans h1 h2

theorem rat_inv_pos {a : Rat} (ha : 0 < a) : 0 < a⁻¹ := by
  have hne : a ≠ 0 := by grind
  have hmul : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hne
  rcases @Rat.le_total a⁻¹ 0 with hle | hge
  · have h1 : a * a⁻¹ ≤ a * 0 := Rat.mul_le_mul_of_nonneg_left hle (by grind)
    grind
  · have hne' : a⁻¹ ≠ 0 := by
      intro h0
      rw [h0] at hmul
      grind
    grind

theorem rat_div_le_iff {a b c : Rat} (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c := by
  have hne : c ≠ 0 := by grind
  constructor
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (by grind : (0 : Rat) ≤ c)
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel c hne] at h1
    simpa using h1
  · intro h
    have hinv : 0 < c⁻¹ := rat_inv_pos hc
    have h1 := rat_mul_le_mul_of_nonneg_right h (by grind : (0 : Rat) ≤ c⁻¹)
    rw [Rat.mul_assoc, Rat.mul_inv_cancel c hne] at h1
    rw [Rat.div_def]
    simpa using h1

theorem rat_le_div_iff {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  have hne : c ≠ 0 := by grind
  constructor
  · intro h
    have h1 := rat_mul_le_mul_of_nonneg_right h (by grind : (0 : Rat) ≤ c)
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel c hne] at h1
    simpa using h1
  · intro h
    have hinv : 0 < c⁻¹ := rat_inv_pos hc
    have h1 := rat_mul_le_mul_of_nonneg_right h (by grind : (0 : Rat) ≤ c⁻¹)
    rw [Rat.mul_assoc, Rat.mul_inv_cancel c hne] at h1
    rw [Rat.div_def]
    simpa using h1

theorem rat_div_le_div_of_le_left {a b c : Rat} (ha : 0 ≤ a) (hb : 0 < b) (hbc : b ≤ c) :
    a / c ≤ a / b := by
  have hc : 0 < c := by grind
  rw [rat_div_le_iff hc]
  have hne : b ≠ 0 := by grind
  have h1 : a / b * b ≤ a / b * c := by
    have hab : 0 ≤ a / b := by
      rw [Rat.div_def]
      exact rat_mul_nonneg ha (by have := rat_inv_pos hb; grind)
    exact Rat.mul_le_mul_of_nonneg_left hbc hab
  have h2 : a / b * b = a := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel b hne]
    simp
  rw [h2] at h1
  exact h1

/-! ### `ratAbs` helpers -/

theorem ratAbs_nonneg (x : Rat) : 0 ≤ ratAbs x := by
  unfold ratAbs
  split <;> grind

theorem ratAbs_of_nonneg {x : Rat} (hx : 0 ≤ x) : ratAbs x = x := by
  unfold ratAbs
  simp [hx]

theorem ratAbs_of_nonpos {x : Rat} (hx : x ≤ 0) : ratAbs x = -x := by
  unfold ratAbs
  split <;> grind

theorem ratAbs_neg (x : Rat) : ratAbs (-x) = ratAbs x := by
  unfold ratAbs
  split <;> split <;> grind

theorem ratAbs_mul (x y : Rat) : ratAbs (x * y) = ratAbs x * ratAbs y := by
  rcases @Rat.le_total 0 x with hx | hx <;> rcases @Rat.le_total 0 y with hy | hy
  · have hxy : 0 ≤ x * y := rat_mul_nonneg hx hy
    rw [ratAbs_of_nonneg hxy, ratAbs_of_nonneg hx, ratAbs_of_nonneg hy]
  · have hxy : x * y ≤ 0 := by
      have h := rat_mul_nonneg hx (by grind : 0 ≤ -y)
      have heq : x * (-y) = -(x * y) := by grind
      grind
    rw [ratAbs_of_nonpos hxy, ratAbs_of_nonneg hx, ratAbs_of_nonpos hy]
    grind
  · have hxy : x * y ≤ 0 := by
      have h := rat_mul_nonneg (by grind : 0 ≤ -x) hy
      have heq : (-x) * y = -(x * y) := by grind
      grind
    rw [ratAbs_of_nonpos hxy, ratAbs_of_nonpos hx, ratAbs_of_nonneg hy]
    grind
  · have hxy : 0 ≤ x * y := by
      have h := rat_mul_nonneg (by grind : 0 ≤ -x) (by grind : 0 ≤ -y)
      have heq : (-x) * (-y) = x * y := by grind
      grind
    rw [ratAbs_of_nonneg hxy, ratAbs_of_nonpos hx, ratAbs_of_nonpos hy]
    grind

theorem ratAbs_le_iff {x a : Rat} : ratAbs x ≤ a ↔ -a ≤ x ∧ x ≤ a := by
  unfold ratAbs
  split <;> grind

/-! ### `ratPow` helpers -/

theorem ratPow_zero (x : Rat) : ratPow x 0 = 1 := rfl

theorem ratPow_succ (x : Rat) (n : Nat) : ratPow x (n + 1) = ratPow x n * x := rfl

theorem ratPow_one (x : Rat) : ratPow x 1 = x := by
  simp [ratPow]

theorem ratPow_one_base (n : Nat) : ratPow 1 n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [ratPow, ih]

theorem ratPow_add (x : Rat) (a b : Nat) : ratPow x (a + b) = ratPow x a * ratPow x b := by
  induction b with
  | zero => simp [ratPow]
  | succ k ih =>
    rw [Nat.add_succ, ratPow, ratPow, ih, Rat.mul_assoc]

theorem ratPow_nonneg {x : Rat} (hx : 0 ≤ x) (n : Nat) : 0 ≤ ratPow x n := by
  induction n with
  | zero => simp only [ratPow]; decide
  | succ k ih => exact rat_mul_nonneg ih hx

theorem ratPow_le_one {x : Rat} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : Nat) : ratPow x n ≤ 1 := by
  induction n with
  | zero => simp [ratPow]
  | succ k ih =>
    rw [ratPow]
    have h := rat_mul_le_mul_nonneg (ratPow_nonneg hx0 k) hx0 ih hx1
    simpa using h

theorem ratAbs_ratPow (x : Rat) (n : Nat) : ratAbs (ratPow x n) = ratPow (ratAbs x) n := by
  induction n with
  | zero => simp only [ratPow, ratAbs]; grind
  | succ k ih =>
    rw [ratPow, ratPow, ratAbs_mul, ih]

/-! ### `sumFin` helpers -/

theorem sumFin_congr {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i = g i) :
    sumFin f = sumFin g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFin]
    rw [ih (fun i => h i.castSucc), h ⟨k, Nat.lt_succ_self k⟩]

theorem sumFin_zero (n : Nat) : sumFin (fun _ : Fin n => (0 : Rat)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFin, ih]
    grind

theorem sumFin_add_fn {n : Nat} (f g : Fin n → Rat) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  induction n with
  | zero => simp only [sumFin]; grind
  | succ k ih =>
    simp only [sumFin, ih]
    grind

theorem sumFin_sub_fn {n : Nat} (f g : Fin n → Rat) :
    sumFin (fun i => f i - g i) = sumFin f - sumFin g := by
  induction n with
  | zero => simp only [sumFin]; grind
  | succ k ih =>
    simp only [sumFin, ih]
    grind

theorem sumFin_neg_fn {n : Nat} (f : Fin n → Rat) :
    sumFin (fun i => -(f i)) = -(sumFin f) := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin, ih]
    grind

theorem sumFin_mul_left {n : Nat} (c : Rat) (f : Fin n → Rat) :
    sumFin (fun i => c * f i) = c * sumFin f := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin, ih]
    grind

theorem sumFin_mul_right {n : Nat} (f : Fin n → Rat) (c : Rat) :
    sumFin (fun i => f i * c) = sumFin f * c := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin, ih]
    grind

theorem sumFin_const (n : Nat) (c : Rat) :
    sumFin (fun _ : Fin n => c) = (n : Rat) * c := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin, ih]
    have hnat : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
      exact Rat.natCast_add k 1
    rw [hnat]
    grind

theorem sumFin_le_sumFin {n : Nat} {f g : Fin n → Rat} (h : ∀ i, f i ≤ g i) :
    sumFin f ≤ sumFin g := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h ⟨k, Nat.lt_succ_self k⟩
    grind

theorem sumFin_nonneg {n : Nat} {f : Fin n → Rat} (h : ∀ i, 0 ≤ f i) :
    0 ≤ sumFin f := by
  have := sumFin_le_sumFin (f := fun _ : Fin n => (0 : Rat)) (g := f) h
  rwa [sumFin_zero] at this

theorem sumFin_single {n : Nat} (a : Fin n) (f : Fin n → Rat)
    (h : ∀ i, i ≠ a → f i = 0) : sumFin f = f a := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ k ih =>
    simp only [sumFin]
    by_cases ha : a.val = k
    · have haeq : a = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext ha
      subst haeq
      have h0 : sumFin (fun i : Fin k => f i.castSucc) = 0 := by
        rw [sumFin_congr (g := fun _ => 0)]
        · exact sumFin_zero k
        · intro i
          apply h i.castSucc
          intro heq
          have hv := congrArg Fin.val heq
          simp at hv
          omega
      rw [h0]
      grind
    · have halt : a.val < k := by omega
      have hlast : f ⟨k, Nat.lt_succ_self k⟩ = 0 := by
        apply h
        intro heq
        have hv := congrArg Fin.val heq
        simp at hv
        omega
      rw [hlast]
      have hrec := ih ⟨a.val, halt⟩ (fun i => f i.castSucc) (fun i hi => by
        apply h i.castSucc
        intro heq
        apply hi
        have hv : i.val = a.val := congrArg Fin.val heq
        exact Fin.ext hv)
      rw [hrec]
      grind

theorem sumFin_add {n m : Nat} (f : Fin (n + m) → Rat) :
    sumFin f =
      sumFin (fun i : Fin n => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n m)⟩) +
      sumFin (fun j : Fin m => f ⟨n + j.val, Nat.add_lt_add_left j.isLt n⟩) := by
  induction m with
  | zero =>
    simp only [Nat.add_zero, sumFin]
    have hc : sumFin f = sumFin (fun i : Fin n => f ⟨i.val, i.isLt⟩) :=
      sumFin_congr (fun i => rfl)
    grind
  | succ k ih =>
    change sumFin (fun i : Fin (n + k) => f i.castSucc) + f ⟨n + k, Nat.lt_succ_self (n + k)⟩ =
      sumFin (fun i : Fin n => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n (k + 1))⟩) +
      (sumFin (fun j : Fin k => f ⟨n + j.castSucc.val, Nat.add_lt_add_left j.castSucc.isLt n⟩) +
       f ⟨n + k, Nat.add_lt_add_left (Nat.lt_succ_self k) n⟩)
    have hrec := ih (fun x : Fin (n + k) => f x.castSucc)
    have h1 : sumFin (fun i : Fin n => f (Fin.castSucc ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n k)⟩)) =
        sumFin (fun i : Fin n => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n (k + 1))⟩) :=
      sumFin_congr (fun i => rfl)
    have h2 : sumFin (fun j : Fin k => f (Fin.castSucc ⟨n + j.val, Nat.add_lt_add_left j.isLt n⟩)) =
        sumFin (fun j : Fin k => f ⟨n + j.castSucc.val, Nat.add_lt_add_left j.castSucc.isLt n⟩) :=
      sumFin_congr (fun j => rfl)
    rw [h1, h2] at hrec
    rw [hrec]
    grind

theorem sumFin_swap {m n : Nat} (f : Fin m → Fin n → Rat) :
    sumFin (fun i => sumFin (fun j => f i j)) = sumFin (fun j => sumFin (fun i => f i j)) := by
  induction m with
  | zero =>
    simp [sumFin, sumFin_zero]
  | succ k ih =>
    simp only [sumFin, ih]
    rw [← sumFin_add_fn]

theorem sumFin_split_at {n : Nat} (i0 : Fin n) (f : Fin n → Rat) :
    sumFin f = f i0 + sumFin (fun i => if i = i0 then 0 else f i) := by
  have h1 : sumFin f = sumFin (fun i => (if i = i0 then f i else 0) + (if i = i0 then 0 else f i)) := by
    apply sumFin_congr
    intro i
    by_cases h : i = i0 <;> simp [h] <;> grind
  rw [h1, sumFin_add_fn]
  have hsingle : sumFin (fun i => if i = i0 then f i else 0) = f i0 := by
    rw [sumFin_single i0]
    · simp
    · intro i hi
      simp [hi]
  rw [hsingle]

/-! ### Vector (`dot`, `normSq`) and Matrix (`matMul`) helpers -/

theorem dot_comm {d : Nat} (u v : Fin d → Rat) : dot u v = dot v u := by
  unfold dot
  exact sumFin_congr (fun i => Rat.mul_comm (u i) (v i))

theorem dot_add_right {d : Nat} (u v w : Fin d → Rat) :
    dot u (fun i => v i + w i) = dot u v + dot u w := by
  unfold dot
  rw [← sumFin_add_fn]
  exact sumFin_congr (fun i => Rat.mul_add (u i) (v i) (w i))

theorem dot_sub_right {d : Nat} (u v w : Fin d → Rat) :
    dot u (fun i => v i - w i) = dot u v - dot u w := by
  unfold dot
  rw [← sumFin_sub_fn]
  exact sumFin_congr (fun i => by grind)

theorem dot_scale_right {d : Nat} (u v : Fin d → Rat) (c : Rat) :
    dot u (fun i => c * v i) = c * dot u v := by
  unfold dot
  rw [← sumFin_mul_left]
  exact sumFin_congr (fun i => by grind)

theorem normSq_nonneg {d : Nat} (v : Fin d → Rat) : 0 ≤ normSq v := by
  unfold normSq dot
  exact sumFin_nonneg (fun i => rat_sq_nonneg (v i))

theorem matMul_assoc {m p q n : Nat} (A : RatMat m p) (B : RatMat p q) (C : RatMat q n) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i j
  unfold matMul
  have h1 : sumFin (fun r => sumFin (fun k => A i k * B k r) * C r j) =
      sumFin (fun r => sumFin (fun k => A i k * B k r * C r j)) :=
    sumFin_congr (fun r => (sumFin_mul_right _ _).symm)
  have h2 : sumFin (fun k => A i k * sumFin (fun r => B k r * C r j)) =
      sumFin (fun k => sumFin (fun r => A i k * (B k r * C r j))) :=
    sumFin_congr (fun k => (sumFin_mul_left _ _).symm)
  rw [h1, h2, sumFin_swap]
  exact sumFin_congr (fun k => sumFin_congr (fun r => Rat.mul_assoc _ _ _))

theorem matMul_id_left {m n : Nat} (A : RatMat m n) : matMul (idMat m) A = A := by
  funext i j
  unfold matMul idMat
  rw [sumFin_single i]
  · simp
  · intro k hk
    have hne : i ≠ k := fun h => hk h.symm
    simp [hne]

theorem matMul_id_right {m n : Nat} (A : RatMat m n) : matMul A (idMat n) = A := by
  funext i j
  unfold matMul idMat
  rw [sumFin_single j]
  · simp
  · intro k hk
    simp [hk]

end DeltanetWyStability
