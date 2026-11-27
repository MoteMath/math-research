/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoRegularGrayDefectCones.Defs

/-!
# Proofs (`two-regular-gray-defect-cones`)

All proofs of the formalized mechanism (zero `sorry`, zero `native_decide`, zero Mathlib).
-/

namespace LinRepEngine

theorem sumFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFin f = sumFin g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFin]
    rw [ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩), h ⟨k, Nat.lt_succ_self k⟩]

theorem sumFin_zero {n : Nat} : sumFin (fun _ : Fin n => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumFin, ih]

theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin, ih]
    omega

theorem sumFin_sub {n : Nat} (f g : Fin n → Int) :
    sumFin (fun i => f i - g i) = sumFin f - sumFin g := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin, ih]
    omega

theorem sumFin_neg {n : Nat} (f : Fin n → Int) :
    sumFin (fun i => -f i) = -sumFin f := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin, ih]
    omega

theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFin (fun i => c * f i) = c * sumFin f := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin, ih, Int.mul_add]

theorem sumFin_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    sumFin (fun i => f i * c) = sumFin f * c := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin, ih, Int.add_mul]

theorem sumFin_comm {m n : Nat} (f : Fin m → Fin n → Int) :
    sumFin (fun i => sumFin (fun j => f i j)) =
    sumFin (fun j => sumFin (fun i => f i j)) := by
  induction m with
  | zero => simp [sumFin, sumFin_zero]
  | succ k ih =>
    simp only [sumFin]
    rw [ih (fun i j => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ j), ← sumFin_add]

theorem sumFin_nonneg {n : Nat} {f : Fin n → Int} (h : ∀ i, 0 ≤ f i) :
    0 ≤ sumFin f := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin]
    have h0 := ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have h1 := h ⟨k, Nat.lt_succ_self k⟩
    omega

theorem sumFin_dvd {n : Nat} {m : Int} {f : Fin n → Int} (h : ∀ i, m ∣ f i) :
    m ∣ sumFin f := by
  induction n with
  | zero => exact Int.dvd_zero m
  | succ k ih =>
    simp only [sumFin]
    exact Int.dvd_add (ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) (h ⟨k, Nat.lt_succ_self k⟩)

/-- Split a sum over `Fin (a + b)` into `Fin a` and `Fin b`. -/
theorem sumFin_split {a b : Nat} (f : Fin (a + b) → Int) :
    sumFin f =
      sumFin (fun i : Fin a => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a b)⟩) +
      sumFin (fun j : Fin b => f ⟨a + j.val, Nat.add_lt_add_left j.isLt a⟩) := by
  induction b with
  | zero =>
    simp only [sumFin, Int.add_zero]
    exact sumFin_congr (fun i => rfl)
  | succ k ih =>
    simp only [sumFin]
    have h1 := ih (fun t => f ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩)
    have hL : sumFin (fun i : Fin (a + k) => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
        sumFin (fun i : Fin a => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right a (k + 1))⟩) +
        sumFin (fun j : Fin k => f ⟨a + j.val, Nat.add_lt_add_left (Nat.lt_succ_of_lt j.isLt) a⟩) := h1
    change sumFin (fun i : Fin (a + k) => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨a + k, _⟩ = _
    rw [hL]
    omega

/-- Helper bound for Kronecker product indexing. -/
theorem kron_idx_lt {a b : Nat} (i : Fin a) (j : Fin b) : j.val * a + i.val < a * b := by
  have hj : j.val + 1 ≤ b := j.isLt
  have h1 : j.val * a + i.val < j.val * a + a := Nat.add_lt_add_left i.isLt (j.val * a)
  have h2 : j.val * a + a = (j.val + 1) * a := by rw [Nat.add_mul, Nat.one_mul]
  have h3 : (j.val + 1) * a ≤ b * a := Nat.mul_le_mul_right a hj
  have h4 : b * a = a * b := Nat.mul_comm b a
  omega

/-- Double-sum factorization over `Fin (a * b)` indexed as `j.val * a + i.val`. -/
theorem sumFin_prod {a b : Nat} (f : Fin (a * b) → Int) :
    sumFin f =
      sumFin (fun j : Fin b =>
        sumFin (fun i : Fin a =>
          f ⟨j.val * a + i.val, kron_idx_lt i j⟩)) := by
  induction b with
  | zero => simp [sumFin]
  | succ k ih =>
    change sumFin (f : Fin (a * k + a) → Int) = _
    rw [sumFin_split (a := a * k) (b := a) f]
    simp only [sumFin]
    rw [ih (fun t => f ⟨t.val, Nat.lt_of_lt_of_le t.isLt (Nat.le_add_right (a * k) a)⟩)]
    congr 1
    apply sumFin_congr
    intro i
    congr 1
    apply Fin.ext
    simp [Nat.mul_comm]

def vecAdd {d : Nat} (u v : Vec d) : Vec d :=
  fun i => u i + v i

def vecZero (d : Nat) : Vec d :=
  fun _ => 0

def matAdd {m n : Nat} (A B : Mat m n) : Mat m n :=
  fun i j => A i j + B i j

-- Fundamental linear algebra lemmas
theorem vecEq_iff_eq {d : Nat} {u v : Vec d} : VecEq u v ↔ u = v :=
  ⟨fun h => funext h, fun h i => congrFun h i⟩

theorem dot_congr {d : Nat} {u1 u2 v1 v2 : Vec d} (hu : VecEq u1 u2) (hv : VecEq v1 v2) :
    dot u1 v1 = dot u2 v2 :=
  sumFin_congr (fun i => by rw [hu i, hv i])

theorem dot_vecScale_left {d : Nat} (c : Int) (u v : Vec d) :
    dot (vecScale c u) v = c * dot u v := by
  simp only [dot, vecScale, Int.mul_assoc]
  exact sumFin_mul_left c (fun i => u i * v i)

theorem dot_vecScale_right {d : Nat} (c : Int) (u v : Vec d) :
    dot u (vecScale c v) = c * dot u v := by
  simp only [dot, vecScale]
  rw [← sumFin_mul_left]
  exact sumFin_congr (fun i => by rw [Int.mul_left_comm])

theorem dot_vecAdd_right {d : Nat} (u v w : Vec d) :
    dot u (vecAdd v w) = dot u v + dot u w := by
  simp only [dot, vecAdd, Int.mul_add]
  exact sumFin_add _ _

theorem dot_vecZero_right {d : Nat} (u : Vec d) : dot u (vecZero d) = 0 := by
  simp only [dot, vecZero, Int.mul_zero]
  exact sumFin_zero

theorem matVec_congr {m n : Nat} {A B : Mat m n} {x y : Vec n}
    (hM : MatEq A B) (hx : VecEq x y) : VecEq (matVec A x) (matVec B y) :=
  fun i => sumFin_congr (fun j => by rw [hM i j, hx j])

theorem matVec_matMul {m k n : Nat} (A : Mat m k) (B : Mat k n) (v : Vec n) :
    VecEq (matVec (matMul A B) v) (matVec A (matVec B v)) := by
  intro i
  simp only [matVec, matMul]
  have h1 : sumFin (fun j => sumFin (fun t => A i t * B t j) * v j) =
            sumFin (fun j => sumFin (fun t => A i t * (B t j * v j))) := by
    apply sumFin_congr; intro j
    rw [← sumFin_mul_right]
    apply sumFin_congr; intro t
    exact Int.mul_assoc _ _ _
  rw [h1, sumFin_comm]
  apply sumFin_congr; intro t
  rw [← sumFin_mul_left]

theorem dot_matVec_eq_dot_matT {m n : Nat} (u : Vec m) (M : Mat m n) (v : Vec n) :
    dot u (matVec M v) = dot (matVec (matT M) u) v := by
  simp only [dot, matVec, matT]
  have h1 : sumFin (fun i => u i * sumFin (fun j => M i j * v j)) =
            sumFin (fun i => sumFin (fun j => (M i j * u i) * v j)) := by
    apply sumFin_congr; intro i
    rw [← sumFin_mul_left]
    apply sumFin_congr; intro j
    rw [Int.mul_comm (M i j) (u i), Int.mul_assoc]
  rw [h1, sumFin_comm]
  apply sumFin_congr; intro j
  rw [← sumFin_mul_right]

theorem matVec_matScale {m n : Nat} (c : Int) (M : Mat m n) (v : Vec n) :
    VecEq (matVec (matScale c M) v) (vecScale c (matVec M v)) := by
  intro i
  simp only [matVec, matScale, vecScale, Int.mul_assoc]
  exact sumFin_mul_left c (fun j => M i j * v j)

theorem matVec_vecAdd {m n : Nat} (M : Mat m n) (x y : Vec n) :
    VecEq (matVec M (vecAdd x y)) (vecAdd (matVec M x) (matVec M y)) := by
  intro i
  simp only [matVec, vecAdd, Int.mul_add]
  exact sumFin_add _ _

theorem matVec_matAdd {m n : Nat} (A B : Mat m n) (x : Vec n) :
    VecEq (matVec (matAdd A B) x) (vecAdd (matVec A x) (matVec B x)) := by
  intro i
  simp only [matVec, matAdd, vecAdd, Int.add_mul]
  exact sumFin_add _ _

theorem matVec_vecZero {m n : Nat} (M : Mat m n) :
    VecEq (matVec M (vecZero n)) (vecZero m) := by
  intro i
  simp only [matVec, vecZero, Int.mul_zero]
  exact sumFin_zero

theorem vecNonneg_matVec {m n : Nat} {C : Mat m n} {x : Vec n}
    (hC : MatNonneg C) (hx : VecNonneg x) : VecNonneg (matVec C x) := by
  intro i
  exact sumFin_nonneg (fun j => Int.mul_nonneg (hC i j) (hx j))

theorem dot_nonneg {d : Nat} {u v : Vec d} (hu : VecNonneg u) (hv : VecNonneg v) :
    0 ≤ dot u v :=
  sumFin_nonneg (fun i => Int.mul_nonneg (hu i) (hv i))

theorem dvd_of_emod_eq_zero {m a : Int} (h : a % m = 0) : m ∣ a :=
  Int.dvd_of_emod_eq_zero h

theorem vecDvd_matVec {r c : Nat} {m : Int} (M : Mat r c) {x : Vec c}
    (hx : ∀ j, m ∣ x j) : ∀ i, m ∣ matVec M x i := by
  intro i
  exact sumFin_dvd (fun j => Int.dvd_mul_of_dvd_right (hx j))

theorem dot_dvd_right {d : Nat} {m : Int} (u : Vec d) {v : Vec d}
    (hv : ∀ i, m ∣ v i) : m ∣ dot u v :=
  sumFin_dvd (fun i => Int.dvd_mul_of_dvd_right (hv i))

/-- Bit-string evaluation `M_{b_0} * M_{b_1} * ... * M_{b_k} * v` (LSB-first). -/
def evalBits {d : Nat} (M0 M1 : Mat d d) (v : Vec d) : List Bool → Vec d
  | [] => v
  | b :: bs => matVec (if b then M1 else M0) (evalBits M0 M1 v bs)

/-- Canonical LSB-first binary bit list of `n : Nat` (empty list for `0`). -/
def bitsOf (n : Nat) : List Bool :=
  if h : n = 0 then []
  else (n % 2 == 1) :: bitsOf (n / 2)
termination_by n
decreasing_by omega

theorem evalVec_zero {d : Nat} (R : LinRep d) : evalVec R 0 = R.v := by
  unfold evalVec; simp

theorem evalVec_eq_evalBits_bitsOf {d : Nat} (R : LinRep d) (n : Nat) :
    evalVec R n = evalBits R.M0 R.M1 R.v (bitsOf n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold evalVec bitsOf
    split
    · rfl
    · rename_i hne
      simp only [evalBits]
      rw [ih (n / 2) (by omega)]

theorem evalBits_append_false {d : Nat} (R : LinRep d) (bs : List Bool) :
    evalBits R.M0 R.M1 R.v (bs ++ [false]) = evalBits R.M0 R.M1 R.v bs := by
  induction bs with
  | nil =>
    simp only [List.nil_append, evalBits, Bool.false_eq_true, ↓reduceIte]
    exact vecEq_iff_eq.mp R.stable
  | cons b tl ih =>
    simp only [List.cons_append, evalBits, ih]

theorem replicate_succ_append {α : Type} (m : Nat) (x : α) :
    List.replicate (m + 1) x = List.replicate m x ++ [x] := by
  induction m with
  | zero => rfl
  | succ k ih =>
    calc List.replicate (k + 2) x
        = x :: List.replicate (k + 1) x := List.replicate_succ
      _ = x :: (List.replicate k x ++ [x]) := by rw [ih]
      _ = (x :: List.replicate k x) ++ [x] := rfl
      _ = List.replicate (k + 1) x ++ [x] := by rw [← List.replicate_succ]

/-- Leading-zero invariance: padding any number of MSB zero bits preserves `evalBits`. -/
theorem evalBits_append_zeros {d : Nat} (R : LinRep d) (bs : List Bool) (k : Nat) :
    evalBits R.M0 R.M1 R.v (bs ++ List.replicate k false) = evalBits R.M0 R.M1 R.v bs := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [replicate_succ_append, ← List.append_assoc, evalBits_append_false, ih]

theorem evalVec_two_mul {d : Nat} (R : LinRep d) (n : Nat) :
    evalVec R (2 * n) = matVec R.M0 (evalVec R n) := by
  cases n with
  | zero =>
    simp only [Nat.mul_zero, evalVec_zero]
    exact (vecEq_iff_eq.mp R.stable).symm
  | succ k =>
    conv => lhs; unfold evalVec
    have hne : 2 * (k + 1) ≠ 0 := by omega
    have hmod : (2 * (k + 1)) % 2 = 0 := by omega
    have hdiv : (2 * (k + 1)) / 2 = k + 1 := by omega
    simp [hne, hmod, hdiv]

theorem evalVec_two_mul_add_one {d : Nat} (R : LinRep d) (n : Nat) :
    evalVec R (2 * n + 1) = matVec R.M1 (evalVec R n) := by
  conv => lhs; unfold evalVec
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [hmod, hdiv]

theorem evalVec_one {d : Nat} (R : LinRep d) :
    evalVec R 1 = matVec R.M1 R.v := by
  simpa [evalVec_zero] using evalVec_two_mul_add_one R 0

theorem sumRange_congr {f g : Nat → Int} (h : ∀ k, f k = g k) (n : Nat) :
    sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumRange, ih, h k]

theorem sumRange_two_mul (f : Nat → Int) (n : Nat) :
    sumRange f (2 * n) = sumRange (fun k => f (2 * k) + f (2 * k + 1)) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h1, sumRange, sumRange, ih, sumRange]
    omega

/-- Vector-valued prefix sum `∑_{k=0}^{n-1} evalVec R k`. -/
def sumVec {d : Nat} (R : LinRep d) : Nat → Vec d
  | 0 => vecZero d
  | n + 1 => vecAdd (sumVec R n) (evalVec R n)

theorem dot_sumVec {d : Nat} (R : LinRep d) (n : Nat) :
    dot R.u (sumVec R n) = sumRange (evalRep R) n := by
  induction n with
  | zero => simp [sumVec, sumRange, dot_vecZero_right]
  | succ k ih =>
    simp only [sumVec, sumRange, dot_vecAdd_right, ih, evalRep]

theorem sumVec_two_mul {d : Nat} (R : LinRep d) (n : Nat) :
    VecEq (sumVec R (2 * n)) (matVec (matAdd R.M0 R.M1) (sumVec R n)) := by
  induction n with
  | zero =>
    simp only [sumVec]
    exact fun i => (matVec_vecZero (matAdd R.M0 R.M1) i).symm
  | succ k ih =>
    intro i
    have h1 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h1, sumVec, sumVec, vecAdd, vecAdd, ih i, evalVec_two_mul, evalVec_two_mul_add_one]
    have hadd := matVec_vecAdd (matAdd R.M0 R.M1) (sumVec R k) (evalVec R k) i
    have hma := matVec_matAdd R.M0 R.M1 (evalVec R k) i
    simp only [sumVec, vecAdd] at hadd hma ⊢
    rw [hadd, hma]
    omega

theorem sumVec_two_mul_add_one {d : Nat} (R : LinRep d) (n : Nat) :
    VecEq (sumVec R (2 * n + 1))
      (vecAdd (matVec R.M0 (evalVec R n)) (matVec (matAdd R.M0 R.M1) (sumVec R n))) := by
  intro i
  rw [sumVec, vecAdd, sumVec_two_mul R n i, evalVec_two_mul]
  simp only [vecAdd]
  omega

-- Block vector/matrix helpers for `a + b`
def vecAppend {a b : Nat} (x : Vec a) (y : Vec b) : Vec (a + b) :=
  fun i =>
    if h : i.val < a then x ⟨i.val, h⟩
    else y ⟨i.val - a, by omega⟩

def matBlock {a b c d : Nat}
    (M11 : Mat a c) (M12 : Mat a d) (M21 : Mat b c) (M22 : Mat b d) : Mat (a + b) (c + d) :=
  fun i j =>
    if hi : i.val < a then
      if hj : j.val < c then M11 ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else M12 ⟨i.val, hi⟩ ⟨j.val - c, by omega⟩
    else
      if hj : j.val < c then M21 ⟨i.val - a, by omega⟩ ⟨j.val, hj⟩
      else M22 ⟨i.val - a, by omega⟩ ⟨j.val - c, by omega⟩

def matZero (m n : Nat) : Mat m n := fun _ _ => 0

theorem dot_vecAppend {a b : Nat} (u1 : Vec a) (u2 : Vec b) (v1 : Vec a) (v2 : Vec b) :
    dot (vecAppend u1 u2) (vecAppend v1 v2) = dot u1 v1 + dot u2 v2 := by
  simp only [dot]
  rw [sumFin_split]
  congr 1
  · apply sumFin_congr; intro i
    simp [vecAppend, i.isLt]
  · apply sumFin_congr; intro j
    have hnot : ¬ (a + j.val < a) := by omega
    simp [vecAppend, hnot]

theorem matVec_matBlock {a b c d : Nat}
    (M11 : Mat a c) (M12 : Mat a d) (M21 : Mat b c) (M22 : Mat b d)
    (x : Vec c) (y : Vec d) :
    VecEq (matVec (matBlock M11 M12 M21 M22) (vecAppend x y))
      (vecAppend (vecAdd (matVec M11 x) (matVec M12 y))
                 (vecAdd (matVec M21 x) (matVec M22 y))) := by
  intro i
  simp only [matVec]
  rw [sumFin_split]
  by_cases hi : i.val < a
  · simp only [vecAppend, hi, ↓reduceDIte, vecAdd]
    congr 1
    · apply sumFin_congr; intro j
      simp [matBlock, hi, j.isLt]
    · apply sumFin_congr; intro j
      have hnot : ¬ (c + j.val < c) := by omega
      simp [matBlock, hi, hnot]
  · simp only [vecAppend, hi, ↓reduceDIte, vecAdd]
    congr 1
    · apply sumFin_congr; intro j
      simp [matBlock, hi, j.isLt]
    · apply sumFin_congr; intro j
      have hnot : ¬ (c + j.val < c) := by omega
      simp [matBlock, hi, hnot]

-- 1. Constant combinator
def LinRep.const (c : Int) : LinRep 1 where
  u := fun _ => c
  M0 := fun _ _ => 1
  M1 := fun _ _ => 1
  v := fun _ => 1
  stable := by decide

theorem evalRep_const (c : Int) (n : Nat) : evalRep (LinRep.const c) n = c := by
  have hvec : ∀ k, evalVec (LinRep.const c) k = fun _ => 1 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      unfold evalVec
      split
      · rfl
      · rename_i hne
        rw [ih (k / 2) (by omega)]
        funext i
        split <;> simp [LinRep.const, matVec, sumFin]
  rw [evalRep, hvec n]
  simp [LinRep.const, dot, sumFin]

-- 2. Scalar multiplication combinator
def LinRep.scale {d : Nat} (c : Int) (R : LinRep d) : LinRep d where
  u := vecScale c R.u
  M0 := R.M0
  M1 := R.M1
  v := R.v
  stable := R.stable

theorem evalVec_scale {d : Nat} (c : Int) (R : LinRep d) (n : Nat) :
    evalVec (LinRep.scale c R) n = evalVec R n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold evalVec
    split
    · rfl
    · rename_i hne
      rw [ih (n / 2) (by omega)]
      rfl

theorem evalRep_scale {d : Nat} (c : Int) (R : LinRep d) (n : Nat) :
    evalRep (LinRep.scale c R) n = c * evalRep R n := by
  rw [evalRep, evalVec_scale, LinRep.scale, dot_vecScale_left, evalRep]

-- 3. Direct-sum addition combinator
def LinRep.add {d1 d2 : Nat} (R1 : LinRep d1) (R2 : LinRep d2) : LinRep (d1 + d2) where
  u := vecAppend R1.u R2.u
  M0 := matBlock R1.M0 (matZero d1 d2) (matZero d2 d1) R2.M0
  M1 := matBlock R1.M1 (matZero d1 d2) (matZero d2 d1) R2.M1
  v := vecAppend R1.v R2.v
  stable := by
    intro i
    rw [matVec_matBlock]
    by_cases hi : i.val < d1
    · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.add_zero]
      exact R1.stable ⟨i.val, hi⟩
    · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.zero_add]
      exact R2.stable ⟨i.val - d1, by omega⟩

theorem evalVec_add {d1 d2 : Nat} (R1 : LinRep d1) (R2 : LinRep d2) (n : Nat) :
    evalVec (LinRep.add R1 R2) n = vecAppend (evalVec R1 n) (evalVec R2 n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold evalVec
    split
    · rfl
    · rename_i hne
      rw [ih (n / 2) (by omega)]
      apply vecEq_iff_eq.mp
      split <;>
      · intro i
        simp only [LinRep.add]
        rw [matVec_matBlock]
        by_cases hi : i.val < d1
        · simp [vecAppend, hi, vecAdd, matVec, matZero, sumFin_zero]
        · simp [vecAppend, hi, vecAdd, matVec, matZero, sumFin_zero]

theorem evalRep_add {d1 d2 : Nat} (R1 : LinRep d1) (R2 : LinRep d2) (n : Nat) :
    evalRep (LinRep.add R1 R2) n = evalRep R1 n + evalRep R2 n := by
  rw [evalRep, evalVec_add, LinRep.add, dot_vecAppend, evalRep, evalRep]

-- 4. Subtraction combinator
def LinRep.sub {d1 d2 : Nat} (R1 : LinRep d1) (R2 : LinRep d2) : LinRep (d1 + d2) :=
  LinRep.add R1 (LinRep.scale (-1) R2)

theorem evalRep_sub {d1 d2 : Nat} (R1 : LinRep d1) (R2 : LinRep d2) (n : Nat) :
    evalRep (LinRep.sub R1 R2) n = evalRep R1 n - evalRep R2 n := by
  rw [LinRep.sub, evalRep_add, evalRep_scale]
  omega

-- 5. Kronecker-product multiplication combinator (2-regular ring closure!)
theorem kron_div_lt {a b : Nat} (k : Fin (a * b)) : k.val / a < b :=
  Nat.div_lt_of_lt_mul k.isLt

def kronVec {a b : Nat} (x : Vec a) (y : Vec b) : Vec (a * b) :=
  fun k =>
    if ha : a = 0 then 0
    else
      have hlt1 : k.val % a < a := Nat.mod_lt _ (Nat.pos_of_ne_zero ha)
      x ⟨k.val % a, hlt1⟩ * y ⟨k.val / a, kron_div_lt k⟩

def kronMat {a b : Nat} (A : Mat a a) (B : Mat b b) : Mat (a * b) (a * b) :=
  fun r c =>
    if ha : a = 0 then 0
    else
      have hr1 : r.val % a < a := Nat.mod_lt _ (Nat.pos_of_ne_zero ha)
      have hc1 : c.val % a < a := Nat.mod_lt _ (Nat.pos_of_ne_zero ha)
      A ⟨r.val % a, hr1⟩ ⟨c.val % a, hc1⟩ * B ⟨r.val / a, kron_div_lt r⟩ ⟨c.val / a, kron_div_lt c⟩

theorem dot_kronVec {a b : Nat} (u1 v1 : Vec a) (u2 v2 : Vec b) :
    dot (kronVec u1 u2) (kronVec v1 v2) = dot u1 v1 * dot u2 v2 := by
  by_cases ha : a = 0
  · subst ha
    simp [dot, kronVec, sumFin, sumFin_zero]
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha
    simp only [dot]
    rw [sumFin_prod]
    have hinner : ∀ j : Fin b,
        sumFin (fun i : Fin a =>
          kronVec u1 u2 ⟨j.val * a + i.val, kron_idx_lt i j⟩ *
          kronVec v1 v2 ⟨j.val * a + i.val, kron_idx_lt i j⟩) =
        sumFin (fun i : Fin a => u1 i * v1 i) * (u2 j * v2 j) := by
      intro j
      rw [← sumFin_mul_right]
      apply sumFin_congr; intro i
      have hmod : (j.val * a + i.val) % a = i.val := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
      have hdiv : (j.val * a + i.val) / a = j.val := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hapos, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
      simp only [kronVec, ha, ↓reduceDIte, hmod, hdiv]
      rw [Int.mul_assoc, Int.mul_left_comm (u2 j) (v1 i) (v2 j), ← Int.mul_assoc]
    rw [sumFin_congr hinner, sumFin_mul_left]

theorem matVec_kronMat {a b : Nat} (A : Mat a a) (B : Mat b b) (x : Vec a) (y : Vec b) :
    VecEq (matVec (kronMat A B) (kronVec x y)) (kronVec (matVec A x) (matVec B y)) := by
  intro r
  by_cases ha : a = 0
  · subst ha; exfalso; have := r.isLt; simp at this
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha
    simp only [matVec]
    rw [sumFin_prod]
    have hr1 : r.val % a < a := Nat.mod_lt _ hapos
    have hr2 : r.val / a < b := kron_div_lt r
    have hinner : ∀ j : Fin b,
        sumFin (fun i : Fin a =>
          kronMat A B r ⟨j.val * a + i.val, kron_idx_lt i j⟩ *
          kronVec x y ⟨j.val * a + i.val, kron_idx_lt i j⟩) =
        matVec A x ⟨r.val % a, hr1⟩ * (B ⟨r.val / a, hr2⟩ j * y j) := by
      intro j
      simp only [matVec]
      rw [← sumFin_mul_right]
      apply sumFin_congr; intro i
      have hmod : (j.val * a + i.val) % a = i.val := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
      have hdiv : (j.val * a + i.val) / a = j.val := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hapos, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
      simp only [kronMat, kronVec, ha, ↓reduceDIte, hmod, hdiv]
      rw [Int.mul_assoc, Int.mul_left_comm (B ⟨r.val / a, hr2⟩ j) (x i) (y j), ← Int.mul_assoc]
    rw [sumFin_congr hinner, sumFin_mul_left]
    simp only [kronVec, ha, ↓reduceDIte, matVec]

def LinRep.mul {d1 d2 : Nat} (R1 : LinRep d1) (R2 : LinRep d2) : LinRep (d1 * d2) where
  u := kronVec R1.u R2.u
  M0 := kronMat R1.M0 R2.M0
  M1 := kronMat R1.M1 R2.M1
  v := kronVec R1.v R2.v
  stable := by
    intro r
    rw [matVec_kronMat]
    by_cases h1 : d1 = 0
    · subst h1; exfalso; have := r.isLt; simp at this
    · simp only [kronVec, h1, ↓reduceDIte]
      rw [R1.stable, R2.stable]

theorem evalVec_mul {d1 d2 : Nat} (R1 : LinRep d1) (R2 : LinRep d2) (n : Nat) :
    evalVec (LinRep.mul R1 R2) n = kronVec (evalVec R1 n) (evalVec R2 n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold evalVec
    split
    · rfl
    · rename_i hne
      rw [ih (n / 2) (by omega)]
      apply vecEq_iff_eq.mp
      split
      · exact matVec_kronMat R1.M1 R2.M1 _ _
      · exact matVec_kronMat R1.M0 R2.M0 _ _

theorem evalRep_mul {d1 d2 : Nat} (R1 : LinRep d1) (R2 : LinRep d2) (n : Nat) :
    evalRep (LinRep.mul R1 R2) n = evalRep R1 n * evalRep R2 n := by
  rw [evalRep, evalVec_mul, LinRep.mul, dot_kronVec, evalRep, evalRep]

-- 6. Even & Odd decimation combinators
def LinRep.even {d : Nat} (R : LinRep d) : LinRep d where
  u := matVec (matT R.M0) R.u
  M0 := R.M0
  M1 := R.M1
  v := R.v
  stable := R.stable

def LinRep.odd {d : Nat} (R : LinRep d) : LinRep d where
  u := matVec (matT R.M1) R.u
  M0 := R.M0
  M1 := R.M1
  v := R.v
  stable := R.stable

theorem evalVec_even {d : Nat} (R : LinRep d) (n : Nat) :
    evalVec (LinRep.even R) n = evalVec R n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold evalVec
    split
    · rfl
    · rename_i hne
      rw [ih (n / 2) (by omega)]
      rfl

theorem evalVec_odd {d : Nat} (R : LinRep d) (n : Nat) :
    evalVec (LinRep.odd R) n = evalVec R n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold evalVec
    split
    · rfl
    · rename_i hne
      rw [ih (n / 2) (by omega)]
      rfl

theorem evalRep_even {d : Nat} (R : LinRep d) (n : Nat) :
    evalRep (LinRep.even R) n = evalRep R (2 * n) := by
  rw [evalRep, evalVec_even, LinRep.even, ← dot_matVec_eq_dot_matT, ← evalVec_two_mul, evalRep]

theorem evalRep_odd {d : Nat} (R : LinRep d) (n : Nat) :
    evalRep (LinRep.odd R) n = evalRep R (2 * n + 1) := by
  rw [evalRep, evalVec_odd, LinRep.odd, ← dot_matVec_eq_dot_matT, ← evalVec_two_mul_add_one, evalRep]

-- 7. Shift-by-1 combinator: compiles f(n) |-> f(n + 1) via a 2-state carry block matrix!
def LinRep.shift1 {d : Nat} (R : LinRep d) : LinRep (d + d) where
  u := vecAppend (vecZero d) R.u
  M0 := matBlock R.M0 (matZero d d) R.M1 (matZero d d)
  M1 := matBlock R.M1 (matZero d d) (matZero d d) R.M0
  v := vecAppend R.v (matVec R.M1 R.v)
  stable := by
    intro i
    rw [matVec_matBlock]
    by_cases hi : i.val < d
    · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.add_zero]
      exact R.stable ⟨i.val, hi⟩
    · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.add_zero]

theorem evalVec_shift1 {d : Nat} (R : LinRep d) (n : Nat) :
    evalVec (LinRep.shift1 R) n = vecAppend (evalVec R n) (evalVec R (n + 1)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      simp only [evalVec_zero, LinRep.shift1, Nat.zero_add, evalVec_one]
    | succ k =>
      have hsplit : (k + 1) = 2 * ((k + 1) / 2) + (k + 1) % 2 := by omega
      by_cases hmod : (k + 1) % 2 = 0
      · have h2 : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        rw [h2, evalVec_two_mul, ih ((k + 1) / 2) hlt]
        apply vecEq_iff_eq.mp
        intro i
        simp only [LinRep.shift1]
        rw [matVec_matBlock]
        by_cases hi : i.val < d
        · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.add_zero]
          rw [evalVec_two_mul]; rfl
        · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.add_zero]
          rw [evalVec_two_mul_add_one]; rfl
      · have hmod1 : (k + 1) % 2 = 1 := by omega
        have h2 : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        have h2s : (2 * ((k + 1) / 2) + 1) + 1 = 2 * (((k + 1) / 2) + 1) := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        rw [h2, evalVec_two_mul_add_one, ih ((k + 1) / 2) hlt]
        apply vecEq_iff_eq.mp
        intro i
        simp only [LinRep.shift1]
        rw [matVec_matBlock]
        by_cases hi : i.val < d
        · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.add_zero]
          rw [evalVec_two_mul_add_one]; rfl
        · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.zero_add]
          rw [h2s, evalVec_two_mul]; rfl

theorem evalRep_shift1 {d : Nat} (R : LinRep d) (n : Nat) :
    evalRep (LinRep.shift1 R) n = evalRep R (n + 1) := by
  rw [evalRep, evalVec_shift1, LinRep.shift1, dot_vecAppend]
  have hz : dot (vecZero d) (evalVec R n) = 0 := by
    simp [dot, vecZero, sumFin_zero]
  rw [hz, Int.zero_add, evalRep]

-- 8. Prefix-sum combinator: compiles f(n) |-> ∑_{k=0}^{n-1} f(k)!
def LinRep.prefixSum {d : Nat} (R : LinRep d) : LinRep (d + d) where
  u := vecAppend (vecZero d) R.u
  M0 := matBlock R.M0 (matZero d d) (matZero d d) (matAdd R.M0 R.M1)
  M1 := matBlock R.M1 (matZero d d) R.M0 (matAdd R.M0 R.M1)
  v := vecAppend R.v (vecZero d)
  stable := by
    intro i
    rw [matVec_matBlock]
    by_cases hi : i.val < d
    · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.add_zero]
      exact R.stable ⟨i.val, hi⟩
    · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, vecZero,
                 Int.zero_mul, Int.mul_zero, sumFin_zero, Int.add_zero]

theorem evalVec_prefixSum {d : Nat} (R : LinRep d) (n : Nat) :
    evalVec (LinRep.prefixSum R) n = vecAppend (evalVec R n) (sumVec R n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      simp only [evalVec_zero, LinRep.prefixSum, sumVec]
    | succ k =>
      by_cases hmod : (k + 1) % 2 = 0
      · have h2 : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        rw [h2, evalVec_two_mul, ih ((k + 1) / 2) hlt]
        apply vecEq_iff_eq.mp
        intro i
        simp only [LinRep.prefixSum]
        rw [matVec_matBlock]
        by_cases hi : i.val < d
        · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.add_zero]
          rw [evalVec_two_mul]; rfl
        · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.zero_add]
          exact (sumVec_two_mul R ((k + 1) / 2) ⟨i.val - d, by omega⟩).symm
      · have h2 : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        rw [h2, evalVec_two_mul_add_one, ih ((k + 1) / 2) hlt]
        apply vecEq_iff_eq.mp
        intro i
        simp only [LinRep.prefixSum]
        rw [matVec_matBlock]
        by_cases hi : i.val < d
        · simp only [vecAppend, hi, ↓reduceDIte, vecAdd, matVec, matZero, Int.zero_mul, sumFin_zero, Int.add_zero]
          rw [evalVec_two_mul_add_one]; rfl
        · simp only [vecAppend, hi, ↓reduceDIte]
          exact (sumVec_two_mul_add_one R ((k + 1) / 2) ⟨i.val - d, by omega⟩).symm

theorem evalRep_prefixSum {d : Nat} (R : LinRep d) (n : Nat) :
    evalRep (LinRep.prefixSum R) n = sumRange (evalRep R) n := by
  rw [evalRep, evalVec_prefixSum, LinRep.prefixSum, dot_vecAppend]
  have hz : dot (vecZero d) (evalVec R n) = 0 := by simp [dot, vecZero, sumFin_zero]
  rw [hz, Int.zero_add, dot_sumVec]

-- ============================================================================
-- Section 4: The Four Finite-Certificate Infinite Proof Engines
-- ============================================================================

/-- Engine 1: Scaled Left-Invariant Nullspace Certificate.
    A finite integer certificate `(K, C0, C1, c, alpha, beta)` proves `∀ n, evalRep R n = 0`. -/
structure IdentityCert {d : Nat} (R : LinRep d) (r : Nat) where
  K        : Mat r d
  C0       : Mat r r
  C1       : Mat r r
  c        : Vec r
  alpha    : Int
  beta     : Int
  alpha_ne : alpha ≠ 0
  beta_ne  : beta ≠ 0
  base     : VecEq (matVec K R.v) (vecZero r)
  step0    : MatEq (matScale beta (matMul K R.M0)) (matMul C0 K)
  step1    : MatEq (matScale beta (matMul K R.M1)) (matMul C1 K)
  cover    : VecEq (vecScale alpha R.u) (matVec (matT K) c)

theorem IdentityCert.sound {d r : Nat} {R : LinRep d} (cert : IdentityCert R r) :
    ∀ n : Nat, evalRep R n = 0 := by
  have hinv : ∀ n : Nat, VecEq (matVec cert.K (evalVec R n)) (vecZero r) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      unfold evalVec
      split
      · exact cert.base
      · rename_i hne
        have hq := ih (n / 2) (by omega)
        intro i
        have hstep : cert.beta * matVec cert.K
            (matVec (if n % 2 == 1 then R.M1 else R.M0) (evalVec R (n / 2))) i = 0 := by
          split
          · have h1 := matVec_matScale cert.beta (matMul cert.K R.M1) (evalVec R (n / 2)) i
            have h2 := matVec_congr cert.step1 (fun _ => rfl) (x := evalVec R (n / 2)) i
            have h3 := matVec_matMul cert.K R.M1 (evalVec R (n / 2)) i
            have h4 := matVec_matMul cert.C1 cert.K (evalVec R (n / 2)) i
            have h5 := matVec_congr (fun _ _ => rfl) hq (A := cert.C1) i
            have h6 := matVec_vecZero cert.C1 i
            simp only [vecScale] at h1
            rw [← h3, ← h1, h2, h4, h5, h6]; rfl
          · have h1 := matVec_matScale cert.beta (matMul cert.K R.M0) (evalVec R (n / 2)) i
            have h2 := matVec_congr cert.step0 (fun _ => rfl) (x := evalVec R (n / 2)) i
            have h3 := matVec_matMul cert.K R.M0 (evalVec R (n / 2)) i
            have h4 := matVec_matMul cert.C0 cert.K (evalVec R (n / 2)) i
            have h5 := matVec_congr (fun _ _ => rfl) hq (A := cert.C0) i
            have h6 := matVec_vecZero cert.C0 i
            simp only [vecScale] at h1
            rw [← h3, ← h1, h2, h4, h5, h6]; rfl
        rcases Int.mul_eq_zero.mp hstep with hb | hz
        · exact absurd hb cert.beta_ne
        · exact hz
  intro n
  have hmul : cert.alpha * evalRep R n = 0 := by
    rw [evalRep, ← dot_vecScale_left, dot_congr cert.cover (fun _ => rfl),
        ← dot_matVec_eq_dot_matT, dot_congr (fun _ => rfl) (hinv n), dot_vecZero_right]
  rcases Int.mul_eq_zero.mp hmul with ha | hz
  · exact absurd ha cert.alpha_ne
  · exact hz

/-- Engine 2: Matrix-Commutation / Bisimulation Intertwining Certificate.
    A finite matrix `T : Mat d2 d1` intertwining `(R1, R2)` proves `∀ n, evalRep R1 n = evalRep R2 n`. -/
structure IntertwineCert {d1 d2 : Nat} (R1 : LinRep d1) (R2 : LinRep d2) where
  T     : Mat d2 d1
  base  : VecEq (matVec T R1.v) R2.v
  comm0 : MatEq (matMul T R1.M0) (matMul R2.M0 T)
  comm1 : MatEq (matMul T R1.M1) (matMul R2.M1 T)
  obs   : VecEq (matVec (matT T) R2.u) R1.u

theorem IntertwineCert.sound {d1 d2 : Nat} {R1 : LinRep d1} {R2 : LinRep d2}
    (cert : IntertwineCert R1 R2) : ∀ n : Nat, evalRep R1 n = evalRep R2 n := by
  have hstate : ∀ n : Nat, VecEq (matVec cert.T (evalVec R1 n)) (evalVec R2 n) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      unfold evalVec
      split
      · exact cert.base
      · rename_i hne
        have hq := ih (n / 2) (by omega)
        intro i
        split
        · have h1 := matVec_matMul cert.T R1.M1 (evalVec R1 (n / 2)) i
          have h2 := matVec_congr cert.comm1 (fun _ => rfl) (x := evalVec R1 (n / 2)) i
          have h3 := matVec_matMul R2.M1 cert.T (evalVec R1 (n / 2)) i
          have h4 := matVec_congr (fun _ _ => rfl) hq (A := R2.M1) i
          rw [← h1, h2, h3, h4]
        · have h1 := matVec_matMul cert.T R1.M0 (evalVec R1 (n / 2)) i
          have h2 := matVec_congr cert.comm0 (fun _ => rfl) (x := evalVec R1 (n / 2)) i
          have h3 := matVec_matMul R2.M0 cert.T (evalVec R1 (n / 2)) i
          have h4 := matVec_congr (fun _ _ => rfl) hq (A := R2.M0) i
          rw [← h1, h2, h3, h4]
  intro n
  rw [evalRep, evalRep, ← dot_congr cert.obs (fun _ => rfl),
      ← dot_matVec_eq_dot_matT, dot_congr (fun _ => rfl) (hstate n)]

/-- Engine 3: Modular Invariant-Subspace Divisibility Certificate.
    A finite modular certificate `(K, C0, C1, c)` proves `∀ n, m ∣ evalRep R n`. -/
structure ModCert {d : Nat} (R : LinRep d) (r : Nat) (m : Int) where
  K     : Mat r d
  C0    : Mat r r
  C1    : Mat r r
  c     : Vec r
  m_pos : 0 < m
  base  : VecModZero m (matVec K R.v)
  step0 : MatModEq m (matMul K R.M0) (matMul C0 K)
  step1 : MatModEq m (matMul K R.M1) (matMul C1 K)
  cover : VecModEq m R.u (matVec (matT K) c)

theorem ModCert.sound {d r : Nat} {m : Int} {R : LinRep d} (cert : ModCert R r m) :
    ∀ n : Nat, m ∣ evalRep R n := by
  have hinv : ∀ n : Nat, ∀ i : Fin r, m ∣ matVec cert.K (evalVec R n) i := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      unfold evalVec
      split
      · intro i; exact dvd_of_emod_eq_zero (cert.base i)
      · rename_i hne
        have hq := ih (n / 2) (by omega)
        intro i
        split
        · have hdiff : m ∣ (matVec (matMul cert.K R.M1) (evalVec R (n / 2)) i -
                            matVec (matMul cert.C1 cert.K) (evalVec R (n / 2)) i) := by
            simp only [matVec]
            rw [← sumFin_sub]
            apply sumFin_dvd; intro j
            rw [← Int.sub_mul]
            exact Int.dvd_mul_of_dvd_left (dvd_of_emod_eq_zero (cert.step1 i j))
          have hrhs : m ∣ matVec (matMul cert.C1 cert.K) (evalVec R (n / 2)) i := by
            rw [matVec_matMul]
            exact vecDvd_matVec cert.C1 hq i
          have hlhs : m ∣ matVec (matMul cert.K R.M1) (evalVec R (n / 2)) i := by
            have heq : matVec (matMul cert.K R.M1) (evalVec R (n / 2)) i =
              (matVec (matMul cert.K R.M1) (evalVec R (n / 2)) i -
               matVec (matMul cert.C1 cert.K) (evalVec R (n / 2)) i) +
               matVec (matMul cert.C1 cert.K) (evalVec R (n / 2)) i := by omega
            rw [heq]; exact Int.dvd_add hdiff hrhs
          rwa [matVec_matMul] at hlhs
        · have hdiff : m ∣ (matVec (matMul cert.K R.M0) (evalVec R (n / 2)) i -
                            matVec (matMul cert.C0 cert.K) (evalVec R (n / 2)) i) := by
            simp only [matVec]
            rw [← sumFin_sub]
            apply sumFin_dvd; intro j
            rw [← Int.sub_mul]
            exact Int.dvd_mul_of_dvd_left (dvd_of_emod_eq_zero (cert.step0 i j))
          have hrhs : m ∣ matVec (matMul cert.C0 cert.K) (evalVec R (n / 2)) i := by
            rw [matVec_matMul]
            exact vecDvd_matVec cert.C0 hq i
          have hlhs : m ∣ matVec (matMul cert.K R.M0) (evalVec R (n / 2)) i := by
            have heq : matVec (matMul cert.K R.M0) (evalVec R (n / 2)) i =
              (matVec (matMul cert.K R.M0) (evalVec R (n / 2)) i -
               matVec (matMul cert.C0 cert.K) (evalVec R (n / 2)) i) +
               matVec (matMul cert.C0 cert.K) (evalVec R (n / 2)) i := by omega
            rw [heq]; exact Int.dvd_add hdiff hrhs
          rwa [matVec_matMul] at hlhs
  intro n
  have hdiff : m ∣ (dot R.u (evalVec R n) - dot (matVec (matT cert.K) cert.c) (evalVec R n)) := by
    simp only [dot]
    rw [← sumFin_sub]
    apply sumFin_dvd; intro i
    rw [← Int.sub_mul]
    exact Int.dvd_mul_of_dvd_left (dvd_of_emod_eq_zero (cert.cover i))
  have hrhs : m ∣ dot (matVec (matT cert.K) cert.c) (evalVec R n) := by
    rw [← dot_matVec_eq_dot_matT]
    exact dot_dvd_right cert.c (hinv n)
  have heq : evalRep R n =
      (dot R.u (evalVec R n) - dot (matVec (matT cert.K) cert.c) (evalVec R n)) +
       dot (matVec (matT cert.K) cert.c) (evalVec R n) := by
    simp [evalRep]
  rw [heq]
  exact Int.dvd_add hdiff hrhs

/-- Helper: if `0 < a` and `0 ≤ a * b`, then `0 ≤ b`. -/
theorem nonneg_of_mul_nonneg_left {a b : Int} (ha : 0 < a) (hab : 0 ≤ a * b) : 0 ≤ b := by
  by_cases hb : 0 ≤ b
  · exact hb
  · have hneg : b ≤ -1 := by omega
    have hmul : a * b ≤ a * (-1) := Int.mul_le_mul_of_nonneg_left hneg (by omega)
    omega

/-- Engine 4a: Polyhedral Invariant-Cone Inequality Certificate (for all `n : Nat`).
    A finite integer cone `(P, C0, C1, c, alpha, beta)` with `C0, C1, c ≥ 0` and `alpha, beta > 0`
    proves `∀ n, 0 ≤ evalRep R n`. -/
structure ConeCert {d : Nat} (R : LinRep d) (r : Nat) where
  P         : Mat r d
  C0        : Mat r r
  C1        : Mat r r
  c         : Vec r
  alpha     : Int
  beta      : Int
  alpha_pos : 0 < alpha
  beta_pos  : 0 < beta
  C0_nn     : MatNonneg C0
  C1_nn     : MatNonneg C1
  c_nn      : VecNonneg c
  base      : VecNonneg (matVec P R.v)
  step0     : MatEq (matScale beta (matMul P R.M0)) (matMul C0 P)
  step1     : MatEq (matScale beta (matMul P R.M1)) (matMul C1 P)
  cover     : VecEq (vecScale alpha R.u) (matVec (matT P) c)

theorem ConeCert.sound {d r : Nat} {R : LinRep d} (cert : ConeCert R r) :
    ∀ n : Nat, 0 ≤ evalRep R n := by
  have hinv : ∀ n : Nat, VecNonneg (matVec cert.P (evalVec R n)) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      unfold evalVec
      split
      · exact cert.base
      · rename_i hne
        have hq := ih (n / 2) (by omega)
        intro i
        apply nonneg_of_mul_nonneg_left cert.beta_pos
        split
        · have h1 := matVec_matScale cert.beta (matMul cert.P R.M1) (evalVec R (n / 2)) i
          have h2 := matVec_congr cert.step1 (fun _ => rfl) (x := evalVec R (n / 2)) i
          have h3 := matVec_matMul cert.P R.M1 (evalVec R (n / 2)) i
          have h4 := matVec_matMul cert.C1 cert.P (evalVec R (n / 2)) i
          simp only [vecScale] at h1
          rw [← h3, ← h1, h2, h4]
          exact vecNonneg_matVec cert.C1_nn hq i
        · have h1 := matVec_matScale cert.beta (matMul cert.P R.M0) (evalVec R (n / 2)) i
          have h2 := matVec_congr cert.step0 (fun _ => rfl) (x := evalVec R (n / 2)) i
          have h3 := matVec_matMul cert.P R.M0 (evalVec R (n / 2)) i
          have h4 := matVec_matMul cert.C0 cert.P (evalVec R (n / 2)) i
          simp only [vecScale] at h1
          rw [← h3, ← h1, h2, h4]
          exact vecNonneg_matVec cert.C0_nn hq i
  intro n
  apply nonneg_of_mul_nonneg_left cert.alpha_pos
  rw [evalRep, ← dot_vecScale_left, dot_congr cert.cover (fun _ => rfl), ← dot_matVec_eq_dot_matT]
  exact dot_nonneg cert.c_nn (hinv n)

/-- Engine 4b: Positive-Domain Polyhedral Invariant-Cone Certificate (for all `n ≥ 1`).
    Replaces base check `P * v ≥ 0` with `P * (M1 * v) ≥ 0` (the MSB-1 entry point `n = 1`),
    proving `∀ n ≥ 1, 0 ≤ evalRep R n`. -/
structure ConePosCert {d : Nat} (R : LinRep d) (r : Nat) where
  P         : Mat r d
  C0        : Mat r r
  C1        : Mat r r
  c         : Vec r
  alpha     : Int
  beta      : Int
  alpha_pos : 0 < alpha
  beta_pos  : 0 < beta
  C0_nn     : MatNonneg C0
  C1_nn     : MatNonneg C1
  c_nn      : VecNonneg c
  base1     : VecNonneg (matVec P (matVec R.M1 R.v))
  step0     : MatEq (matScale beta (matMul P R.M0)) (matMul C0 P)
  step1     : MatEq (matScale beta (matMul P R.M1)) (matMul C1 P)
  cover     : VecEq (vecScale alpha R.u) (matVec (matT P) c)

theorem ConePosCert.sound {d r : Nat} {R : LinRep d} (cert : ConePosCert R r) :
    ∀ n : Nat, 1 ≤ n → 0 ≤ evalRep R n := by
  have hinv : ∀ n : Nat, 1 ≤ n → VecNonneg (matVec cert.P (evalVec R n)) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases h1 : n = 1
      · subst h1; rw [evalVec_one]; exact cert.base1
      · have hq_pos : 1 ≤ n / 2 := by omega
        have hq := ih (n / 2) (by omega) hq_pos
        have hne : n ≠ 0 := by omega
        unfold evalVec
        simp only [hne, ↓reduceDIte]
        intro i
        apply nonneg_of_mul_nonneg_left cert.beta_pos
        split
        · have hs1 := matVec_matScale cert.beta (matMul cert.P R.M1) (evalVec R (n / 2)) i
          have hs2 := matVec_congr cert.step1 (fun _ => rfl) (x := evalVec R (n / 2)) i
          have hs3 := matVec_matMul cert.P R.M1 (evalVec R (n / 2)) i
          have hs4 := matVec_matMul cert.C1 cert.P (evalVec R (n / 2)) i
          simp only [vecScale] at hs1
          rw [← hs3, ← hs1, hs2, hs4]
          exact vecNonneg_matVec cert.C1_nn hq i
        · have hs1 := matVec_matScale cert.beta (matMul cert.P R.M0) (evalVec R (n / 2)) i
          have hs2 := matVec_congr cert.step0 (fun _ => rfl) (x := evalVec R (n / 2)) i
          have hs3 := matVec_matMul cert.P R.M0 (evalVec R (n / 2)) i
          have hs4 := matVec_matMul cert.C0 cert.P (evalVec R (n / 2)) i
          simp only [vecScale] at hs1
          rw [← hs3, ← hs1, hs2, hs4]
          exact vecNonneg_matVec cert.C0_nn hq i
  intro n hn
  apply nonneg_of_mul_nonneg_left cert.alpha_pos
  rw [evalRep, ← dot_vecScale_left, dot_congr cert.cover (fun _ => rfl), ← dot_matVec_eq_dot_matT]
  exact dot_nonneg cert.c_nn (hinv n hn)

/-- Soundness compiler: any pure-data certificate accepted by `checkConePosCert`
    yields an infinite theorem `∀ n ≥ 1, 0 ≤ evalRep R n`. -/
theorem checkConePosCert_sound {d r : Nat} (R : LinRep d) (D : ConePosCertData d r)
    (h : checkConePosCert R D = true) : ∀ n : Nat, 1 ≤ n → 0 ≤ evalRep R n := by
  unfold checkConePosCert at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hC0⟩, hC1⟩, hc⟩, hbase⟩, hs0⟩, hs1⟩, hcov⟩
  exact ({
    P := D.P, C0 := D.C0, C1 := D.C1, c := D.c, alpha := D.alpha, beta := D.beta,
    alpha_pos := ha, beta_pos := hb, C0_nn := hC0, C1_nn := hC1, c_nn := hc,
    base1 := hbase, step0 := hs0, step1 := hs1, cover := hcov
  } : ConePosCert R r).sound

/-- Pure-data modular invariant-subspace certificate (zero `Prop` fields). -/
structure ModCertData (d r : Nat) where
  K  : Mat r d
  C0 : Mat r r
  C1 : Mat r r
  c  : Vec r
  m  : Int

/-- Executable Boolean verifier for `ModCertData`. -/
def checkModCert {d r : Nat} (R : LinRep d) (D : ModCertData d r) : Bool :=
  decide (0 < D.m) &&
  decide (VecModZero D.m (matVec D.K R.v)) &&
  decide (MatModEq D.m (matMul D.K R.M0) (matMul D.C0 D.K)) &&
  decide (MatModEq D.m (matMul D.K R.M1) (matMul D.C1 D.K)) &&
  decide (VecModEq D.m R.u (matVec (matT D.K) D.c))

/-- Soundness compiler: any pure-data certificate accepted by `checkModCert`
    yields an infinite divisibility theorem `∀ n, D.m ∣ evalRep R n`. -/
theorem checkModCert_sound {d r : Nat} (R : LinRep d) (D : ModCertData d r)
    (h : checkModCert R D = true) : ∀ n : Nat, D.m ∣ evalRep R n := by
  unfold checkModCert at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨hm, hbase⟩, hs0⟩, hs1⟩, hcov⟩
  exact ({
    K := D.K, C0 := D.C0, C1 := D.C1, c := D.c, m_pos := hm,
    base := hbase, step0 := hs0, step1 := hs1, cover := hcov
  } : ModCert R r D.m).sound

-- Bit-level recurrence lemmas for native `gray`, `popcount`, `highBit`, `dq`
theorem testBit_two_mul_add_bit (x b : Nat) (hb : b < 2) (i : Nat) :
    (2 * x + b).testBit i = match i with | 0 => (b == 1) | k + 1 => x.testBit k := by
  cases i with
  | zero =>
    simp only [Nat.testBit_zero]
    have hm : (2 * x + b) % 2 = b := by omega
    rw [hm]
    have : b = 0 ∨ b = 1 := by omega
    rcases this with rfl | rfl <;> rfl
  | succ k =>
    rw [Nat.testBit_succ]
    have hd : (2 * x + b) / 2 = x := by omega
    rw [hd]

theorem gray_two_mul (n : Nat) : gray (2 * n) = 2 * gray n + n % 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [gray, Nat.testBit_xor]
  have hd : 2 * n / 2 = n := by omega
  rw [hd]
  have h1 := testBit_two_mul_add_bit n 0 (by omega) i
  have h2 := testBit_two_mul_add_bit (n ^^^ (n / 2)) (n % 2) (by omega) i
  simp only [Nat.add_zero] at h1
  rw [h1, h2]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero]
    have : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases this with h | h <;> simp [h]
  | succ k =>
    simp [Nat.testBit_xor, Nat.testBit_succ]

theorem gray_two_mul_add_one (n : Nat) : gray (2 * n + 1) = 2 * gray n + (1 - n % 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [gray, Nat.testBit_xor]
  have hd : (2 * n + 1) / 2 = n := by omega
  rw [hd]
  have h1 := testBit_two_mul_add_bit n 1 (by omega) i
  have h2 := testBit_two_mul_add_bit (n ^^^ (n / 2)) (1 - n % 2) (by omega) i
  rw [h1, h2]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero]
    have : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases this with h | h <;> simp [h]
  | succ k =>
    simp [Nat.testBit_xor, Nat.testBit_succ]

theorem popcount_zero : popcount 0 = 0 := by unfold popcount; simp

theorem popcount_two_mul (n : Nat) : popcount (2 * n) = popcount n := by
  cases n with
  | zero => simp [popcount_zero]
  | succ k =>
    conv => lhs; unfold popcount
    have hne : 2 * (k + 1) ≠ 0 := by omega
    have hm : 2 * (k + 1) % 2 = 0 := by omega
    have hd : 2 * (k + 1) / 2 = k + 1 := by omega
    simp [hne, hm, hd]

theorem popcount_two_mul_add_one (n : Nat) : popcount (2 * n + 1) = 1 + popcount n := by
  conv => lhs; unfold popcount
  have hm : (2 * n + 1) % 2 = 1 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  simp [hm, hd]

theorem popcount_two_mul_add_bit (x b : Nat) (hb : b < 2) :
    popcount (2 * x + b) = b + popcount x := by
  have : b = 0 ∨ b = 1 := by omega
  rcases this with rfl | rfl
  · simpa using popcount_two_mul x
  · exact popcount_two_mul_add_one x

theorem highBit_zero : highBit 0 = 0 := by unfold highBit; simp
theorem highBit_one : highBit 1 = 1 := by unfold highBit; simp

theorem highBit_two_mul (n : Nat) : highBit (2 * n) = 2 * highBit n := by
  cases n with
  | zero => simp [highBit_zero]
  | succ k =>
    conv => lhs; unfold highBit
    have h0 : 2 * (k + 1) ≠ 0 := by omega
    have h1 : 2 * (k + 1) ≠ 1 := by omega
    have hd : 2 * (k + 1) / 2 = k + 1 := by omega
    simp [h0, h1, hd]

theorem highBit_two_mul_add_one (n : Nat) :
    highBit (2 * n + 1) = 2 * highBit n + (if n = 0 then 1 else 0) := by
  cases n with
  | zero => simp [highBit_zero, highBit_one]
  | succ k =>
    conv => lhs; unfold highBit
    have hd : (2 * (k + 1) + 1) / 2 = k + 1 := by omega
    simp [hd]

theorem dq_zero (q : Int) : dq q 0 = 0 := by unfold dq; simp

theorem dq_two_mul (q : Int) (n : Nat) : dq q (2 * n) = q * dq q n + ((n % 2 : Nat) : Int) := by
  cases n with
  | zero => simp [dq_zero]
  | succ k =>
    conv => lhs; unfold dq
    have h0 : 2 * (k + 1) ≠ 0 := by omega
    have hm : 2 * (k + 1) % 2 = 0 := by omega
    have hd : 2 * (k + 1) / 2 = k + 1 := by omega
    simp [h0, hm, hd]

theorem dq_two_mul_add_one (q : Int) (n : Nat) :
    dq q (2 * n + 1) = q * dq q n - ((n % 2 : Nat) : Int) := by
  conv => lhs; unfold dq
  have hm : (2 * n + 1) % 2 = 1 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  simp [hm, hd]
  omega

/-- Bridge 1: `dq 1 n = popcount(G(n)) - popcount(n)` for all `n`. -/
theorem dq_one_eq (n : Nat) : dq 1 n = (popcount (gray n) : Int) - (popcount n : Int) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [dq_zero, gray, popcount_zero]
    | succ k =>
      by_cases hmod : (k + 1) % 2 = 0
      · have h2 : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        rw [h2, dq_two_mul, ih ((k + 1) / 2) hlt, gray_two_mul,
            popcount_two_mul_add_bit _ _ (by omega), popcount_two_mul]
        omega
      · have h2 : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        rw [h2, dq_two_mul_add_one, ih ((k + 1) / 2) hlt, gray_two_mul_add_one,
            popcount_two_mul_add_bit _ _ (by omega), popcount_two_mul_add_one]
        have : ((k + 1) / 2) % 2 = 0 ∨ ((k + 1) / 2) % 2 = 1 := by omega
        rcases this with h | h <;> simp [h] <;> omega

/-- Bridge 2: `dq 2 n = G(n) - n` for all `n`. -/
theorem dq_two_eq (n : Nat) : dq 2 n = (gray n : Int) - (n : Int) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [dq_zero, gray]
    | succ k =>
      by_cases hmod : (k + 1) % 2 = 0
      · have h2 : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        rw [h2, dq_two_mul, ih ((k + 1) / 2) hlt, gray_two_mul]
        omega
      · have h2 : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        rw [h2, dq_two_mul_add_one, ih ((k + 1) / 2) hlt, gray_two_mul_add_one]
        have : ((k + 1) / 2) % 2 = 0 ∨ ((k + 1) / 2) % 2 = 1 := by omega
        rcases this with h | h <;> simp [h] <;> omega

theorem W_G_eq_S1 (n : Nat) : W_G n = S_q 1 n :=
  sumRange_congr (fun k => (dq_one_eq k).symm) n

theorem E_G_eq_S2 (n : Nat) : E_G n = S_q 2 n :=
  sumRange_congr (fun k => (dq_two_eq k).symm) n

theorem S_q_two_mul (q : Int) (n : Nat) : S_q q (2 * n) = 2 * q * S_q q n := by
  unfold S_q
  rw [sumRange_two_mul]
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    rw [sumRange, sumRange, ih, dq_two_mul, dq_two_mul_add_one]
    have hmul : 2 * q * (sumRange (dq q) k + dq q k) = 2 * q * sumRange (dq q) k + 2 * q * dq q k :=
      Int.mul_add _ _ _
    have h2 : 2 * q * dq q k = q * dq q k + q * dq q k := by
      rw [show (2 : Int) * q = q + q by omega, Int.add_mul]
    omega

theorem S_q_two_mul_add_one (q : Int) (n : Nat) :
    S_q q (2 * n + 1) = 2 * q * S_q q n + q * dq q n + ((n % 2 : Nat) : Int) := by
  unfold S_q
  rw [sumRange]
  have he := S_q_two_mul q n
  unfold S_q at he
  rw [he, dq_two_mul]
  omega

-- ============================================================================
-- Helper constructors for concrete small vectors & matrices (kernel-simp friendly)
-- ============================================================================

@[simp] def getIdx : List Int → Nat → Int
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: tl, n + 1 => getIdx tl n

@[simp] def getRow : List (List Int) → Nat → List Int
  | [], _ => []
  | r :: _, 0 => r
  | _ :: tl, n + 1 => getRow tl n

def mkVec {d : Nat} (l : List Int) : Vec d := fun i => getIdx l i.val
def mkMat {m n : Nat} (rows : List (List Int)) : Mat m n :=
  fun i j => getIdx (getRow rows i.val) j.val

-- ============================================================================
-- Concrete 2-Regular Linear Representations & Their Semantic Bridges
-- ============================================================================

/-- 4-dimensional parametric linear representation of `S_q(q, n)`:
    state(n) = [ S_q(q, n), d_q(q, n), n % 2, 1 ]. -/
def SqRep (q : Int) : LinRep 4 where
  u  := mkVec [1, 0, 0, 0]
  M0 := mkMat [
    [2 * q, 0, 0, 0],
    [    0, q, 1, 0],
    [    0, 0, 0, 0],
    [    0, 0, 0, 1]
  ]
  M1 := mkMat [
    [2 * q, q,  1, 0],
    [    0, q, -1, 0],
    [    0, 0,  0, 1],
    [    0, 0,  0, 1]
  ]
  v  := mkVec [0, 0, 0, 1]
  stable := by
    intro ⟨i, hi⟩
    match i with
    | 0 | 1 | 2 | 3 => simp [matVec, sumFin, mkMat, mkVec]
    | _ + 4 => omega

theorem evalVec_SqRep (q : Int) (n : Nat) :
    VecEq (evalVec (SqRep q) n) (mkVec [S_q q n, dq q n, ((n % 2 : Nat) : Int), 1]) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      intro ⟨i, hi⟩
      match i with
      | 0 | 1 | 2 | 3 => simp [evalVec_zero, SqRep, mkVec, S_q, sumRange, dq_zero]
      | _ + 4 => omega
    | succ k =>
      by_cases hmod : (k + 1) % 2 = 0
      · have h2 : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        have hq := ih ((k + 1) / 2) hlt
        rw [h2, evalVec_two_mul]
        intro ⟨i, hi⟩
        have hcong := matVec_congr (fun _ _ => rfl) hq (A := (SqRep q).M0) ⟨i, hi⟩
        rw [hcong]
        match i with
        | 0 => simp [SqRep, matVec, sumFin, mkMat, mkVec, S_q_two_mul]
        | 1 => simp [SqRep, matVec, sumFin, mkMat, mkVec, dq_two_mul]
        | 2 => simp [SqRep, matVec, sumFin, mkMat, mkVec]
        | 3 => simp [SqRep, matVec, sumFin, mkMat, mkVec]
        | _ + 4 => omega
      · have h2 : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        have hq := ih ((k + 1) / 2) hlt
        rw [h2, evalVec_two_mul_add_one]
        intro ⟨i, hi⟩
        have hcong := matVec_congr (fun _ _ => rfl) hq (A := (SqRep q).M1) ⟨i, hi⟩
        rw [hcong]
        match i with
        | 0 => simp [SqRep, matVec, sumFin, mkMat, mkVec, S_q_two_mul_add_one]
        | 1 => simp [SqRep, matVec, sumFin, mkMat, mkVec, dq_two_mul_add_one]; omega
        | 2 => simp [SqRep, matVec, sumFin, mkMat, mkVec]
        | 3 => simp [SqRep, matVec, sumFin, mkMat, mkVec]
        | _ + 4 => omega

theorem evalRep_SqRep (q : Int) (n : Nat) : evalRep (SqRep q) n = S_q q n := by
  rw [evalRep, dot_congr (fun _ => rfl) (evalVec_SqRep q n)]
  simp [SqRep, dot, sumFin, mkVec]

/-- 5-dimensional linear representation for Theorem 2:
    state(n) = [ W_G(n), d_1(n), n % 2, 1, n ],
    observing `2*n - 2 + (n % 2) - 5*W_G(n)`. -/
def WGUpperRep : LinRep 5 where
  u  := mkVec [-5, 0, 1, -2, 2]
  M0 := mkMat [
    [2, 0,  0, 0, 0],
    [0, 1,  1, 0, 0],
    [0, 0,  0, 0, 0],
    [0, 0,  0, 1, 0],
    [0, 0,  0, 0, 2]
  ]
  M1 := mkMat [
    [2, 1,  1, 0, 0],
    [0, 1, -1, 0, 0],
    [0, 0,  0, 1, 0],
    [0, 0,  0, 1, 0],
    [0, 0,  0, 1, 2]
  ]
  v  := mkVec [0, 0, 0, 1, 0]
  stable := by decide

theorem evalVec_WGUpperRep (n : Nat) :
    VecEq (evalVec WGUpperRep n) (mkVec [W_G n, dq 1 n, ((n % 2 : Nat) : Int), 1, (n : Int)]) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      intro ⟨i, hi⟩
      match i with
      | 0 | 1 | 2 | 3 | 4 => simp [evalVec_zero, WGUpperRep, mkVec, W_G, sumRange, dq_zero]
      | _ + 5 => omega
    | succ k =>
      by_cases hmod : (k + 1) % 2 = 0
      · have h2 : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        have hq := ih ((k + 1) / 2) hlt
        rw [h2, evalVec_two_mul]
        intro ⟨i, hi⟩
        rw [matVec_congr (fun _ _ => rfl) hq (A := WGUpperRep.M0) ⟨i, hi⟩]
        match i with
        | 0 => simp [WGUpperRep, matVec, sumFin, mkMat, mkVec, W_G_eq_S1, S_q_two_mul]
        | 1 => simp [WGUpperRep, matVec, sumFin, mkMat, mkVec, dq_two_mul]
        | 2 => simp [WGUpperRep, matVec, sumFin, mkMat, mkVec]
        | 3 => simp [WGUpperRep, matVec, sumFin, mkMat, mkVec]
        | 4 => simp [WGUpperRep, matVec, sumFin, mkMat, mkVec]
        | _ + 5 => omega
      · have h2 : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        have hlt : (k + 1) / 2 < k + 1 := by omega
        have hq := ih ((k + 1) / 2) hlt
        rw [h2, evalVec_two_mul_add_one]
        intro ⟨i, hi⟩
        rw [matVec_congr (fun _ _ => rfl) hq (A := WGUpperRep.M1) ⟨i, hi⟩]
        match i with
        | 0 => simp [WGUpperRep, matVec, sumFin, mkMat, mkVec, W_G_eq_S1, S_q_two_mul_add_one]
        | 1 => simp [WGUpperRep, matVec, sumFin, mkMat, mkVec, dq_two_mul_add_one]; omega
        | 2 => simp [WGUpperRep, matVec, sumFin, mkMat, mkVec]
        | 3 => simp [WGUpperRep, matVec, sumFin, mkMat, mkVec]
        | 4 => simp [WGUpperRep, matVec, sumFin, mkMat, mkVec]; omega
        | _ + 5 => omega

theorem evalRep_WGUpperRep (n : Nat) :
    evalRep WGUpperRep n = 2 * (n : Int) - 2 + ((n % 2 : Nat) : Int) - 5 * W_G n := by
  rw [evalRep, dot_congr (fun _ => rfl) (evalVec_WGUpperRep n)]
  simp [WGUpperRep, dot, sumFin, mkVec]
  omega

/-- 3-dimensional linear representation of `L(n) = n - highBit(n)`:
    state(n) = [ n - highBit(n), [n == 0], 1 ]. -/
def LRep : LinRep 3 where
  u  := mkVec [1, 0, 0]
  M0 := mkMat [[2, 0, 0], [0, 1, 0], [0, 0, 1]]
  M1 := mkMat [[2, -1, 1], [0, 0, 0], [0, 0, 1]]
  v  := mkVec [0, 1, 1]
  stable := by decide

/-- 3-dimensional linear representation of `R(n) = 2 * highBit(n) - n`:
    state(n) = [ 2 * highBit(n) - n, [n == 0], 1 ]. -/
def RRep : LinRep 3 where
  u  := mkVec [1, 0, 0]
  M0 := mkMat [[2, 0, 0], [0, 1, 0], [0, 0, 1]]
  M1 := mkMat [[2, 2, -1], [0, 0, 0], [0, 0, 1]]
  v  := mkVec [0, 1, 1]
  stable := by decide

/-- 5-dimensional minimal linear representation of `Q_dyadic(n) = L(n) * R(n)`:
    state(n) = [ Q(n), L(n), R(n), [n == 0], 1 ]. -/
def QRep : LinRep 5 where
  u  := mkVec [1, 0, 0, 0, 0]
  M0 := mkMat [
    [4,  0, 0, 0,  0],
    [0,  2, 0, 0,  0],
    [0,  0, 2, 0,  0],
    [0,  0, 0, 1,  0],
    [0,  0, 0, 0,  1]
  ]
  M1 := mkMat [
    [4, -2, 2,  1, -1],
    [0,  2, 0, -1,  1],
    [0,  0, 2,  2, -1],
    [0,  0, 0,  0,  0],
    [0,  0, 0,  0,  1]
  ]
  v  := mkVec [0, 0, 0, 1, 1]
  stable := by decide

theorem evalVec_LRep (n : Nat) :
    VecEq (evalVec LRep n) (mkVec [(n : Int) - (highBit n : Int), if n = 0 then 1 else 0, 1]) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      intro ⟨i, hi⟩
      match i with
      | 0 | 1 | 2 => simp [evalVec_zero, LRep, mkVec, highBit_zero]
      | _ + 3 => omega
    | succ k =>
      by_cases hmod : (k + 1) % 2 = 0
      · have h2 : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hq := ih ((k + 1) / 2) (by omega)
        have hqne : (k + 1) / 2 ≠ 0 := by omega
        rw [h2, evalVec_two_mul]
        intro ⟨i, hi⟩
        rw [matVec_congr (fun _ _ => rfl) hq (A := LRep.M0) ⟨i, hi⟩]
        match i with
        | 0 => simp [LRep, matVec, sumFin, mkMat, mkVec, highBit_two_mul]; omega
        | 1 => simp [LRep, matVec, sumFin, mkMat, mkVec, hqne]; omega
        | 2 => simp [LRep, matVec, sumFin, mkMat, mkVec]
        | _ + 3 => omega
      · have h2 : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        have hq := ih ((k + 1) / 2) (by omega)
        rw [h2, evalVec_two_mul_add_one]
        intro ⟨i, hi⟩
        rw [matVec_congr (fun _ _ => rfl) hq (A := LRep.M1) ⟨i, hi⟩]
        match i with
        | 0 => simp [LRep, matVec, sumFin, mkMat, mkVec, highBit_two_mul_add_one]; split <;> omega
        | 1 => simp [LRep, matVec, sumFin, mkMat, mkVec]
        | 2 => simp [LRep, matVec, sumFin, mkMat, mkVec]
        | _ + 3 => omega

theorem evalVec_RRep (n : Nat) :
    VecEq (evalVec RRep n) (mkVec [2 * (highBit n : Int) - (n : Int), if n = 0 then 1 else 0, 1]) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      intro ⟨i, hi⟩
      match i with
      | 0 | 1 | 2 => simp [evalVec_zero, RRep, mkVec, highBit_zero]
      | _ + 3 => omega
    | succ k =>
      by_cases hmod : (k + 1) % 2 = 0
      · have h2 : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hq := ih ((k + 1) / 2) (by omega)
        have hqne : (k + 1) / 2 ≠ 0 := by omega
        rw [h2, evalVec_two_mul]
        intro ⟨i, hi⟩
        rw [matVec_congr (fun _ _ => rfl) hq (A := RRep.M0) ⟨i, hi⟩]
        match i with
        | 0 => simp [RRep, matVec, sumFin, mkMat, mkVec, highBit_two_mul]; omega
        | 1 => simp [RRep, matVec, sumFin, mkMat, mkVec, hqne]; omega
        | 2 => simp [RRep, matVec, sumFin, mkMat, mkVec]
        | _ + 3 => omega
      · have h2 : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        have hq := ih ((k + 1) / 2) (by omega)
        rw [h2, evalVec_two_mul_add_one]
        intro ⟨i, hi⟩
        rw [matVec_congr (fun _ _ => rfl) hq (A := RRep.M1) ⟨i, hi⟩]
        match i with
        | 0 => simp [RRep, matVec, sumFin, mkMat, mkVec, highBit_two_mul_add_one]; split <;> omega
        | 1 => simp [RRep, matVec, sumFin, mkMat, mkVec]
        | 2 => simp [RRep, matVec, sumFin, mkMat, mkVec]
        | _ + 3 => omega

theorem evalRep_LRep (n : Nat) : evalRep LRep n = (n : Int) - (highBit n : Int) := by
  rw [evalRep, dot_congr (fun _ => rfl) (evalVec_LRep n)]
  simp [LRep, dot, sumFin, mkVec]

theorem evalRep_RRep (n : Nat) : evalRep RRep n = 2 * (highBit n : Int) - (n : Int) := by
  rw [evalRep, dot_congr (fun _ => rfl) (evalVec_RRep n)]
  simp [RRep, dot, sumFin, mkVec]

/-- Engine 2 (`IntertwineCert`) + `LinRep.mul` (Kronecker product) proves
    `QRep` (dim 5) is identically equal to `LRep ⊗ RRep` (dim 9) for ALL `n : Nat`! -/
def Q_kron_intertwine : IntertwineCert QRep (LinRep.mul LRep RRep) where
  T := mkMat [
    [1, 0, 0, 0, 0], -- L*R = Q
    [0, 0, 0, 0, 0], -- z*R = 0
    [0, 0, 1, 0, 0], -- 1*R = R
    [0, 0, 0, 0, 0], -- L*z = 0
    [0, 0, 0, 1, 0], -- z*z = z
    [0, 0, 0, 1, 0], -- 1*z = z
    [0, 1, 0, 0, 0], -- L*1 = L
    [0, 0, 0, 1, 0], -- z*1 = z
    [0, 0, 0, 0, 1]  -- 1*1 = 1
  ]
  base  := by decide
  comm0 := by decide
  comm1 := by decide
  obs   := by decide

theorem evalRep_QRep (n : Nat) : evalRep QRep n = Q_dyadic n := by
  rw [Q_kron_intertwine.sound n, evalRep_mul, evalRep_LRep, evalRep_RRep, Q_dyadic]

/-- 3-dimensional linear representation of the odd-filtered Thue-Morse parity indicator
    `a(n) = (n % 2) * (1 - popcount(n) % 2)`. -/
def OddEvenPopRep : LinRep 3 where
  u  := mkVec [1, 0, 0]
  M0 := mkMat [[0, 0, 0], [0, 1, 0], [0, 0, 1]]
  M1 := mkMat [[0, 0, 1], [0, 0, 1], [0, 1, 0]]
  v  := mkVec [0, 1, 0]
  stable := by decide

theorem evalVec_OddEvenPopRep (n : Nat) :
    VecEq (evalVec OddEvenPopRep n)
      (mkVec [((n % 2 : Nat) : Int) * (1 - ((popcount n % 2 : Nat) : Int)),
              1 - ((popcount n % 2 : Nat) : Int),
              ((popcount n % 2 : Nat) : Int)]) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      intro ⟨i, hi⟩
      match i with
      | 0 | 1 | 2 => simp [evalVec_zero, OddEvenPopRep, mkVec, popcount_zero]
      | _ + 3 => omega
    | succ k =>
      by_cases hmod : (k + 1) % 2 = 0
      · have h2 : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hq := ih ((k + 1) / 2) (by omega)
        rw [h2, evalVec_two_mul]
        intro ⟨i, hi⟩
        rw [matVec_congr (fun _ _ => rfl) hq (A := OddEvenPopRep.M0) ⟨i, hi⟩]
        match i with
        | 0 | 1 | 2 => simp [OddEvenPopRep, matVec, sumFin, mkMat, mkVec, popcount_two_mul]
        | _ + 3 => omega
      · have h2 : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        have hq := ih ((k + 1) / 2) (by omega)
        rw [h2, evalVec_two_mul_add_one]
        intro ⟨i, hi⟩
        rw [matVec_congr (fun _ _ => rfl) hq (A := OddEvenPopRep.M1) ⟨i, hi⟩]
        match i with
        | 0 | 1 | 2 =>
          simp [OddEvenPopRep, matVec, sumFin, mkMat, mkVec, popcount_two_mul_add_one]
          omega
        | _ + 3 => omega

theorem evalRep_OddEvenPopRep (n : Nat) :
    evalRep OddEvenPopRep n = ((n % 2 : Nat) : Int) * (1 - ((popcount n % 2 : Nat) : Int)) := by
  rw [evalRep, dot_congr (fun _ => rfl) (evalVec_OddEvenPopRep n)]
  simp [OddEvenPopRep, dot, sumFin, mkVec]

/-- 4-dimensional linear representation of `r4(n) = (n % 2) * ((n / 2) % 4)`. -/
def Mod4RefRep : LinRep 4 where
  u  := mkVec [1, 0, 0, 0]
  M0 := mkMat [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1]]
  M1 := mkMat [[0, 1, 2, 0], [0, 0, 0, 1], [0, 1, 0, 0], [0, 0, 0, 1]]
  v  := mkVec [0, 0, 0, 1]
  stable := by decide

theorem evalVec_Mod4RefRep (n : Nat) :
    VecEq (evalVec Mod4RefRep n)
      (mkVec [((n % 2 : Nat) : Int) * (((n / 2) % 4 : Nat) : Int),
              ((n % 2 : Nat) : Int),
              (((n / 2) % 2 : Nat) : Int),
              1]) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      intro ⟨i, hi⟩
      match i with
      | 0 | 1 | 2 | 3 => simp [evalVec_zero, Mod4RefRep, mkVec]
      | _ + 4 => omega
    | succ k =>
      by_cases hmod : (k + 1) % 2 = 0
      · have h2 : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hq := ih ((k + 1) / 2) (by omega)
        rw [h2, evalVec_two_mul]
        intro ⟨i, hi⟩
        rw [matVec_congr (fun _ _ => rfl) hq (A := Mod4RefRep.M0) ⟨i, hi⟩]
        match i with
        | 0 | 1 | 2 | 3 => simp [Mod4RefRep, matVec, sumFin, mkMat, mkVec]
        | _ + 4 => omega
      · have h2 : k + 1 = 2 * ((k + 1) / 2) + 1 := by omega
        have hq := ih ((k + 1) / 2) (by omega)
        rw [h2, evalVec_two_mul_add_one]
        intro ⟨i, hi⟩
        rw [matVec_congr (fun _ _ => rfl) hq (A := Mod4RefRep.M1) ⟨i, hi⟩]
        match i with
        | 0 => simp [Mod4RefRep, matVec, sumFin, mkMat, mkVec]; omega
        | 1 => simp [Mod4RefRep, matVec, sumFin, mkMat, mkVec]
        | 2 => simp [Mod4RefRep, matVec, sumFin, mkMat, mkVec]; omega
        | 3 => simp [Mod4RefRep, matVec, sumFin, mkMat, mkVec]
        | _ + 4 => omega

theorem evalRep_Mod4RefRep (n : Nat) :
    evalRep Mod4RefRep n = ((n % 2 : Nat) : Int) * (((n / 2) % 4 : Nat) : Int) := by
  rw [evalRep, dot_congr (fun _ => rfl) (evalVec_Mod4RefRep n)]
  simp [Mod4RefRep, dot, sumFin, mkVec]

-- ============================================================================
-- Section 6: Five Novel Infinite Theorems Proved Through the Proof Engine
-- ============================================================================

-- ----------------------------------------------------------------------------
-- THEOREM 1: Parametric q-Gray-Defect Nonnegativity (∀ q ≥ 0, ∀ n, S_q(q, n) ≥ 0)
-- Proved symbolically via a 4-row parametric `ConeCert`!
-- ----------------------------------------------------------------------------

def Sq_nonneg_cert (q : Int) (hq : 0 ≤ q) : ConeCert (SqRep q) 4 where
  P := mkMat [
    [1, 0, 0, 0], -- g0 = S_q(q, n)
    [1, 1, 0, 0], -- g1 = S_q(q, n) + d_q(q, n)
    [0, 0, 1, 0], -- g2 = n % 2
    [0, 0, 0, 1]  -- g3 = 1
  ]
  C0 := mkMat [
    [2 * q, 0, 0, 0],
    [    q, q, 1, 0],
    [    0, 0, 0, 0],
    [    0, 0, 0, 1]
  ]
  C1 := mkMat [
    [q,     q, 1, 0],
    [0, 2 * q, 0, 0],
    [0,     0, 0, 1],
    [0,     0, 0, 1]
  ]
  c := mkVec [1, 0, 0, 0]
  alpha := 1
  beta := 1
  alpha_pos := by omega
  beta_pos := by omega
  C0_nn := by
    intro ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3
    | 1, 0 | 1, 1 | 1, 2 | 1, 3
    | 2, 0 | 2, 1 | 2, 2 | 2, 3
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 => simp [mkMat]; try omega
    | _ + 4, _ | _, _ + 4 => omega
  C1_nn := by
    intro ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3
    | 1, 0 | 1, 1 | 1, 2 | 1, 3
    | 2, 0 | 2, 1 | 2, 2 | 2, 3
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 => simp [mkMat]; try omega
    | _ + 4, _ | _, _ + 4 => omega
  c_nn  := by decide
  base  := by
    intro ⟨i, hi⟩
    match i with
    | 0 | 1 | 2 | 3 => simp [SqRep, matVec, sumFin, mkMat, mkVec]
    | _ + 4 => omega
  step0 := by
    intro ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3
    | 1, 0 | 1, 1 | 1, 2 | 1, 3
    | 2, 0 | 2, 1 | 2, 2 | 2, 3
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 => simp [SqRep, matScale, matMul, sumFin, mkMat]; try omega
    | _ + 4, _ | _, _ + 4 => omega
  step1 := by
    intro ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3
    | 1, 0 | 1, 1 | 1, 2 | 1, 3
    | 2, 0 | 2, 1 | 2, 2 | 2, 3
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 => simp [SqRep, matScale, matMul, sumFin, mkMat]; try omega
    | _ + 4, _ | _, _ + 4 => omega
  cover := by
    intro ⟨i, hi⟩
    match i with
    | 0 | 1 | 2 | 3 => simp [SqRep, vecScale, matVec, matT, sumFin, mkMat, mkVec]
    | _ + 4 => omega

/-- Theorem 1: For every nonnegative integer weight `q ≥ 0` and every `n : Nat`,
    the cumulative base-`q` Gray-defect `S_q(q, n)` is nonnegative. -/
theorem gray_defect_nonneg_all_q (q : Int) (hq : 0 ≤ q) (n : Nat) : 0 ≤ S_q q n := by
  rw [← evalRep_SqRep q n]
  exact (Sq_nonneg_cert q hq).sound n

theorem W_G_nonneg (n : Nat) : 0 ≤ W_G n := by
  rw [W_G_eq_S1]; exact gray_defect_nonneg_all_q 1 (by omega) n

theorem E_G_nonneg (n : Nat) : 0 ≤ E_G n := by
  rw [E_G_eq_S2]; exact gray_defect_nonneg_all_q 2 (by omega) n

-- ----------------------------------------------------------------------------
-- THEOREM 2: Sharp 2/5 Parity Envelope for Gray Switching-Weight Excess
--   ∀ n ≥ 1, 5 * W_G(n) ≤ 2*n - 2 + (n % 2)
-- Proved via a 6-row, α = 1, β = 2 `ConePosCert` discharged by `decide`!
-- ----------------------------------------------------------------------------

def WG_upper_cone_cert : ConePosCert WGUpperRep 6 where
  P := mkMat [
    [ 0,  0,  1,  0, 0], -- p
    [ 0,  0, -1,  1, 0], -- 1 - p
    [-5, -5, -1,  1, 2], -- 2n - 5W - 5d - p + 1
    [-5, -3, -1, -1, 2], -- 2n - 5W - 3d - p - 1
    [-5, -1,  0, -2, 2], -- 2n - 5W - d - 2
    [-5,  0,  1, -2, 2]  -- 2n - 5W + p - 2
  ]
  C0 := mkMat [
    [0, 0, 0, 0, 0, 0],
    [2, 2, 0, 0, 0, 0],
    [0, 7, 0, 3, 1, 0],
    [0, 5, 0, 1, 3, 0],
    [0, 4, 0, 0, 2, 2],
    [0, 4, 0, 0, 0, 4]
  ]
  C1 := mkMat [
    [2, 2, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0],
    [4, 0, 4, 0, 0, 0],
    [0, 0, 2, 2, 0, 0],
    [0, 4, 0, 4, 0, 0],
    [0, 7, 0, 3, 1, 0]
  ]
  c := mkVec [0, 0, 0, 0, 0, 1]
  alpha := 1
  beta := 2
  alpha_pos := by decide
  beta_pos  := by decide
  C0_nn     := by decide
  C1_nn     := by decide
  c_nn      := by decide
  base1     := by decide
  step0     := by decide
  step1     := by decide
  cover     := by decide

/-- Theorem 2: Sharp 2/5 parity-coupled upper bound on cumulative Gray switching-weight excess:
    for all `n ≥ 1`, `5 * W_G(n) ≤ 2*n - 2 + (n % 2)`. -/
theorem W_G_sharp_two_fifths_bound (n : Nat) (hn : 1 ≤ n) :
    5 * W_G n ≤ 2 * (n : Int) - 2 + ((n % 2 : Nat) : Int) := by
  have h := WG_upper_cone_cert.sound n hn
  rw [evalRep_WGUpperRep] at h
  omega

-- ----------------------------------------------------------------------------
-- THEOREM 3: Aperiodic Thue-Morse Parity Law for W_G(n) (mod 2)
--            and Exact Mod-4 Period-8 Law for E_G(n)
-- Proved via `ModCert` on `LinRep.sub` discharged by `decide`!
-- ----------------------------------------------------------------------------

def WG_mod2_cert : ModCert (LinRep.sub (SqRep 1) OddEvenPopRep) 3 2 where
  K := mkMat [
    [1, 0, 0, 0, -1,  0,  0], -- W - a
    [0, 1, 1, 0,  0,  0, -1], -- d + p - o_pop
    [0, 0, 0, 1,  0, -1, -1]  -- 1 - e_pop - o_pop
  ]
  C0 := mkMat [[0, 0, 0], [0, 1, 0], [0, 0, 1]]
  C1 := mkMat [[0, 1, 0], [0, 1, 1], [0, 0, 1]]
  c  := mkVec [1, 0, 0]
  m_pos := by decide
  base  := by decide
  step0 := by decide
  step1 := by decide
  cover := by decide

/-- Theorem 3a: Aperiodic Thue-Morse parity law for `W_G(n)`:
    `W_G(n)` is odd iff `n` is odd and has even Hamming weight. -/
theorem W_G_thue_morse_parity (n : Nat) :
    (2 : Int) ∣ (W_G n - ((n % 2 : Nat) : Int) * (1 - ((popcount n % 2 : Nat) : Int))) := by
  have h := WG_mod2_cert.sound n
  rw [evalRep_sub, evalRep_SqRep, ← W_G_eq_S1, evalRep_OddEvenPopRep] at h
  exact h

def EG_mod4_cert : ModCert (LinRep.sub (SqRep 2) Mod4RefRep) 4 4 where
  K := mkMat [
    [1, 0, 0, 0, -1,  0,  0,  0], -- E_G - r4
    [0, 2, 0, 0,  0,  0, -2,  0], -- 2 * (e - b1)
    [0, 0, 1, 0,  0, -1,  0,  0], -- p - b0
    [0, 0, 0, 1,  0,  0,  0, -1]  -- 1 - 1'
  ]
  C0 := mkMat [[0, 0, 0, 0], [0, 0, 2, 0], [0, 0, 0, 0], [0, 0, 0, 1]]
  C1 := mkMat [[0, 1, 1, 0], [0, 0, 2, 0], [0, 0, 0, 1], [0, 0, 0, 1]]
  c  := mkVec [1, 0, 0, 0]
  m_pos := by decide
  base  := by decide
  step0 := by decide
  step1 := by decide
  cover := by decide

/-- Theorem 3b: Exact mod-4 period-8 law for cumulative Gray value excess `E_G(n)`:
    `E_G(n) ≡ (n % 2) * ((n / 2) % 4) (mod 4)` for all `n : Nat`. -/
theorem E_G_mod4_law (n : Nat) :
    (4 : Int) ∣ (E_G n - ((n % 2 : Nat) : Int) * (((n / 2) % 4 : Nat) : Int)) := by
  have h := EG_mod4_cert.sound n
  rw [evalRep_sub, evalRep_SqRep, ← E_G_eq_S2, evalRep_Mod4RefRep] at h
  exact h

-- ----------------------------------------------------------------------------
-- THEOREM 4: Sharp Two-Sided Dyadic Parabolic Sandwich for E_G(n)
--   ∀ n, Q_dyadic(n) ≤ 2 * E_G(n) ∧ E_G(n) ≤ Q_dyadic(n)
-- Proved via two 4-row α = 1, β = 1 `ConePosCert`s on `LinRep.sub` discharged by `decide`!
-- ----------------------------------------------------------------------------

/-- `Q_dyadic(n) - E_G(n)` compiled via `LinRep.sub QRep (SqRep 2)` (dim 9):
    state = [ Q, L, R, z, 1,  E_G, e, p, 1' ]. -/
def Q_sub_EG_rep : LinRep 9 := LinRep.sub QRep (SqRep 2)

/-- `2 * E_G(n) - Q_dyadic(n)` compiled via `LinRep.sub (LinRep.scale 2 (SqRep 2)) QRep` (dim 9):
    state = [ E_G, e, p, 1,  Q, L, R, z, 1' ]. -/
def TwoEG_sub_Q_rep : LinRep 9 := LinRep.sub (LinRep.scale 2 (SqRep 2)) QRep

def EG_upper_sandwich_cert : ConePosCert Q_sub_EG_rep 6 where
  P := mkMat [
    [0,  0, 0, 0,  0,  0,  0,  1,  0], -- g0 = p
    [0,  0, 0, 0,  0,  0,  0, -1,  1], -- g1 = 1' - p
    [1,  0, 0, 0,  0, -1,  0,  0,  0], -- g2 = Q - E_G
    [1, -1, 1, 0, -1, -1, -1,  0,  0], -- g3 = Q - E_G + R - L - e - 1
    [0,  0, 0, 1,  0,  0,  0,  0,  0], -- g4 = z (= 0 for n ≥ 1)
    [0,  0, 0, 0,  1,  0,  0,  0, -1]  -- g5 = 1 - 1' (= 0)
  ]
  C0 := mkMat [
    [0, 0, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0],
    [0, 0, 4, 0, 0, 0],
    [0, 1, 2, 2, 0, 1],
    [0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 1]
  ]
  C1 := mkMat [
    [1, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0],
    [0, 1, 2, 2, 1, 1],
    [0, 0, 0, 4, 4, 0],
    [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1]
  ]
  c := mkVec [0, 0, 1, 0, 0, 0]
  alpha := 1
  beta := 1
  alpha_pos := by decide
  beta_pos  := by decide
  C0_nn     := by decide
  C1_nn     := by decide
  c_nn      := by decide
  base1     := by decide
  step0     := by decide
  step1     := by decide
  cover     := by decide

def EG_lower_sandwich_cert : ConePosCert TwoEG_sub_Q_rep 7 where
  P := mkMat [
    [0, 0,  1,  0,  0, 0,  0, 0,  0], -- h0 = p
    [0, 0, -1,  1,  0, 0,  0, 0,  0], -- h1 = 1 - p
    [2, 0,  0,  0, -1, 0,  0, 0,  0], -- h2 = 2*E_G - Q
    [2, 2,  1,  0, -1, 1, -1, 0,  0], -- h3 = 2*E_G - Q + 2*e + L - R + p
    [0, 0,  0,  0,  0, 0,  0, -1, 0], -- h4 = -z (= 0 for n ≥ 1)
    [0, 0,  0,  1,  0, 0,  0, 0, -1], -- h5 = 1 - 1' (= 0)
    [0, 0,  0, -1,  0, 0,  0, 0,  1]  -- h6 = 1' - 1 (= 0)
  ]
  C0 := mkMat [
    [0, 0, 0, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0, 0],
    [0, 0, 4, 0, 0, 0, 0],
    [0, 0, 2, 2, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 1]
  ]
  C1 := mkMat [
    [1, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0],
    [1, 1, 2, 2, 1, 0, 1],
    [0, 4, 0, 4, 4, 0, 3],
    [0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 1]
  ]
  c := mkVec [0, 0, 1, 0, 0, 0, 0]
  alpha := 1
  beta := 1
  alpha_pos := by decide
  beta_pos  := by decide
  C0_nn     := by decide
  C1_nn     := by decide
  c_nn      := by decide
  base1     := by decide
  step0     := by decide
  step1     := by decide
  cover     := by decide

/-- Theorem 4: Sharp two-sided dyadic parabolic sandwich for cumulative Gray value excess:
    for all `n : Nat`, `Q_dyadic(n) ≤ 2 * E_G(n)` and `E_G(n) ≤ Q_dyadic(n)`. -/
theorem E_G_dyadic_parabolic_sandwich (n : Nat) :
    Q_dyadic n ≤ 2 * E_G n ∧ E_G n ≤ Q_dyadic n := by
  cases n with
  | zero =>
    simp [E_G, sumRange, Q_dyadic, highBit_zero]
  | succ k =>
    have hpos : 1 ≤ k + 1 := by omega
    have hup := EG_upper_sandwich_cert.sound (k + 1) hpos
    rw [Q_sub_EG_rep, evalRep_sub, evalRep_QRep, evalRep_SqRep, ← E_G_eq_S2] at hup
    have hlo := EG_lower_sandwich_cert.sound (k + 1) hpos
    rw [TwoEG_sub_Q_rep, evalRep_sub, evalRep_scale, evalRep_SqRep, ← E_G_eq_S2, evalRep_QRep] at hlo
    omega

-- ----------------------------------------------------------------------------
-- THEOREM 5: Exact Shifted-Decimated Second-Difference Identity (All q : Int!)
--   ∀ q n, S_q(q, 2n) + S_q(q, 2n+2) - 2*S_q(q, 2n+1) = -2*(n % 2)
-- Proved via `LinRep.shift1` + 1-row parametric `IdentityCert`!
-- ----------------------------------------------------------------------------

/-- Combined 8-dim representation on `LinRep.shift1 (SqRep q)` observing
    `S_q(q, 2n) + S_q(q, 2n+2) - 2*S_q(q, 2n+1) + 2*(n % 2)`. -/
def SecondDiffRep (q : Int) : LinRep 8 where
  u  := mkVec [-2 * q, -2 * q, 0, 0, 2 * q, 0, 0, 0]
  M0 := (LinRep.shift1 (SqRep q)).M0
  M1 := (LinRep.shift1 (SqRep q)).M1
  v  := (LinRep.shift1 (SqRep q)).v
  stable := (LinRep.shift1 (SqRep q)).stable

theorem evalVec_SecondDiffRep (q : Int) (n : Nat) :
    evalVec (SecondDiffRep q) n = evalVec (LinRep.shift1 (SqRep q)) n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold evalVec
    split
    · rfl
    · rename_i hne
      rw [ih (n / 2) (by omega)]
      rfl

theorem evalRep_SecondDiffRep (q : Int) (n : Nat) :
    evalRep (SecondDiffRep q) n =
      S_q q (2 * n) + S_q q (2 * n + 2) - 2 * S_q q (2 * n + 1) + 2 * ((n % 2 : Nat) : Int) := by
  rw [evalRep, evalVec_SecondDiffRep, evalVec_shift1]
  have h1 := evalVec_SqRep q n
  have h2 := evalVec_SqRep q (n + 1)
  have happ : VecEq (vecAppend (evalVec (SqRep q) n) (evalVec (SqRep q) (n + 1)))
      (vecAppend (mkVec [S_q q n, dq q n, ((n % 2 : Nat) : Int), 1])
                 (mkVec [S_q q (n + 1), dq q (n + 1), (((n + 1) % 2 : Nat) : Int), 1])) := by
    intro i
    by_cases hi : i.val < 4
    · simp only [vecAppend, hi, ↓reduceDIte]; exact h1 ⟨i.val, hi⟩
    · simp only [vecAppend, hi, ↓reduceDIte]; exact h2 ⟨i.val - 4, by omega⟩
  rw [dot_congr (fun _ => rfl) happ]
  have h2n2 : 2 * n + 2 = 2 * (n + 1) := by omega
  rw [h2n2, S_q_two_mul q n, S_q_two_mul q (n + 1), S_q_two_mul_add_one q n]
  simp only [SecondDiffRep, dot, sumFin, mkVec, vecAppend,
             show (0 : Nat) < 4 by omega, show (1 : Nat) < 4 by omega,
             show (2 : Nat) < 4 by omega, show (3 : Nat) < 4 by omega,
             show ¬ (4 : Nat) < 4 by omega, show ¬ (5 : Nat) < 4 by omega,
             show ¬ (6 : Nat) < 4 by omega, show ¬ (7 : Nat) < 4 by omega,
             ↓reduceDIte, show (4 - 4 : Nat) = 0 by rfl, show (5 - 4 : Nat) = 1 by rfl,
             show (6 - 4 : Nat) = 2 by rfl, show (7 - 4 : Nat) = 3 by rfl, getIdx]
  have h2q : 2 * (q * dq q n) = 2 * q * dq q n := (Int.mul_assoc 2 q (dq q n)).symm
  have hneg : (-2) * q * S_q q n = -(2 * q * S_q q n) := by
    rw [Int.neg_mul, Int.neg_mul]
  have hneg2 : (-2) * q * dq q n = -(2 * q * dq q n) := by
    rw [Int.neg_mul, Int.neg_mul]
  omega

/-- 1-row parametric `IdentityCert` certifying `SecondDiffRep q` vanishes identically ∀ q, ∀ n! -/
def SecondDiff_identity_cert (q : Int) : IdentityCert (SecondDiffRep q) 1 where
  K  := mkMat [[-1, -1, 0, 0, 1, 0, 0, 0]]
  C0 := mkMat [[0]]
  C1 := mkMat [[2 * q]]
  c  := mkVec [2 * q]
  alpha := 1
  beta := 1
  alpha_ne := by omega
  beta_ne  := by omega
  base := by
    intro ⟨i, hi⟩
    match i with
    | 0 =>
      dsimp only [SecondDiffRep, LinRep.shift1, SqRep, matVec, sumFin, mkMat, mkVec,
                  vecAppend, vecZero, getIdx, getRow]
      simp only [show (0 : Nat) < 4 by omega, show (1 : Nat) < 4 by omega,
                 show (2 : Nat) < 4 by omega, show (3 : Nat) < 4 by omega,
                 show ¬ (4 : Nat) < 4 by omega, show ¬ (5 : Nat) < 4 by omega,
                 show ¬ (6 : Nat) < 4 by omega, show ¬ (7 : Nat) < 4 by omega,
                 ↓reduceDIte, show (4 - 4 : Nat) = 0 by rfl, show (5 - 4 : Nat) = 1 by rfl,
                 show (6 - 4 : Nat) = 2 by rfl, show (7 - 4 : Nat) = 3 by rfl,
                 getRow, getIdx]
      omega
    | _ + 1 => omega
  step0 := by
    intro ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7 =>
      dsimp only [SecondDiffRep, LinRep.shift1, SqRep, matScale, matMul, matBlock, matZero,
                  sumFin, mkMat, getRow, getIdx]
      simp only [show (0 : Nat) < 4 by omega, show (1 : Nat) < 4 by omega,
                 show (2 : Nat) < 4 by omega, show (3 : Nat) < 4 by omega,
                 show ¬ (4 : Nat) < 4 by omega, show ¬ (5 : Nat) < 4 by omega,
                 show ¬ (6 : Nat) < 4 by omega, show ¬ (7 : Nat) < 4 by omega,
                 ↓reduceDIte, show (4 - 4 : Nat) = 0 by rfl, show (5 - 4 : Nat) = 1 by rfl,
                 show (6 - 4 : Nat) = 2 by rfl, show (7 - 4 : Nat) = 3 by rfl,
                 getRow, getIdx]
      omega
    | _ + 1, _ | _, _ + 8 => omega
  step1 := by
    intro ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 | 0, 6 | 0, 7 =>
      dsimp only [SecondDiffRep, LinRep.shift1, SqRep, matScale, matMul, matBlock, matZero,
                  sumFin, mkMat, getRow, getIdx]
      simp only [show (0 : Nat) < 4 by omega, show (1 : Nat) < 4 by omega,
                 show (2 : Nat) < 4 by omega, show (3 : Nat) < 4 by omega,
                 show ¬ (4 : Nat) < 4 by omega, show ¬ (5 : Nat) < 4 by omega,
                 show ¬ (6 : Nat) < 4 by omega, show ¬ (7 : Nat) < 4 by omega,
                 ↓reduceDIte, show (4 - 4 : Nat) = 0 by rfl, show (5 - 4 : Nat) = 1 by rfl,
                 show (6 - 4 : Nat) = 2 by rfl, show (7 - 4 : Nat) = 3 by rfl,
                 getRow, getIdx]
      omega
    | _ + 1, _ | _, _ + 8 => omega
  cover := by
    intro ⟨i, hi⟩
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
      simp [SecondDiffRep, vecScale, matVec, matT, sumFin, mkMat, mkVec]; try omega
    | _ + 8 => omega

/-- Theorem 5: Universal q-independent shifted-decimated second-difference law:
    for all `q : Int` and all `n : Nat`,
    `S_q(q, 2n) + S_q(q, 2n+2) - 2*S_q(q, 2n+1) = -2*(n % 2)`. -/
theorem S_q_second_diff_identity (q : Int) (n : Nat) :
    S_q q (2 * n) + S_q q (2 * n + 2) - 2 * S_q q (2 * n + 1) = -2 * ((n % 2 : Nat) : Int) := by
  have h := (SecondDiff_identity_cert q).sound n
  rw [evalRep_SecondDiffRep] at h
  omega

theorem W_G_second_diff (n : Nat) :
    W_G (2 * n) + W_G (2 * n + 2) - 2 * W_G (2 * n + 1) = -2 * ((n % 2 : Nat) : Int) := by
  simpa [W_G_eq_S1] using S_q_second_diff_identity 1 n

theorem E_G_second_diff (n : Nat) :
    E_G (2 * n) + E_G (2 * n + 2) - 2 * E_G (2 * n + 1) = -2 * ((n % 2 : Nat) : Int) := by
  simpa [E_G_eq_S2] using S_q_second_diff_identity 2 n

-- ============================================================================
-- Section 7: Infinite Extremal Families, Non-Vacuity, Mutation Tests & Axioms
-- ============================================================================

-- Small exact evaluation helpers (using our recurrence laws, zero well-founded reduction lag)
theorem dq_one_val (q : Int) : dq q 1 = 0 := by
  simpa [dq_zero] using dq_two_mul_add_one q 0

theorem dq_two_val (q : Int) : dq q 2 = 1 := by
  simpa [dq_one_val] using dq_two_mul q 1

theorem dq_three_val (q : Int) : dq q 3 = -1 := by
  simpa [dq_one_val] using dq_two_mul_add_one q 1

theorem dq_four_val (q : Int) : dq q 4 = q := by
  simpa [dq_two_val] using dq_two_mul q 2

theorem S_q_one (q : Int) : S_q q 1 = 0 := by
  simp [S_q, sumRange, dq_zero]

theorem S_q_two (q : Int) : S_q q 2 = 0 := by
  simpa [S_q_one] using S_q_two_mul q 1

theorem S_q_three (q : Int) : S_q q 3 = 1 := by
  simpa [S_q_one, dq_one_val] using S_q_two_mul_add_one q 1

theorem extremalB_even (k : Nat) : extremalB k % 2 = 0 := by
  induction k with
  | zero => decide
  | succ m _ => simp only [extremalB]; omega

/-- Exact closed-form invariant along the infinite extremal family `extremalB`:
    for ALL `k : Nat`, `dq 1 (b_k) = 1` and `5 * (W_G b_k + 1) = 2 * (b_k + 1) - 1`. -/
theorem extremalB_invariant (k : Nat) :
    dq 1 (extremalB k) = 1 ∧ 5 * (W_G (extremalB k) + 1) = 2 * ((extremalB k + 1 : Nat) : Int) - 1 := by
  induction k with
  | zero =>
    constructor
    · exact dq_two_val 1
    · rw [extremalB, W_G_eq_S1, S_q_two]
      omega
  | succ m ih =>
    rcases ih with ⟨hdb, hWb⟩
    let b := extremalB m
    have hbeven : b % 2 = 0 := extremalB_even m
    have hstep_b : extremalB (m + 1) = 2 * (2 * (2 * b + 1) + 1) := by
      simp only [extremalB, b]; omega
    have hd1 : dq 1 (2 * b + 1) = 1 := by
      rw [dq_two_mul_add_one, hdb, hbeven]; omega
    have hd2 : dq 1 (2 * (2 * b + 1) + 1) = 0 := by
      rw [dq_two_mul_add_one, hd1]
      have hodd : (2 * b + 1) % 2 = 1 := by omega
      rw [hodd]; omega
    have hd3 : dq 1 (extremalB (m + 1)) = 1 := by
      rw [hstep_b, dq_two_mul, hd2]
      have hodd2 : (2 * (2 * b + 1) + 1) % 2 = 1 := by omega
      rw [hodd2]; omega
    have hW1 : W_G (2 * b + 1) = 2 * W_G b + 1 := by
      rw [W_G_eq_S1, S_q_two_mul_add_one, ← W_G_eq_S1, hdb, hbeven]; omega
    have hW2 : W_G (2 * (2 * b + 1) + 1) = 4 * W_G b + 4 := by
      rw [W_G_eq_S1, S_q_two_mul_add_one, ← W_G_eq_S1, hW1, hd1]
      have hodd : (2 * b + 1) % 2 = 1 := by omega
      rw [hodd]; omega
    have hW3 : W_G (extremalB (m + 1)) = 8 * W_G b + 8 := by
      rw [hstep_b, W_G_eq_S1, S_q_two_mul, ← W_G_eq_S1, hW2]; omega
    refine ⟨hd3, ?_⟩
    rw [hW3]
    have hWb' : 5 * (W_G b + 1) = 2 * ((b + 1 : Nat) : Int) - 1 := hWb
    have hcast : ((extremalB (m + 1) + 1 : Nat) : Int) = 8 * ((b + 1 : Nat) : Int) - 1 := by
      simp only [extremalB, b]; omega
    rw [hcast]
    omega

/-- Infinite odd sharpness family for Theorem 2:
    `∀ k : Nat, 5 * W_G (extremalA k) = 2 * extremalA k - 1` (exact ZERO slack!). -/
theorem extremal_W_G_odd (k : Nat) :
    5 * W_G (extremalA k) = 2 * (extremalA k : Int) - 1 := by
  rcases extremalB_invariant k with ⟨hdb, hWb⟩
  have hstep : W_G (extremalA k) = W_G (extremalB k) + dq 1 (extremalB k) := by
    rw [extremalA, W_G_eq_S1, W_G_eq_S1, S_q, sumRange, S_q]
  rw [hstep, hdb]
  exact hWb

/-- Infinite even sharpness family for Theorem 2:
    `∀ k : Nat, 5 * W_G (2 * extremalA k) = 2 * (2 * extremalA k) - 2` (exact ZERO slack!). -/
theorem extremal_W_G_even (k : Nat) :
    5 * W_G (2 * extremalA k) = 2 * ((2 * extremalA k : Nat) : Int) - 2 := by
  rw [W_G_eq_S1, S_q_two_mul, ← W_G_eq_S1]
  have hodd := extremal_W_G_odd k
  omega

-- Infinite zero family: `W_G(2^m) = 0` and `E_G(2^m) = 0` for all `m : Nat`
theorem S_q_pow2 (q : Int) (m : Nat) : S_q q (2 ^ m) = 0 := by
  induction m with
  | zero => exact S_q_one q
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_comm, S_q_two_mul, ih]
    simp

theorem W_G_pow2 (m : Nat) : W_G (2 ^ m) = 0 := by rw [W_G_eq_S1]; exact S_q_pow2 1 m
theorem E_G_pow2 (m : Nat) : E_G (2 ^ m) = 0 := by rw [E_G_eq_S2]; exact S_q_pow2 2 m

-- Infinite extremal families for Theorem 4 (dyadic parabolic sandwich!)
theorem highBit_pow2 (m : Nat) : highBit (2 ^ m) = 2 ^ m := by
  induction m with
  | zero => exact highBit_one
  | succ k ih => rw [Nat.pow_succ, Nat.mul_comm, highBit_two_mul, ih]

theorem highBit_pow2_add_one (m : Nat) (hm : 1 ≤ m) : highBit (2 ^ m + 1) = 2 ^ m := by
  cases m with
  | zero => omega
  | succ k =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, highBit_two_mul_add_one, highBit_pow2]
    simp

theorem dq_two_pow2 (m : Nat) (hm : 1 ≤ m) : dq 2 (2 ^ m) = ((2 ^ (m - 1) : Nat) : Int) := by
  induction m with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => exact dq_two_val 2
    | succ j =>
      have hpow : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      have heven : 2 ^ (j + 1) % 2 = 0 := by
        rw [Nat.pow_succ, Nat.mul_comm]; omega
      rw [hpow, dq_two_mul, ih (by omega), heven]
      have hpow2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
      simp only [Nat.add_sub_cancel, hpow2]
      omega

/-- Sharpness of Theorem 4 lower bound: for ALL `m ≥ 1`,
    `2 * E_G(2^m + 1) = Q_dyadic(2^m + 1) + 1` (exact +1 slack, ratio `E_G/Q → 1/2`!). -/
theorem extremal_E_G_lower (m : Nat) (hm : 1 ≤ m) :
    2 * E_G (2 ^ m + 1) = Q_dyadic (2 ^ m + 1) + 1 := by
  have hE : E_G (2 ^ m + 1) = ((2 ^ (m - 1) : Nat) : Int) := by
    rw [E_G_eq_S2, S_q, sumRange]
    have hz : sumRange (dq 2) (2 ^ m) = 0 := S_q_pow2 2 m
    rw [hz, Int.zero_add, dq_two_pow2 m hm]
  have hQ : Q_dyadic (2 ^ m + 1) = ((2 ^ m : Nat) : Int) - 1 := by
    rw [Q_dyadic, highBit_pow2_add_one m hm]
    have h1 : (((2 ^ m + 1 : Nat) : Int) - ((2 ^ m : Nat) : Int)) = 1 := by omega
    rw [h1, Int.one_mul]
    omega
  rw [hE, hQ]
  cases m with
  | zero => omega
  | succ k =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    simp only [Nat.add_sub_cancel, hpow]
    omega

/-- Sharpness of Theorem 4 upper bound: for ALL `m ≥ 1`,
    `E_G(3 * 2^(m-1)) = Q_dyadic(3 * 2^(m-1))` (exact ZERO slack infinitely often!). -/
theorem extremal_E_G_upper_mid (m : Nat) (hm : 1 ≤ m) :
    E_G (3 * 2 ^ (m - 1)) = Q_dyadic (3 * 2 ^ (m - 1)) := by
  cases m with
  | zero => omega
  | succ k =>
    simp only [Nat.add_sub_cancel]
    induction k with
    | zero =>
      simp only [Nat.pow_zero, Nat.mul_one, E_G_eq_S2, S_q_three, Q_dyadic]
      have hhb3 : highBit 3 = 2 := by
        simpa [highBit_one] using highBit_two_mul_add_one 1
      rw [hhb3]; omega
    | succ j ih =>
      have h2 : 3 * 2 ^ (j + 1) = 2 * (3 * 2 ^ j) := by
        rw [Nat.pow_succ]; omega
      rw [h2, E_G_eq_S2, S_q_two_mul, ← E_G_eq_S2, ih (by omega), Q_dyadic, Q_dyadic, highBit_two_mul]
      have hcast1 : ((2 * (3 * 2 ^ j) : Nat) : Int) = 2 * ((3 * 2 ^ j : Nat) : Int) := by omega
      have hcast2 : ((2 * highBit (3 * 2 ^ j) : Nat) : Int) = 2 * (highBit (3 * 2 ^ j) : Int) := by omega
      rw [hcast1, hcast2]
      have hA : 2 * ((3 * 2 ^ j : Nat) : Int) - 2 * (highBit (3 * 2 ^ j) : Int) =
          2 * (((3 * 2 ^ j : Nat) : Int) - (highBit (3 * 2 ^ j) : Int)) := by omega
      have hB : 2 * (2 * (highBit (3 * 2 ^ j) : Int)) - 2 * ((3 * 2 ^ j : Nat) : Int) =
          2 * (2 * (highBit (3 * 2 ^ j) : Int) - ((3 * 2 ^ j : Nat) : Int)) := by omega
      rw [hA, hB]
      have hmul4 : ∀ x y : Int, 2 * 2 * (x * y) = (2 * x) * (2 * y) := by
        intro x y
        calc 2 * 2 * (x * y) = 2 * (2 * (x * y)) := Int.mul_assoc 2 2 (x * y)
          _ = 2 * (x * (2 * y)) := by rw [Int.mul_left_comm 2 x y]
          _ = (2 * x) * (2 * y) := (Int.mul_assoc 2 x (2 * y)).symm
      exact hmul4 _ _

-- ----------------------------------------------------------------------------
-- Pure-Data Checker Verification & Hostile Mutation Rejection Tests
-- ----------------------------------------------------------------------------

/-- Pure-data package of the 6-row `ConePosCert` for Theorem 2. -/
def WG_upper_data : ConePosCertData 5 6 where
  P := WG_upper_cone_cert.P
  C0 := WG_upper_cone_cert.C0
  C1 := WG_upper_cone_cert.C1
  c := WG_upper_cone_cert.c
  alpha := WG_upper_cone_cert.alpha
  beta := WG_upper_cone_cert.beta

/-- Positive pure-data acceptance test (compiles via `checkConePosCert_sound`). -/
theorem WG_upper_data_accepted : checkConePosCert WGUpperRep WG_upper_data = true := by decide

/-- Hostile mutation test 1: tightening the target constant from `-2` to `-3` in `u`
    is REJECTED by `checkConePosCert` (demonstrates non-triviality of the checker). -/
def WGUpperRep_tightened : LinRep 5 := { WGUpperRep with u := mkVec [-5, 0, 1, -3, 2] }

theorem mutation_rejected_tightened_target :
    checkConePosCert WGUpperRep_tightened WG_upper_data = false := by decide

/-- Hostile mutation test 2: corrupting one entry of `C0` (`7 -> 6`) is REJECTED. -/
def WG_upper_data_corruptC0 : ConePosCertData 5 6 :=
  { WG_upper_data with
    C0 := mkMat [
      [0, 0, 0, 0, 0, 0],
      [2, 2, 0, 0, 0, 0],
      [0, 6, 0, 3, 1, 0],
      [0, 5, 0, 1, 3, 0],
      [0, 4, 0, 0, 2, 2],
      [0, 4, 0, 0, 0, 4]
    ] }

theorem mutation_rejected_corrupt_C0 :
    checkConePosCert WGUpperRep WG_upper_data_corruptC0 = false := by decide

/-- Pure-data package of `ModCert` for Theorem 3a + hostile mutation test (modulus 2 → 4 rejected). -/
def WG_mod2_data : ModCertData 7 3 where
  K := WG_mod2_cert.K
  C0 := WG_mod2_cert.C0
  C1 := WG_mod2_cert.C1
  c := WG_mod2_cert.c
  m := 2

theorem WG_mod2_data_accepted :
    checkModCert (LinRep.sub (SqRep 1) OddEvenPopRep) WG_mod2_data = true := by decide

theorem mutation_rejected_mod4_WG :
    checkModCert (LinRep.sub (SqRep 1) OddEvenPopRep) { WG_mod2_data with m := 4 } = false := by
  decide

-- ----------------------------------------------------------------------------
-- Non-Vacuity Witnesses (`Nonempty`) for Every Proof Engine Structure
-- ----------------------------------------------------------------------------

theorem nonvacuity_IdentityCert : Nonempty (IdentityCert (SecondDiffRep 1) 1) :=
  ⟨SecondDiff_identity_cert 1⟩
theorem nonvacuity_IntertwineCert : Nonempty (IntertwineCert QRep (LinRep.mul LRep RRep)) :=
  ⟨Q_kron_intertwine⟩
theorem nonvacuity_ModCert_2 : Nonempty (ModCert (LinRep.sub (SqRep 1) OddEvenPopRep) 3 2) :=
  ⟨WG_mod2_cert⟩
theorem nonvacuity_ModCert_4 : Nonempty (ModCert (LinRep.sub (SqRep 2) Mod4RefRep) 4 4) :=
  ⟨EG_mod4_cert⟩
theorem nonvacuity_ConeCert : Nonempty (ConeCert (SqRep 1) 4) :=
  ⟨Sq_nonneg_cert 1 (by omega)⟩
theorem nonvacuity_ConePosCert_WG : Nonempty (ConePosCert WGUpperRep 6) :=
  ⟨WG_upper_cone_cert⟩
theorem nonvacuity_ConePosCert_EG_up : Nonempty (ConePosCert Q_sub_EG_rep 6) :=
  ⟨EG_upper_sandwich_cert⟩
theorem nonvacuity_ConePosCert_EG_lo : Nonempty (ConePosCert TwoEG_sub_Q_rep 7) :=
  ⟨EG_lower_sandwich_cert⟩

-- ----------------------------------------------------------------------------
-- Kernel-Checked Boundary Counterexamples (Sharpness & Non-Triviality!)
-- ----------------------------------------------------------------------------

/-- Termwise nonnegativity FAILS: at `k = 7`, `popcount(G(7)) - popcount(7) = -2 < 0`
    and `G(7) - 7 = -3 < 0`. -/
theorem counterexample_termwise_negative :
    (popcount (gray 7) : Int) - (popcount 7 : Int) = -2 ∧ (gray 7 : Int) - 7 = -3 := by
  have h1 : (popcount (gray 7) : Int) - (popcount 7 : Int) = dq 1 7 := (dq_one_eq 7).symm
  have h2 : (gray 7 : Int) - 7 = dq 2 7 := (dq_two_eq 7).symm
  have hd1 : dq 1 7 = -2 := by
    have h7 : (7 : Nat) = 2 * 3 + 1 := rfl
    rw [h7, dq_two_mul_add_one, dq_three_val]; omega
  have hd2 : dq 2 7 = -3 := by
    have h7 : (7 : Nat) = 2 * 3 + 1 := rfl
    rw [h7, dq_two_mul_add_one, dq_three_val]; omega
  exact ⟨h1.trans hd1, h2.trans hd2⟩

/-- Theorem 1 parameter bound `q ≥ 0` is sharp: fails at `q = -1, n = 5` (`S_q (-1) 5 = -1 < 0`). -/
theorem counterexample_q_negative : S_q (-1) 5 = -1 := by
  have h5 : (5 : Nat) = 2 * 2 + 1 := rfl
  rw [h5, S_q_two_mul_add_one, S_q_two, dq_two_val]
  omega

/-- Theorem 2 additive terms `-1` (odd) and `-2` (even) cannot be tightened by 1:
    equality holds at `n = 3 = extremalA 0` and `n = 6 = 2 * extremalA 0`. -/
theorem counterexample_WG_tight_additive :
    5 * W_G 3 = 2 * 3 - 1 ∧ 5 * W_G 6 = 2 * 6 - 2 :=
  ⟨extremal_W_G_odd 0, extremal_W_G_even 0⟩

/-- Theorem 2 slope `2/5 = 0.400` cannot be lowered to `399/1000`:
    fails at `n = 1463 = extremalA 3` where `W_G(1463) = 585` and `1000*585 > 399*1463`. -/
theorem counterexample_WG_tight_slope :
    W_G 1463 = 585 ∧ 1000 * W_G 1463 > 399 * 1463 := by
  have h := extremal_W_G_odd 3
  have ha3 : extremalA 3 = 1463 := by decide
  rw [ha3] at h
  omega

/-- Theorem 3a parity `W_G(n) mod 2` is NOT periodic of period 4: `W_G(3) = 1` vs `W_G(7) = 2`. -/
theorem counterexample_WG_not_period4 :
    W_G 3 % 2 = 1 ∧ W_G 7 % 2 = 0 := by
  have h3 : W_G 3 = 1 := by rw [W_G_eq_S1, S_q_three]
  have h7 : W_G 7 = 2 := by
    have : (7 : Nat) = 2 * 3 + 1 := rfl
    rw [this, W_G_eq_S1, S_q_two_mul_add_one, S_q_three, dq_three_val]; omega
  rw [h3, h7]; decide

/-- Theorem 4 lower ratio `1/2` cannot be raised to `51/100`:
    fails at `n = 65 = 2^6 + 1` where `E_G(65) = 32`, `Q_dyadic(65) = 63`,
    and `100 * 32 = 3200 < 3213 = 51 * 63`. -/
theorem counterexample_EG_tight_lower_ratio :
    E_G 65 = 32 ∧ Q_dyadic 65 = 63 ∧ 100 * E_G 65 < 51 * Q_dyadic 65 := by
  have h := extremal_E_G_lower 6 (by omega)
  have hQ : Q_dyadic 65 = 63 := by
    have h65 : (65 : Nat) = 2 ^ 6 + 1 := by decide
    rw [h65, Q_dyadic, highBit_pow2_add_one 6 (by omega)]
    omega
  have h65 : 2 ^ 6 + 1 = 65 := by decide
  rw [h65, hQ] at h
  omega

-- ----------------------------------------------------------------------------
-- Exhaustive Axiom Audit (`#print axioms`) on All Engine & Domain Theorems
-- ----------------------------------------------------------------------------


end LinRepEngine
