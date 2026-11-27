/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SternWalshCarryResonance.Defs

/-!
# Proofs (`stern-walsh-carry-resonance`)

Stern diatomic sequence, Calkin-Wilf SL2(Z) tree matrices, Walsh-Hadamard monomial lifter, carry-orbit lifter and mod-3 resonance laws.
-/

namespace SternCW

def Vec2.sub (u v : Vec2) : Vec2 := ⟨u.x - v.x, u.y - v.y⟩
def Vec2.neg (u : Vec2) : Vec2 := ⟨-u.x, -u.y⟩
def Mat2.sub (M N : Mat2) : Mat2 := ⟨M.a - N.a, M.b - N.b, M.c - N.c, M.d - N.d⟩
def Mat2.det (M : Mat2) : Int := M.a * M.d - M.b * M.c
def Mat2.transpose (M : Mat2) : Mat2 := ⟨M.a, M.c, M.b, M.d⟩

def Jmat : Mat2 := ⟨0, 1, 1, 0⟩
def L1 : Mat2 := Lmat 1
def R1 : Mat2 := Rmat 1
def eMinus : Vec2 := ⟨-1, 1⟩

theorem ofNat_add (a b : Nat) : Int.ofNat (a + b) = Int.ofNat a + Int.ofNat b := rfl

theorem Mat2.mul_assoc (A B C : Mat2) : (A.mul B).mul C = A.mul (B.mul C) := by
  cases A; cases B; cases C
  simp only [Mat2.mul, Mat2.mk.injEq]
  refine ⟨by grind, by grind, by grind, by grind⟩

theorem Mat2.id_mul (A : Mat2) : Mat2.id.mul A = A := by
  cases A; simp [Mat2.id, Mat2.mul]

theorem Mat2.mul_id (A : Mat2) : A.mul Mat2.id = A := by
  cases A; simp [Mat2.id, Mat2.mul]

theorem Mat2.mul_mulV (A B : Mat2) (v : Vec2) :
    (A.mul B).mulV v = A.mulV (B.mulV v) := by
  cases A; cases B; cases v
  simp only [Mat2.mul, Mat2.mulV, Vec2.mk.injEq]
  exact ⟨by grind, by grind⟩

theorem Mat2.mulV_add (M : Mat2) (u v : Vec2) :
    M.mulV (u.add v) = (M.mulV u).add (M.mulV v) := by
  cases M; cases u; cases v
  simp only [Mat2.mulV, Vec2.add, Vec2.mk.injEq]
  exact ⟨by grind, by grind⟩

theorem Mat2.mulV_smul (M : Mat2) (s : Int) (v : Vec2) :
    M.mulV (v.smul s) = (M.mulV v).smul s := by
  cases M; cases v
  simp only [Mat2.mulV, Vec2.smul, Vec2.mk.injEq]
  exact ⟨by grind, by grind⟩

theorem Mat2.add_mulV (M N : Mat2) (v : Vec2) :
    (M.add N).mulV v = (M.mulV v).add (N.mulV v) := by
  cases M; cases N; cases v
  simp only [Mat2.add, Mat2.mulV, Vec2.add, Vec2.mk.injEq]
  exact ⟨by grind, by grind⟩

theorem Mat2.sub_mulV (M N : Mat2) (v : Vec2) :
    (M.sub N).mulV v = (M.mulV v).sub (N.mulV v) := by
  cases M; cases N; cases v
  simp only [Mat2.sub, Mat2.mulV, Vec2.sub, Vec2.mk.injEq]
  exact ⟨by grind, by grind⟩

theorem Mat2.det_mul (A B : Mat2) : (A.mul B).det = A.det * B.det := by
  cases A; cases B
  simp only [Mat2.mul, Mat2.det]
  grind

theorem Mat2.transpose_mul (A B : Mat2) :
    (A.mul B).transpose = B.transpose.mul A.transpose := by
  cases A; cases B
  simp only [Mat2.mul, Mat2.transpose, Mat2.mk.injEq]
  refine ⟨by grind, by grind, by grind, by grind⟩

theorem Mat2.det_Lmat (a : Int) : (Lmat a).det = 1 := by simp [Lmat, Mat2.det]
theorem Mat2.det_Rmat (a : Int) : (Rmat a).det = 1 := by simp [Rmat, Mat2.det]
theorem Mat2.J_mul_J : Jmat.mul Jmat = Mat2.id := by decide
theorem Mat2.J_L_J (a : Int) : (Jmat.mul (Lmat a)).mul Jmat = Rmat a := by
  simp [Jmat, Lmat, Rmat, Mat2.mul]
theorem Mat2.J_R_J (a : Int) : (Jmat.mul (Rmat a)).mul Jmat = Lmat a := by
  simp [Jmat, Lmat, Rmat, Mat2.mul]
theorem Mat2.L_transpose (a : Int) : (Lmat a).transpose = Rmat a := by
  simp [Lmat, Rmat, Mat2.transpose]
theorem Mat2.R_transpose (a : Int) : (Rmat a).transpose = Lmat a := by
  simp [Lmat, Rmat, Mat2.transpose]

theorem sumVec_x (n : Nat) (f : Nat → Vec2) :
    (sumVec n f).x = sumInt n (fun i => (f i).x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumVec, sumInt, Vec2.add, ih]

theorem sumVec_y (n : Nat) (f : Nat → Vec2) :
    (sumVec n f).y = sumInt n (fun i => (f i).y) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumVec, sumInt, Vec2.add, ih]

theorem sumVec_congr (n : Nat) (f g : Nat → Vec2) (h : ∀ i < n, f i = g i) :
    sumVec n f = sumVec n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumVec]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sumVec_mulV (M : Mat2) (n : Nat) (f : Nat → Vec2) :
    sumVec n (fun i => M.mulV (f i)) = M.mulV (sumVec n f) := by
  induction n with
  | zero => cases M; simp [sumVec, Vec2.zero, Mat2.mulV]
  | succ n ih => simp [sumVec, ih, Mat2.mulV_add]

theorem sumVec_smul (s : Int) (n : Nat) (f : Nat → Vec2) :
    (sumVec n f).smul s = sumVec n (fun i => (f i).smul s) := by
  induction n with
  | zero => simp [sumVec, Vec2.zero, Vec2.smul]
  | succ n ih =>
    simp only [sumVec]
    rw [← ih]
    cases (sumVec n f); cases (f n)
    simp only [Vec2.add, Vec2.smul, Vec2.mk.injEq]
    exact ⟨by grind, by grind⟩

theorem sumVec_even_odd (n : Nat) (f : Nat → Vec2) :
    sumVec (2 * n) f = (sumVec n (fun i => f (2 * i))).add (sumVec n (fun i => f (2 * i + 1))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [h2]
    simp only [sumVec]
    rw [ih]
    cases (sumVec n (fun i => f (2 * i))); cases (sumVec n (fun i => f (2 * i + 1)))
    cases (f (2 * n)); cases (f (2 * n + 1))
    simp only [Vec2.add, Vec2.mk.injEq]
    exact ⟨by omega, by omega⟩

theorem sumInt_congr (n : Nat) (f g : Nat → Int) (h : ∀ i < n, f i = g i) :
    sumInt n f = sumInt n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumInt]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

@[simp] theorem popcount_zero : popcount 0 = 0 := by rw [popcount]
@[simp] theorem popcount_succ_eq (k : Nat) : popcount (k + 1) = (k + 1) % 2 + popcount ((k + 1) / 2) := by
  conv => lhs; rw [popcount]

theorem popcount_div2 (n : Nat) : popcount n = n % 2 + popcount (n / 2) := by
  cases n with
  | zero => simp
  | succ k => simp

theorem popcount_two_mul (n : Nat) : popcount (2 * n) = popcount n := by
  cases n with
  | zero => simp
  | succ k =>
    rw [popcount_div2]
    have h1 : 2 * (k + 1) % 2 = 0 := by omega
    have h2 : 2 * (k + 1) / 2 = k + 1 := by omega
    rw [h1, h2]; omega

theorem popcount_two_mul_add_one (n : Nat) : popcount (2 * n + 1) = popcount n + 1 := by
  rw [popcount_div2]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]; omega

@[simp] theorem tmSign_zero : tmSign 0 = 1 := by simp [tmSign]
@[simp] theorem tmSign_one : tmSign 1 = -1 := by simp [tmSign]

theorem tmSign_two_mul (n : Nat) : tmSign (2 * n) = tmSign n := by
  simp [tmSign, popcount_two_mul]

theorem tmSign_two_mul_add_one (n : Nat) : tmSign (2 * n + 1) = -tmSign n := by
  simp only [tmSign, popcount_two_mul_add_one]
  split <;> split <;> omega

theorem tmSign_sq (n : Nat) : tmSign n * tmSign n = 1 := by
  unfold tmSign; split <;> decide

@[simp] theorem bitAnd_zero_left (b : Nat) : bitAnd 0 b = 0 := by
  cases b <;> rw [bitAnd]
@[simp] theorem bitAnd_zero_right (a : Nat) : bitAnd a 0 = 0 := by
  cases a with
  | zero => rw [bitAnd]
  | succ a' => rw [bitAnd]; intro h; omega
theorem bitAnd_succ_succ (a b : Nat) :
    bitAnd (a + 1) (b + 1) = ((a + 1) % 2) * ((b + 1) % 2) + 2 * bitAnd ((a + 1) / 2) ((b + 1) / 2) := by
  conv => lhs; rw [bitAnd]

theorem bitAnd_eq_land (a b : Nat) : bitAnd a b = a &&& b := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    cases a with
    | zero => simp
    | succ a' =>
      cases b with
      | zero => simp
      | succ b' =>
        rw [bitAnd_succ_succ]
        have hlt : (a' + 1) / 2 < a' + 1 := by omega
        rw [ih _ hlt]
        have hbit : (a' + 1) &&& (b' + 1) =
            2 * (((a' + 1) / 2) &&& ((b' + 1) / 2)) + ((a' + 1) % 2) * ((b' + 1) % 2) := by
          apply Nat.eq_of_testBit_eq
          intro i
          cases i with
          | zero =>
            simp only [Nat.testBit_zero]
            have ha : (a' + 1) % 2 = 0 ∨ (a' + 1) % 2 = 1 := by omega
            have hb : (b' + 1) % 2 = 0 ∨ (b' + 1) % 2 = 1 := by omega
            rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
          | succ j =>
            rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
            have ha : (a' + 1) % 2 = 0 ∨ (a' + 1) % 2 = 1 := by omega
            have hb : (b' + 1) % 2 = 0 ∨ (b' + 1) % 2 = 1 := by omega
            have hrem : ((a' + 1) % 2) * ((b' + 1) % 2) < 2 := by
              rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
            have hdiv : (2 * (((a' + 1) / 2) &&& ((b' + 1) / 2)) +
                ((a' + 1) % 2) * ((b' + 1) % 2)) / 2 = ((a' + 1) / 2) &&& ((b' + 1) / 2) := by
              omega
            rw [hdiv, Nat.testBit_and]
        omega

theorem bitAnd_two_mul_left (x m : Nat) : bitAnd (2 * x) m = 2 * bitAnd x (m / 2) := by
  cases x with
  | zero => simp
  | succ x' =>
    cases m with
    | zero => simp
    | succ m' =>
      have hpos : 2 * (x' + 1) = (2 * x' + 1) + 1 := by omega
      rw [hpos, bitAnd_succ_succ]
      have h1 : (2 * x' + 1 + 1) % 2 = 0 := by omega
      have h2 : (2 * x' + 1 + 1) / 2 = x' + 1 := by omega
      rw [h1, h2]; simp

theorem bitAnd_two_mul_add_one_left (x m : Nat) :
    bitAnd (2 * x + 1) m = m % 2 + 2 * bitAnd x (m / 2) := by
  cases m with
  | zero => simp
  | succ m' =>
    rw [bitAnd_succ_succ]
    have h1 : (2 * x + 1) % 2 = 1 := by omega
    have h2 : (2 * x + 1) / 2 = x := by omega
    rw [h1, h2]; simp

@[simp] theorem igray_zero : igray 0 = 0 := by rw [igray]
theorem igray_succ_eq (k : Nat) : igray (k + 1) = (k + 1) ^^^ igray ((k + 1) / 2) := by
  conv => lhs; rw [igray]

theorem igray_eq_xor (n : Nat) : igray n = n ^^^ igray (n / 2) := by
  cases n with
  | zero => simp
  | succ k => exact igray_succ_eq k

theorem igray_mod2 (n : Nat) : igray n % 2 = popcount n % 2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp
    | succ k =>
      rw [igray_eq_xor, popcount_div2]
      have hlt : (k + 1) / 2 < k + 1 := by omega
      have hrec := ih _ hlt
      have hxor : ((k + 1) ^^^ igray ((k + 1) / 2)) % 2 =
          ((k + 1) % 2 + igray ((k + 1) / 2) % 2) % 2 := by
        have htb := Nat.testBit_xor (k + 1) (igray ((k + 1) / 2)) 0
        simp only [Nat.testBit_zero] at htb
        have h1 : (k + 1) % 2 = 0 ∨ (k + 1) % 2 = 1 := by omega
        have h2 : igray ((k + 1) / 2) % 2 = 0 ∨ igray ((k + 1) / 2) % 2 = 1 := by omega
        have h3 : ((k + 1) ^^^ igray ((k + 1) / 2)) % 2 = 0 ∨
                  ((k + 1) ^^^ igray ((k + 1) / 2)) % 2 = 1 := by omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
          simp_all
      rw [hxor, hrec]; omega

theorem igray_div2 (n : Nat) : igray n / 2 = igray (n / 2) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp
    | succ k =>
      have hlt : (k + 1) / 2 < k + 1 := by omega
      have hrec := ih ((k + 1) / 2) hlt
      rw [igray_eq_xor (k + 1)]
      apply Nat.eq_of_testBit_eq
      intro i
      rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, hrec,
          ← Nat.testBit_xor, ← igray_eq_xor ((k + 1) / 2)]

theorem popcount_or_step (m : Nat) :
    popcount (m ||| igray m) =
      (if m % 2 = 1 ∨ popcount (m / 2) % 2 = 1 then 1 else 0) +
      popcount ((m / 2) ||| igray (m / 2)) := by
  rw [popcount_div2]
  have hdiv : (m ||| igray m) / 2 = (m / 2) ||| igray (m / 2) := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [← Nat.testBit_succ, Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ,
        igray_div2, ← Nat.testBit_or]
  rw [hdiv]
  have hmod : (m ||| igray m) % 2 = if m % 2 = 1 ∨ popcount (m / 2) % 2 = 1 then 1 else 0 := by
    have htb := Nat.testBit_or m (igray m) 0
    simp only [Nat.testBit_zero] at htb
    have hig := igray_mod2 m
    rw [popcount_div2] at hig
    have h1 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    have h2 : popcount (m / 2) % 2 = 0 ∨ popcount (m / 2) % 2 = 1 := by omega
    have h3 : (m ||| igray m) % 2 = 0 ∨ (m ||| igray m) % 2 = 1 := by omega
    have h4 : igray m % 2 = 0 ∨ igray m % 2 = 1 := by omega
    have hsum : (m % 2 + popcount (m / 2)) % 2 = (m % 2 + popcount (m / 2) % 2) % 2 := by omega
    rw [hsum] at hig
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      rcases h4 with h4 | h4 <;>
      (rw [h1, h2, h4] at hig; try rw [h1, h4, h3] at htb) <;>
      (simp only [h1, h2, h3, h4] at *) <;>
      (try omega) <;> (try decide) <;> (try contradiction)
  rw [hmod]

theorem popcount_or_le (k m : Nat) (hm : m < 2 ^ k) : popcount (m ||| igray m) ≤ k := by
  induction k generalizing m with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0; simp
  | succ k ih =>
    rw [popcount_or_step]
    have hdiv : m / 2 < 2 ^ k := by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      omega
    have hrec := ih (m / 2) hdiv
    split <;> omega

@[simp] theorem stern_zero : stern 0 = 0 := by rw [stern]
@[simp] theorem stern_one : stern 1 = 1 := by rw [stern]

theorem stern_two_mul (n : Nat) : stern (2 * n) = stern n := by
  cases n with
  | zero => simp
  | succ k =>
    have h : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h]
    conv => lhs; rw [stern]
    have hmod : (2 * k + 2) % 2 = 0 := by omega
    have hdiv : (2 * k + 2) / 2 = k + 1 := by omega
    simp [hmod, hdiv]

theorem stern_two_mul_add_one (n : Nat) : stern (2 * n + 1) = stern n + stern (n + 1) := by
  cases n with
  | zero => simp
  | succ k =>
    have h : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [h]
    conv => lhs; rw [stern]
    have hmod : (2 * k + 1 + 2) % 2 = 1 := by omega
    have hdiv : (2 * k + 1 + 2) / 2 = k + 1 := by omega
    simp [hmod, hdiv]

theorem treeMat_two_mul (M0 M1 : Mat2) (k x : Nat) :
    treeMat M0 M1 (k + 1) (2 * x) = M0.mul (treeMat M0 M1 k x) := by
  simp only [treeMat]
  have h1 : 2 * x % 2 = 0 := by omega
  have h2 : 2 * x / 2 = x := by omega
  simp [h1, h2]

theorem treeMat_two_mul_add_one (M0 M1 : Mat2) (k x : Nat) :
    treeMat M0 M1 (k + 1) (2 * x + 1) = M1.mul (treeMat M0 M1 k x) := by
  simp only [treeMat]
  have h1 : (2 * x + 1) % 2 = 1 := by omega
  have h2 : (2 * x + 1) / 2 = x := by omega
  simp [h1, h2]

theorem cwMat_det (a : Int) (k x : Nat) : (cwMat a k x).det = 1 := by
  unfold cwMat
  induction k generalizing x with
  | zero => simp [treeMat, Mat2.id, Mat2.det]
  | succ k ih =>
    simp only [treeMat]
    rw [Mat2.det_mul, ih]
    split
    · rw [Mat2.det_Lmat]; omega
    · rw [Mat2.det_Rmat]; omega

/-- Exact bridge between the Calkin-Wilf `SL₂(ℤ)` binary-word matrix product and Stern's sequence. -/
theorem stern_cw_bridge (k : Nat) :
    ∀ x < 2 ^ k, cwVec 1 k x = ⟨Int.ofNat (stern (2 ^ k + x)), Int.ofNat (stern (2 ^ k + x + 1))⟩ := by
  induction k with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by omega
    subst hx0
    have hs2 : stern 2 = 1 := by
      have := stern_two_mul 1; simp at this; exact this
    simp [cwVec, cwMat, treeMat, Mat2.id, Mat2.mulV, ePlus, hs2]
  | succ k ih =>
    intro x hx
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hdiv : x / 2 < 2 ^ k := by omega
    have ihx := ih (x / 2) hdiv
    unfold cwVec cwMat
    simp only [treeMat]
    rw [Mat2.mul_mulV]
    change (if x % 2 = 0 then Lmat 1 else Rmat 1).mulV (cwVec 1 k (x / 2)) = _
    rw [ihx]
    by_cases hpar : x % 2 = 0
    · simp only [hpar, ↓reduceIte, Lmat, Mat2.mulV]
      have hx2 : 2 ^ (k + 1) + x = 2 * (2 ^ k + x / 2) := by omega
      rw [hx2, stern_two_mul, stern_two_mul_add_one]
      simp only [Vec2.mk.injEq, ofNat_add]; exact ⟨by omega, by omega⟩
    · simp only [hpar, ↓reduceIte, Rmat, Mat2.mulV]
      have hx2 : 2 ^ (k + 1) + x = 2 * (2 ^ k + x / 2) + 1 := by omega
      have hx21 : 2 * (2 ^ k + x / 2) + 1 + 1 = 2 * (2 ^ k + x / 2 + 1) := by omega
      rw [hx2, hx21, stern_two_mul_add_one, stern_two_mul]
      simp only [Vec2.mk.injEq, ofNat_add]; exact ⟨by omega, by omega⟩

/-- Bitwise complement conjugation on the Calkin-Wilf matrix word: `W(x̄) = J W(x) J`. -/
theorem cwMat_complement (a : Int) (k : Nat) :
    ∀ x < 2 ^ k, cwMat a k (2 ^ k - 1 - x) = (Jmat.mul (cwMat a k x)).mul Jmat := by
  induction k with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by omega
    subst hx0; simp [cwMat, treeMat, Mat2.id, Jmat, Mat2.mul]
  | succ k ih =>
    intro x hx
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpow_pos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hdiv : x / 2 < 2 ^ k := by omega
    have hcomp_div : (2 ^ (k + 1) - 1 - x) / 2 = 2 ^ k - 1 - x / 2 := by omega
    have hcomp_mod : (2 ^ (k + 1) - 1 - x) % 2 = 1 - x % 2 := by omega
    unfold cwMat
    simp only [treeMat]
    rw [hcomp_div, hcomp_mod]
    have ihx := ih (x / 2) hdiv
    unfold cwMat at ihx
    rw [ihx]
    by_cases hpar : x % 2 = 0
    · simp only [hpar, Nat.sub_zero, Nat.one_ne_zero, ↓reduceIte]
      calc (Rmat a).mul ((Jmat.mul (treeMat (Lmat a) (Rmat a) k (x / 2))).mul Jmat)
          = ((Rmat a).mul (Jmat.mul (treeMat (Lmat a) (Rmat a) k (x / 2)))).mul Jmat := by
              rw [← Mat2.mul_assoc]
        _ = (((Jmat.mul (Lmat a)).mul Jmat).mul (Jmat.mul (treeMat (Lmat a) (Rmat a) k (x / 2)))).mul Jmat := by
              rw [Mat2.J_L_J]
        _ = (Jmat.mul ((Lmat a).mul ((Jmat.mul Jmat).mul (treeMat (Lmat a) (Rmat a) k (x / 2))))).mul Jmat := by
              simp only [Mat2.mul_assoc]
        _ = (Jmat.mul ((Lmat a).mul (treeMat (Lmat a) (Rmat a) k (x / 2)))).mul Jmat := by
              rw [Mat2.J_mul_J, Mat2.id_mul]
    · have h1 : x % 2 = 1 := by omega
      simp only [h1, Nat.sub_self, ↓reduceIte, Nat.one_ne_zero]
      calc (Lmat a).mul ((Jmat.mul (treeMat (Lmat a) (Rmat a) k (x / 2))).mul Jmat)
          = ((Lmat a).mul (Jmat.mul (treeMat (Lmat a) (Rmat a) k (x / 2)))).mul Jmat := by
              rw [← Mat2.mul_assoc]
        _ = (((Jmat.mul (Rmat a)).mul Jmat).mul (Jmat.mul (treeMat (Lmat a) (Rmat a) k (x / 2)))).mul Jmat := by
              rw [Mat2.J_R_J]
        _ = (Jmat.mul ((Rmat a).mul ((Jmat.mul Jmat).mul (treeMat (Lmat a) (Rmat a) k (x / 2))))).mul Jmat := by
              simp only [Mat2.mul_assoc]
        _ = (Jmat.mul ((Rmat a).mul (treeMat (Lmat a) (Rmat a) k (x / 2)))).mul Jmat := by
              rw [Mat2.J_mul_J, Mat2.id_mul]

/-! ## Section 2: Reusable Infinite Proof Engine I — Hadamard Monomialization Lifter -/

/-- Finite 4-equation integer certificate certifying simultaneous Hadamard monomialization
    of `(M₀ + M₁)` and `(M₀ - M₁)` in basis `(eP, eM)`. -/
structure HadamardCert (M0 M1 : Mat2) (eP eM : Vec2) (lamP lamM mu : Int) : Prop where
  add_plus  : (M0.add M1).mulV eP = eP.smul lamP
  add_minus : (M0.add M1).mulV eM = eM.smul lamM
  sub_plus  : (M0.sub M1).mulV eP = eM.smul mu
  sub_minus : (M0.sub M1).mulV eM = eP.smul (-mu)

/-- Quarter-turn rotation in the `(eP, eM)` basis indexed by `popcount m mod 4`. -/
def rotBasis (eP eM : Vec2) (r : Nat) : Vec2 :=
  match r % 4 with
  | 0 => eP
  | 1 => eM
  | 2 => eP.neg
  | _ => eM.neg

theorem rotBasis_succ_sub (M0 M1 : Mat2) (eP eM : Vec2) (lamP lamM mu : Int)
    (hcert : HadamardCert M0 M1 eP eM lamP lamM mu) (r : Nat) :
    (M0.sub M1).mulV (rotBasis eP eM r) = (rotBasis eP eM (r + 1)).smul mu := by
  have hmod : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · have h' : (r + 1) % 4 = 1 := by omega
    simp [rotBasis, h, h', hcert.sub_plus]
  · have h' : (r + 1) % 4 = 2 := by omega
    simp only [rotBasis, h, h', hcert.sub_minus]
    cases eP; simp only [Vec2.neg, Vec2.smul, Vec2.mk.injEq]; exact ⟨by grind, by grind⟩
  · have h' : (r + 1) % 4 = 3 := by omega
    simp only [rotBasis, h, h']
    have hneg : eP.neg = eP.smul (-1) := by cases eP; simp [Vec2.neg, Vec2.smul]
    rw [hneg, Mat2.mulV_smul, hcert.sub_plus]
    cases eM; simp only [Vec2.neg, Vec2.smul, Vec2.mk.injEq]; exact ⟨by grind, by grind⟩
  · have h' : (r + 1) % 4 = 0 := by omega
    simp only [rotBasis, h, h']
    have hneg : eM.neg = eM.smul (-1) := by cases eM; simp [Vec2.neg, Vec2.smul]
    rw [hneg, Mat2.mulV_smul, hcert.sub_minus]
    cases eP; simp only [Vec2.smul, Vec2.mk.injEq]; exact ⟨by grind, by grind⟩

theorem rotBasis_add_even (M0 M1 : Mat2) (eP eM : Vec2) (lamP lamM mu : Int)
    (hcert : HadamardCert M0 M1 eP eM lamP lamM mu) (r : Nat) (hr : r % 2 = 0) :
    (M0.add M1).mulV (rotBasis eP eM r) = (rotBasis eP eM r).smul lamP := by
  have hmod : r % 4 = 0 ∨ r % 4 = 2 := by omega
  rcases hmod with h | h
  · simp [rotBasis, h, hcert.add_plus]
  · simp only [rotBasis, h]
    have hneg : eP.neg = eP.smul (-1) := by cases eP; simp [Vec2.neg, Vec2.smul]
    rw [hneg, Mat2.mulV_smul, hcert.add_plus]
    cases eP; simp only [Vec2.smul, Vec2.mk.injEq]; exact ⟨by grind, by grind⟩

theorem rotBasis_add_odd (M0 M1 : Mat2) (eP eM : Vec2) (lamP lamM mu : Int)
    (hcert : HadamardCert M0 M1 eP eM lamP lamM mu) (r : Nat) (hr : r % 2 = 1) :
    (M0.add M1).mulV (rotBasis eP eM r) = (rotBasis eP eM r).smul lamM := by
  have hmod : r % 4 = 1 ∨ r % 4 = 3 := by omega
  rcases hmod with h | h
  · simp [rotBasis, h, hcert.add_minus]
  · simp only [rotBasis, h]
    have hneg : eM.neg = eM.smul (-1) := by cases eM; simp [Vec2.neg, Vec2.smul]
    rw [hneg, Mat2.mulV_smul, hcert.add_minus]
    cases eM; simp only [Vec2.smul, Vec2.mk.injEq]; exact ⟨by grind, by grind⟩

/-- Fundamental factorization of the Walsh-Hadamard transform by LSB of mask `m`. -/
theorem walshSum_succ (M0 M1 : Mat2) (v0 : Vec2) (k m : Nat) :
    walshSum M0 M1 v0 (k + 1) m =
      (if m % 2 = 0 then M0.add M1 else M0.sub M1).mulV (walshSum M0 M1 v0 k (m / 2)) := by
  unfold walshSum
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [hpow, sumVec_even_odd]
  have heven : sumVec (2 ^ k) (fun i =>
      ((treeMat M0 M1 (k + 1) (2 * i)).mulV v0).smul (tmSign (bitAnd (2 * i) m))) =
      M0.mulV (sumVec (2 ^ k) (fun i =>
        ((treeMat M0 M1 k i).mulV v0).smul (tmSign (bitAnd i (m / 2))))) := by
    rw [← sumVec_mulV]
    apply sumVec_congr
    intro i _
    rw [treeMat_two_mul, Mat2.mul_mulV, bitAnd_two_mul_left, tmSign_two_mul, Mat2.mulV_smul]
  have hodd : sumVec (2 ^ k) (fun i =>
      ((treeMat M0 M1 (k + 1) (2 * i + 1)).mulV v0).smul (tmSign (bitAnd (2 * i + 1) m))) =
      (if m % 2 = 0 then
        M1.mulV (sumVec (2 ^ k) (fun i =>
          ((treeMat M0 M1 k i).mulV v0).smul (tmSign (bitAnd i (m / 2)))))
      else
        (M1.mulV (sumVec (2 ^ k) (fun i =>
          ((treeMat M0 M1 k i).mulV v0).smul (tmSign (bitAnd i (m / 2)))))).neg) := by
    by_cases hpar : m % 2 = 0
    · simp only [hpar, ↓reduceIte]
      rw [← sumVec_mulV]
      apply sumVec_congr
      intro i _
      rw [treeMat_two_mul_add_one, Mat2.mul_mulV, bitAnd_two_mul_add_one_left, hpar,
          Nat.zero_add, tmSign_two_mul, Mat2.mulV_smul]
    · have hm1 : m % 2 = 1 := by omega
      simp only [hpar, ↓reduceIte]
      have hneg_sum : ∀ u : Vec2, u.neg = u.smul (-1) := by
        intro u; cases u; simp [Vec2.neg, Vec2.smul]
      rw [hneg_sum, ← Mat2.mulV_smul, sumVec_smul, ← sumVec_mulV]
      apply sumVec_congr
      intro i _
      rw [treeMat_two_mul_add_one, Mat2.mul_mulV, bitAnd_two_mul_add_one_left, hm1]
      have h21 : 1 + 2 * bitAnd i (m / 2) = 2 * bitAnd i (m / 2) + 1 := by omega
      rw [h21, tmSign_two_mul_add_one, Mat2.mulV_smul, Mat2.mulV_smul]
      cases (M1.mulV ((treeMat M0 M1 k i).mulV v0))
      simp only [Vec2.smul, Vec2.mk.injEq]
      exact ⟨by grind, by grind⟩
  rw [heven, hodd]
  by_cases hpar : m % 2 = 0
  · simp only [hpar, ↓reduceIte, Mat2.add_mulV]
  · simp only [hpar, ↓reduceIte, Mat2.sub_mulV]
    cases (M0.mulV (sumVec (2 ^ k) (fun i => ((treeMat M0 M1 k i).mulV v0).smul (tmSign (bitAnd i (m / 2))))))
    cases (M1.mulV (sumVec (2 ^ k) (fun i => ((treeMat M0 M1 k i).mulV v0).smul (tmSign (bitAnd i (m / 2))))))
    simp only [Vec2.add, Vec2.sub, Vec2.neg, Vec2.mk.injEq]
    exact ⟨by omega, by omega⟩

theorem popcount_le_popcount_or (m : Nat) : popcount m ≤ popcount (m ||| igray m) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    cases m with
    | zero => simp
    | succ m' =>
      rw [popcount_div2 (m' + 1), popcount_or_step (m' + 1)]
      have hlt : (m' + 1) / 2 < m' + 1 := by omega
      have hrec := ih _ hlt
      split <;> omega

theorem expPlus_step (k m : Nat) (hm : m < 2 ^ (k + 1)) :
    expPlus (k + 1) m =
      if m % 2 = 0 ∧ popcount (m / 2) % 2 = 0 then expPlus k (m / 2) + 1
      else expPlus k (m / 2) := by
  unfold expPlus
  rw [popcount_or_step]
  have hdiv : m / 2 < 2 ^ k := by
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    omega
  have hle := popcount_or_le k (m / 2) hdiv
  split <;> split <;> omega

theorem expMinus_step (m : Nat) :
    expMinus m =
      if m % 2 = 0 ∧ popcount (m / 2) % 2 = 1 then expMinus (m / 2) + 1
      else expMinus (m / 2) := by
  unfold expMinus
  rw [popcount_or_step, popcount_div2 m]
  have hle := popcount_le_popcount_or (m / 2)
  split <;> split <;> omega

/-- **REUSABLE INFINITE PROOF ENGINE I (Hadamard Monomialization Lifter):**
    Any finite 4-equation `HadamardCert` on `(M₀, M₁)` lifts to an exact closed-form
    Walsh-Hadamard spectrum for ALL levels `k ∈ ℕ` and ALL bitmasks `m < 2^k`. -/
theorem hadamard_monomial_lifter
    (M0 M1 : Mat2) (eP eM : Vec2) (lamP lamM mu : Int)
    (hcert : HadamardCert M0 M1 eP eM lamP lamM mu) :
    ∀ k m : Nat, m < 2 ^ k →
      walshSum M0 M1 eP k m =
        (rotBasis eP eM (popcount m)).smul
          (mu ^ (popcount m) * lamP ^ (expPlus k m) * lamM ^ (expMinus m)) := by
  intro k
  induction k with
  | zero =>
    intro m hm
    have hm0 : m = 0 := by omega
    subst hm0
    simp [walshSum, sumVec, Vec2.zero, Vec2.add, treeMat, Mat2.id, Mat2.mulV,
          rotBasis, expPlus, expMinus, Vec2.smul]
  | succ k ih =>
    intro m hm
    have hdiv : m / 2 < 2 ^ k := by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      omega
    rw [walshSum_succ, ih (m / 2) hdiv, Mat2.mulV_smul]
    by_cases hpar : m % 2 = 0
    · simp only [hpar, ↓reduceIte]
      have hpop : popcount m = popcount (m / 2) := by rw [popcount_div2, hpar]; omega
      rw [hpop]
      by_cases hp : popcount (m / 2) % 2 = 0
      · rw [rotBasis_add_even M0 M1 eP eM lamP lamM mu hcert _ hp]
        have heP : expPlus (k + 1) m = expPlus k (m / 2) + 1 := by
          rw [expPlus_step k m hm]; simp [hpar, hp]
        have heM : expMinus m = expMinus (m / 2) := by
          rw [expMinus_step m]; simp [hpar, hp]
        rw [heP, heM, Int.pow_succ]
        cases (rotBasis eP eM (popcount (m / 2)))
        simp only [Vec2.smul, Vec2.mk.injEq]
        exact ⟨by grind, by grind⟩
      · have hp1 : popcount (m / 2) % 2 = 1 := by omega
        rw [rotBasis_add_odd M0 M1 eP eM lamP lamM mu hcert _ hp1]
        have heP : expPlus (k + 1) m = expPlus k (m / 2) := by
          rw [expPlus_step k m hm]; simp [hpar, hp1]
        have heM : expMinus m = expMinus (m / 2) + 1 := by
          rw [expMinus_step m]; simp [hpar, hp1]
        rw [heP, heM, Int.pow_succ]
        cases (rotBasis eP eM (popcount (m / 2)))
        simp only [Vec2.smul, Vec2.mk.injEq]
        exact ⟨by grind, by grind⟩
    · have hm1 : m % 2 = 1 := by omega
      simp only [hpar, ↓reduceIte]
      have hpop : popcount m = popcount (m / 2) + 1 := by rw [popcount_div2, hm1]; omega
      rw [rotBasis_succ_sub M0 M1 eP eM lamP lamM mu hcert _]
      have heP : expPlus (k + 1) m = expPlus k (m / 2) := by
        rw [expPlus_step k m hm]; simp [hm1]
      have heM : expMinus m = expMinus (m / 2) := by
        rw [expMinus_step m]; simp [hm1]
      rw [hpop, heP, heM, Int.pow_succ]
      cases (rotBasis eP eM (popcount (m / 2) + 1))
      simp only [Vec2.smul, Vec2.mk.injEq]
      exact ⟨by grind, by grind⟩

theorem rotBasis_ePlus_x (p : Nat) : (rotBasis ePlus eMinus p).x = triSign p := by
  unfold rotBasis triSign ePlus eMinus
  have hmod : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · have htri : (p * (p + 1) / 2) % 2 = 0 := by
      let q := p / 4
      have hp : p = 4 * q := by omega
      rw [hp]
      have hmul : 4 * q * (4 * q + 1) / 2 = 2 * (q * (4 * q + 1)) := by
        have h2 : 4 * q * (4 * q + 1) = 2 * (2 * (q * (4 * q + 1))) := by grind
        rw [h2]; omega
      omega
    simp [h, htri]
  · have htri : (p * (p + 1) / 2) % 2 = 1 := by
      let q := p / 4
      have hp : p = 4 * q + 1 := by omega
      rw [hp]
      have hmul : (4 * q + 1) * (4 * q + 1 + 1) / 2 = (4 * q + 1) * (2 * q + 1) := by
        have h2 : (4 * q + 1) * (4 * q + 1 + 1) = 2 * ((4 * q + 1) * (2 * q + 1)) := by grind
        rw [h2]; omega
      rw [hmul]
      have hexp : (4 * q + 1) * (2 * q + 1) = 2 * (4 * q * q + 3 * q) + 1 := by grind
      omega
    simp [h, htri]
  · have htri : (p * (p + 1) / 2) % 2 = 1 := by
      let q := p / 4
      have hp : p = 4 * q + 2 := by omega
      rw [hp]
      have hmul : (4 * q + 2) * (4 * q + 2 + 1) / 2 = (2 * q + 1) * (4 * q + 3) := by
        have h2 : (4 * q + 2) * (4 * q + 2 + 1) = 2 * ((2 * q + 1) * (4 * q + 3)) := by grind
        rw [h2]; omega
      rw [hmul]
      have hexp : (2 * q + 1) * (4 * q + 3) = 2 * (4 * q * q + 5 * q + 1) + 1 := by grind
      omega
    simp [h, htri, Vec2.neg]
  · have htri : (p * (p + 1) / 2) % 2 = 0 := by
      let q := p / 4
      have hp : p = 4 * q + 3 := by omega
      rw [hp]
      have hmul : (4 * q + 3) * (4 * q + 3 + 1) / 2 = 2 * ((4 * q + 3) * (q + 1)) := by
        have h2 : (4 * q + 3) * (4 * q + 3 + 1) = 2 * (2 * ((4 * q + 3) * (q + 1))) := by grind
        rw [h2]; omega
      omega
    simp [h, htri, Vec2.neg]

/-- Constructive finite certificate witness for ALL parametric `a`-Stern trees! -/
theorem aStern_hadamardCert (a : Int) :
    HadamardCert (Lmat a) (Rmat a) ePlus eMinus (2 + a) (2 - a) a where
  add_plus  := by simp [Lmat, Rmat, Mat2.add, Mat2.mulV, ePlus, Vec2.smul]; omega
  add_minus := by simp [Lmat, Rmat, Mat2.add, Mat2.mulV, eMinus, Vec2.smul]; exact ⟨by omega, by omega⟩
  sub_plus  := by simp [Lmat, Rmat, Mat2.sub, Mat2.mulV, ePlus, eMinus, Vec2.smul]
  sub_minus := by simp [Lmat, Rmat, Mat2.sub, Mat2.mulV, ePlus, eMinus, Vec2.smul]

/-- **THEOREM 1A (Exact Walsh-Hadamard Spectrum of Stern's Diatomic Sequence):**
    For ALL `k ∈ ℕ` and ALL masks `m < 2^k`, EVERY Walsh-Hadamard coefficient of Stern's
    sequence at level `k` is a signed pure power of `3` governed by the inverse Gray code:
    `∑_{x < 2^k} (-1)^pop(x & m) * s(2^k + x) = (-1)^(pop(m)*(pop(m)+1)/2) * 3^(k - pop(m | igray m))`. -/
theorem stern_walsh_spectrum (k m : Nat) (hm : m < 2 ^ k) :
    sumInt (2 ^ k) (fun x => tmSign (x &&& m) * Int.ofNat (stern (2 ^ k + x))) =
      triSign (popcount m) * 3 ^ (k - popcount (m ||| igray m)) := by
  have h := hadamard_monomial_lifter (Lmat 1) (Rmat 1) ePlus eMinus 3 1 1
    (aStern_hadamardCert 1) k m hm
  have hx := congrArg Vec2.x h
  rw [walshSum, sumVec_x] at hx
  have hcongr : sumInt (2 ^ k) (fun x => (((treeMat (Lmat 1) (Rmat 1) k x).mulV ePlus).smul
      (tmSign (bitAnd x m))).x) =
      sumInt (2 ^ k) (fun x => tmSign (x &&& m) * Int.ofNat (stern (2 ^ k + x))) := by
    apply sumInt_congr
    intro x hxk
    have hbr := stern_cw_bridge k x hxk
    unfold cwVec cwMat at hbr
    rw [hbr, bitAnd_eq_land]
    rfl
  rw [hcongr] at hx
  rw [hx]
  simp only [Vec2.smul, rotBasis_ePlus_x, expPlus, Int.one_pow, Int.one_mul, Int.mul_one]
  rw [Int.mul_comm]

/-- **THEOREM 1B (Parametric `a`-Stern Walsh-Hadamard Spectrum):**
    For ALL `a ∈ ℤ`, `k ∈ ℕ`, and `m < 2^k`:
    `∑_{x < 2^k} (-1)^pop(x & m) * cwVec_x(a, k, x) = triSign(pop m) * a^(pop m) * (2+a)^(e_+) * (2-a)^(e_-)`. -/
theorem aStern_walsh_spectrum (a : Int) (k m : Nat) (hm : m < 2 ^ k) :
    (walshSum (Lmat a) (Rmat a) ePlus k m).x =
      a ^ (popcount m) * (2 + a) ^ (expPlus k m) * (2 - a) ^ (expMinus m) * triSign (popcount m) := by
  have h := hadamard_monomial_lifter (Lmat a) (Rmat a) ePlus eMinus (2 + a) (2 - a) a
    (aStern_hadamardCert a) k m hm
  have hx := congrArg Vec2.x h
  rw [hx]
  simp only [Vec2.smul, rotBasis_ePlus_x]

theorem int_pow_pos {a : Int} (ha : 0 < a) (n : Nat) : 0 < a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Int.pow_succ]; exact Int.mul_pos ih ha

/-- **THEOREM 1C (Exact Spectral Vanishing Criterion for `a = 2`):**
    At `a = 2`, the Walsh-Hadamard vector vanishes if and only if `expMinus m > 0`
    (equivalently, `popcount (m ||| igray m) > popcount m`). -/
theorem twoStern_walsh_vanishing (k m : Nat) (hm : m < 2 ^ k) :
    walshSum (Lmat 2) (Rmat 2) ePlus k m = Vec2.zero ↔ expMinus m > 0 := by
  have h := hadamard_monomial_lifter (Lmat 2) (Rmat 2) ePlus eMinus 4 0 2
    (aStern_hadamardCert 2) k m hm
  rw [h]
  constructor
  · intro hz
    cases hem : expMinus m with
    | succ e => omega
    | zero =>
      rw [hem] at hz
      have hpos : (2 : Int) ^ popcount m * 4 ^ expPlus k m * 0 ^ 0 > 0 := by
        have h1 : (0 : Int) < (2 : Int) ^ popcount m := int_pow_pos (by decide) _
        have h2 : (0 : Int) < (4 : Int) ^ expPlus k m := int_pow_pos (by decide) _
        have h3 : (0 : Int) ^ 0 = 1 := rfl
        rw [h3, Int.mul_one]
        exact Int.mul_pos h1 h2
      have hx := congrArg Vec2.x hz
      simp only [Vec2.smul, Vec2.zero, rotBasis_ePlus_x] at hx
      have hts : triSign (popcount m) = 1 ∨ triSign (popcount m) = -1 := by
        unfold triSign; split <;> simp
      rcases hts with hts | hts <;> rw [hts] at hx <;> omega
  · intro hgt
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : expMinus m ≠ 0)
    rw [he, Int.pow_succ]
    simp [Vec2.smul, Vec2.zero]

/-! ## Section 3: Reusable Infinite Proof Engine II — Carry-Transducer `ℤ⁸` Spectral-Orbit Lifter
    and the Mod-3 Carry-Shift Resonance & Oscillation Annihilation Theorem -/

/-- Orthogonal period-4 integer basis sequences `φ(k) = (1,-1,-1,1)[k%4]` and `ψ(k) = (1,1,-1,-1)[k%4]`. -/
def phi4 (k : Nat) : Int :=
  match k % 4 with
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | _ => 1

def psi4 (k : Nat) : Int :=
  match k % 4 with
  | 0 => 1
  | 1 => 1
  | 2 => -1
  | _ => -1

theorem phi4_succ (k : Nat) : phi4 (k + 1) = -psi4 k := by
  unfold phi4 psi4
  have h : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases h with h | h | h | h
  · have h1 : (k + 1) % 4 = 1 := by omega
    rw [h, h1]; rfl
  · have h1 : (k + 1) % 4 = 2 := by omega
    rw [h, h1]; rfl
  · have h1 : (k + 1) % 4 = 3 := by omega
    rw [h, h1]; rfl
  · have h1 : (k + 1) % 4 = 0 := by omega
    rw [h, h1]; rfl

theorem psi4_succ (k : Nat) : psi4 (k + 1) = phi4 k := by
  unfold phi4 psi4
  have h : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases h with h | h | h | h
  · have h1 : (k + 1) % 4 = 1 := by omega
    rw [h, h1]; rfl
  · have h1 : (k + 1) % 4 = 2 := by omega
    rw [h, h1]; rfl
  · have h1 : (k + 1) % 4 = 3 := by omega
    rw [h, h1]; rfl
  · have h1 : (k + 1) % 4 = 0 := by omega
    rw [h, h1]; rfl

theorem phi4_add4 (k : Nat) : phi4 (k + 4) = phi4 k := by simp [phi4]
theorem psi4_add4 (k : Nat) : psi4 (k + 4) = psi4 k := by simp [psi4]

theorem phi4_add2 (k : Nat) : phi4 (k + 2) = -phi4 k := by
  unfold phi4
  have h : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases h with h | h | h | h
  · have h2 : (k + 2) % 4 = 2 := by omega
    rw [h, h2]; rfl
  · have h2 : (k + 2) % 4 = 3 := by omega
    rw [h, h2]; rfl
  · have h2 : (k + 2) % 4 = 0 := by omega
    rw [h, h2]; rfl
  · have h2 : (k + 2) % 4 = 1 := by omega
    rw [h, h2]; rfl

theorem phi4_ne_zero (k : Nat) : phi4 k ≠ 0 := by
  unfold phi4
  have h : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases h with h | h | h | h <;> rw [h] <;> decide

/-- Finite 8-integer Spectral-Orbit Certificate representing an affine + period-4 sequence in `ℤ²`. -/
structure OrbitCert where
  a1 : Int
  b1 : Int
  p1 : Int
  q1 : Int
  a2 : Int
  b2 : Int
  p2 : Int
  q2 : Int
  deriving DecidableEq, Repr

/-- Evaluation of an `OrbitCert` at level `k ∈ ℕ`. -/
def evalOrbit (C : OrbitCert) (k : Nat) : Vec2 :=
  ⟨C.a1 * Int.ofNat k + C.b1 + C.p1 * phi4 k + C.q1 * psi4 k,
   C.a2 * Int.ofNat k + C.b2 + C.p2 * phi4 k + C.q2 * psi4 k⟩

/-- Exact `ℤ⁸` linear transition operator for even carry shifts `V_{2c}(k+1) = (L₁ - R₁) V_c(k)`. -/
def stepEven (C : OrbitCert) : OrbitCert :=
  ⟨-C.a2, C.a2 - C.b2, C.q2, -C.p2,
    C.a1, C.b1 - C.a1, -C.q1, C.p1⟩

/-- Exact `ℤ⁸` linear transition operator for odd carry shifts `V_{2c+1}(k+1) = -L₁ V_c(k) + R₁ V_{c+1}(k)`. -/
def stepOdd (U V : OrbitCert) : OrbitCert :=
  ⟨-U.a1 + V.a1 + V.a2,
   -(U.b1 - U.a1) + (V.b1 - V.a1) + (V.b2 - V.a2),
    U.q1 - V.q1 - V.q2,
   -U.p1 + V.p1 + V.p2,
   -U.a1 - U.a2 + V.a2,
   -(U.b1 - U.a1) - (U.b2 - U.a2) + (V.b2 - V.a2),
    U.q1 + U.q2 - V.q2,
   -U.p1 - U.p2 + V.p2⟩

theorem evalOrbit_stepEven (C : OrbitCert) (k : Nat) :
    evalOrbit (stepEven C) (k + 1) = (L1.sub R1).mulV (evalOrbit C k) := by
  cases C
  have hk : Int.ofNat (k + 1) = Int.ofNat k + 1 := ofNat_add k 1
  simp only [evalOrbit, stepEven, L1, R1, Lmat, Rmat, Mat2.sub, Mat2.mulV,
             phi4_succ, psi4_succ, hk, Vec2.mk.injEq]
  exact ⟨by grind, by grind⟩

theorem evalOrbit_stepOdd (U V : OrbitCert) (k : Nat) :
    evalOrbit (stepOdd U V) (k + 1) =
      (L1.mulV (evalOrbit U k)).neg.add (R1.mulV (evalOrbit V k)) := by
  cases U; cases V
  have hk : Int.ofNat (k + 1) = Int.ofNat k + 1 := ofNat_add k 1
  simp only [evalOrbit, stepOdd, L1, R1, Lmat, Rmat, Mat2.mulV, Vec2.neg, Vec2.add,
             phi4_succ, psi4_succ, hk, Vec2.mk.injEq]
  exact ⟨by grind, by grind⟩

/-- Binary-recursive compiler producing the exact finite `OrbitCert` for ANY carry shift `c ∈ ℕ`. -/
def compileCert (C0 C1 : OrbitCert) : Nat → OrbitCert
  | 0 => C0
  | 1 => C1
  | c + 2 =>
    if (c + 2) % 2 = 0 then
      stepEven (compileCert C0 C1 ((c + 2) / 2))
    else
      stepOdd (compileCert C0 C1 ((c + 2) / 2)) (compileCert C0 C1 ((c + 2) / 2 + 1))
termination_by c => c

@[simp] theorem compileCert_zero (C0 C1 : OrbitCert) : compileCert C0 C1 0 = C0 := by
  rw [compileCert]
@[simp] theorem compileCert_one (C0 C1 : OrbitCert) : compileCert C0 C1 1 = C1 := by
  rw [compileCert]

theorem compileCert_two_mul (C0 C1 : OrbitCert) (m : Nat) (hm : m ≥ 1) :
    compileCert C0 C1 (2 * m) = stepEven (compileCert C0 C1 m) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have h : 2 * (m' + 1) = 2 * m' + 2 := by omega
  rw [h]
  conv => lhs; rw [compileCert]
  have h1 : (2 * m' + 2) % 2 = 0 := by omega
  have h2 : (2 * m' + 2) / 2 = m' + 1 := by omega
  simp [h1, h2]

theorem compileCert_two_mul_add_one (C0 C1 : OrbitCert) (m : Nat) (hm : m ≥ 1) :
    compileCert C0 C1 (2 * m + 1) =
      stepOdd (compileCert C0 C1 m) (compileCert C0 C1 (m + 1)) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have h : 2 * (m' + 1) + 1 = (2 * m' + 1) + 2 := by omega
  rw [h]
  conv => lhs; rw [compileCert]
  have h1 : (2 * m' + 1 + 2) % 2 = 1 := by omega
  have h2 : (2 * m' + 1 + 2) / 2 = m' + 1 := by omega
  simp [h1, h2]

/-- **REUSABLE INFINITE PROOF ENGINE II (Carry-Transducer `ℤ⁸` Spectral-Orbit Lifter):**
    Any family `V : ℕ → ℕ → Vec2` obeying the binary carry-transducer recursion and matching
    finite base certificates `C₀, C₁` at `c = 0, 1` is EXACTLY given by `evalOrbit (compileCert C₀ C₁ c) k`
    for ALL `c ∈ ℕ` and ALL `k ∈ ℕ` with `2^k ≥ c`! -/
theorem carry_orbit_lifter
    (V : Nat → Nat → Vec2) (C0 C1 : OrbitCert)
    (h0 : ∀ k, V 0 k = evalOrbit C0 k)
    (h1 : ∀ k, V 1 k = evalOrbit C1 k)
    (heven : ∀ c k, V (2 * c) (k + 1) = (L1.sub R1).mulV (V c k))
    (hodd : ∀ c k, V (2 * c + 1) (k + 1) = (L1.mulV (V c k)).neg.add (R1.mulV (V (c + 1) k))) :
    ∀ c k : Nat, 2 ^ k ≥ c → V c k = evalOrbit (compileCert C0 C1 c) k := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro k hk
    match c with
    | 0 => rw [compileCert_zero]; exact h0 k
    | 1 => rw [compileCert_one]; exact h1 k
    | n + 2 =>
      have hk_pos : k ≥ 1 := by
        cases k with
        | zero => simp at hk
        | succ _ => omega
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hpow : 2 ^ (k' + 1) = 2 * 2 ^ k' := by rw [Nat.pow_succ]; omega
      by_cases hpar : (n + 2) % 2 = 0
      · let m := (n + 2) / 2
        have hm1 : m ≥ 1 := by omega
        have heq : n + 2 = 2 * m := by omega
        have hlt : m < n + 2 := by omega
        have hkm : 2 ^ k' ≥ m := by omega
        rw [heq, heven m k', ih m hlt k' hkm, compileCert_two_mul C0 C1 m hm1, evalOrbit_stepEven]
      · let m := (n + 2) / 2
        have hm1 : m ≥ 1 := by omega
        have heq : n + 2 = 2 * m + 1 := by omega
        have hlt1 : m < n + 2 := by omega
        have hlt2 : m + 1 < n + 2 := by omega
        have hkm1 : 2 ^ k' ≥ m := by omega
        have hkm2 : 2 ^ k' ≥ m + 1 := by omega
        rw [heq, hodd m k', ih m hlt1 k' hkm1, ih (m + 1) hlt2 k' hkm2,
            compileCert_two_mul_add_one C0 C1 m hm1, evalOrbit_stepOdd]

theorem carrySternF_eq_sum (c k : Nat) :
    carrySternF c k = sumInt (2 ^ k) (fun x => tmSign (x + c) * Int.ofNat (stern (2 ^ k + x))) := by
  unfold carrySternF carrySternVec
  rw [sumVec_x]
  apply sumInt_congr
  intro x hx
  rw [stern_cw_bridge k x hx]
  rfl

theorem carrySternG_eq_sum (c k : Nat) :
    carrySternG c k = sumInt (2 ^ k) (fun x => tmSign (x + c) * Int.ofNat (stern (2 ^ k + x + 1))) := by
  unfold carrySternG carrySternVec
  rw [sumVec_y]
  apply sumInt_congr
  intro x hx
  rw [stern_cw_bridge k x hx]
  rfl

theorem carrySternVec_even (c k : Nat) :
    carrySternVec (2 * c) (k + 1) = (L1.sub R1).mulV (carrySternVec c k) := by
  unfold carrySternVec
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [hpow, sumVec_even_odd]
  have he : sumVec (2 ^ k) (fun i => (cwVec 1 (k + 1) (2 * i)).smul (tmSign (2 * i + 2 * c))) =
      L1.mulV (sumVec (2 ^ k) (fun i => (cwVec 1 k i).smul (tmSign (i + c)))) := by
    rw [← sumVec_mulV]
    apply sumVec_congr
    intro i _
    have h2 : 2 * i + 2 * c = 2 * (i + c) := by omega
    rw [h2, tmSign_two_mul]
    unfold cwVec cwMat
    rw [treeMat_two_mul, Mat2.mul_mulV, Mat2.mulV_smul]
    rfl
  have ho : sumVec (2 ^ k) (fun i => (cwVec 1 (k + 1) (2 * i + 1)).smul (tmSign (2 * i + 1 + 2 * c))) =
      (R1.mulV (sumVec (2 ^ k) (fun i => (cwVec 1 k i).smul (tmSign (i + c))))).neg := by
    have hneg_s : ∀ u : Vec2, u.neg = u.smul (-1) := by intro u; cases u; simp [Vec2.neg, Vec2.smul]
    rw [hneg_s, ← Mat2.mulV_smul, sumVec_smul, ← sumVec_mulV]
    apply sumVec_congr
    intro i _
    have h21 : 2 * i + 1 + 2 * c = 2 * (i + c) + 1 := by omega
    rw [h21, tmSign_two_mul_add_one]
    unfold cwVec cwMat
    rw [treeMat_two_mul_add_one, Mat2.mul_mulV, Mat2.mulV_smul, Mat2.mulV_smul]
    change ((R1.mulV ((treeMat (Lmat 1) (Rmat 1) k i).mulV ePlus)).smul (-tmSign (i + c))) =
           ((R1.mulV ((treeMat (Lmat 1) (Rmat 1) k i).mulV ePlus)).smul (tmSign (i + c))).smul (-1)
    cases (R1.mulV ((treeMat (Lmat 1) (Rmat 1) k i).mulV ePlus))
    simp only [Vec2.smul, Vec2.mk.injEq]
    exact ⟨by grind, by grind⟩
  rw [he, ho, Mat2.sub_mulV]
  cases (L1.mulV (sumVec (2 ^ k) (fun i => (cwVec 1 k i).smul (tmSign (i + c)))))
  cases (R1.mulV (sumVec (2 ^ k) (fun i => (cwVec 1 k i).smul (tmSign (i + c)))))
  simp only [Vec2.add, Vec2.sub, Vec2.neg, Vec2.mk.injEq]
  exact ⟨by omega, by omega⟩

theorem carrySternVec_odd (c k : Nat) :
    carrySternVec (2 * c + 1) (k + 1) =
      (L1.mulV (carrySternVec c k)).neg.add (R1.mulV (carrySternVec (c + 1) k)) := by
  unfold carrySternVec
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [hpow, sumVec_even_odd]
  have he : sumVec (2 ^ k) (fun i => (cwVec 1 (k + 1) (2 * i)).smul (tmSign (2 * i + (2 * c + 1)))) =
      (L1.mulV (sumVec (2 ^ k) (fun i => (cwVec 1 k i).smul (tmSign (i + c))))).neg := by
    have hneg_s : ∀ u : Vec2, u.neg = u.smul (-1) := by intro u; cases u; simp [Vec2.neg, Vec2.smul]
    rw [hneg_s, ← Mat2.mulV_smul, sumVec_smul, ← sumVec_mulV]
    apply sumVec_congr
    intro i _
    have h21 : 2 * i + (2 * c + 1) = 2 * (i + c) + 1 := by omega
    rw [h21, tmSign_two_mul_add_one]
    unfold cwVec cwMat
    rw [treeMat_two_mul, Mat2.mul_mulV, Mat2.mulV_smul, Mat2.mulV_smul]
    change ((L1.mulV ((treeMat (Lmat 1) (Rmat 1) k i).mulV ePlus)).smul (-tmSign (i + c))) =
           ((L1.mulV ((treeMat (Lmat 1) (Rmat 1) k i).mulV ePlus)).smul (tmSign (i + c))).smul (-1)
    cases (L1.mulV ((treeMat (Lmat 1) (Rmat 1) k i).mulV ePlus))
    simp only [Vec2.smul, Vec2.mk.injEq]
    exact ⟨by grind, by grind⟩
  have ho : sumVec (2 ^ k) (fun i => (cwVec 1 (k + 1) (2 * i + 1)).smul (tmSign (2 * i + 1 + (2 * c + 1)))) =
      R1.mulV (sumVec (2 ^ k) (fun i => (cwVec 1 k i).smul (tmSign (i + (c + 1))))) := by
    rw [← sumVec_mulV]
    apply sumVec_congr
    intro i _
    have h2 : 2 * i + 1 + (2 * c + 1) = 2 * (i + (c + 1)) := by omega
    rw [h2, tmSign_two_mul]
    unfold cwVec cwMat
    rw [treeMat_two_mul_add_one, Mat2.mul_mulV, Mat2.mulV_smul]
    rfl
  rw [he, ho]

def baseCert0 : OrbitCert := ⟨0, 0, 1, 0, 0, 0, 0, 1⟩
def baseCert1 : OrbitCert := ⟨-2, -1, 0, 0, 0, -2, 1, 0⟩
def sternCert (c : Nat) : OrbitCert := compileCert baseCert0 baseCert1 c

theorem carrySternVec_zero_eval (k : Nat) :
    carrySternVec 0 k = evalOrbit baseCert0 k := by
  induction k with
  | zero =>
    simp [carrySternVec, sumVec, Vec2.zero, Vec2.add, cwVec, cwMat, treeMat, Mat2.id,
          Mat2.mulV, ePlus, Vec2.smul, evalOrbit, baseCert0, phi4, psi4]
  | succ k ih =>
    have h0 := carrySternVec_even 0 k
    simp only [Nat.mul_zero] at h0
    rw [h0, ih, ← evalOrbit_stepEven]
    rfl

theorem carrySternVec_one_eval (k : Nat) :
    carrySternVec 1 k = evalOrbit baseCert1 k := by
  induction k with
  | zero =>
    simp [carrySternVec, sumVec, Vec2.zero, Vec2.add, cwVec, cwMat, treeMat, Mat2.id,
          Mat2.mulV, ePlus, Vec2.smul, evalOrbit, baseCert1, phi4, psi4]
  | succ k ih =>
    have h1 := carrySternVec_odd 0 k
    simp only [Nat.mul_zero, Nat.zero_add] at h1
    rw [h1, carrySternVec_zero_eval k, ih, ← evalOrbit_stepOdd]
    rfl

/-- **Exact Evaluation of Carry-Shifted Thue-Morse Stern Sums via the `ℤ⁸` Engine:**
    For ALL `c ∈ ℕ` and ALL `k ∈ ℕ` with `2^k ≥ c`, `carrySternVec c k = evalOrbit (sternCert c) k`. -/
theorem carrySternVec_exact (c k : Nat) (hk : 2 ^ k ≥ c) :
    carrySternVec c k = evalOrbit (sternCert c) k :=
  carry_orbit_lifter carrySternVec baseCert0 baseCert1
    carrySternVec_zero_eval carrySternVec_one_eval
    carrySternVec_even carrySternVec_odd c k hk

/-- The 2-automatic oscillation-sign pair `(A_q, B_q) ∈ {-1, +1}²` governing the period-4 phase
    of `sternCert (3q + r)` across all `q ∈ ℕ`. -/
def oscAB : Nat → Int × Int
  | 0 => (1, 1)
  | 1 => (1, -1)
  | q + 2 =>
    if (q + 2) % 2 = 0 then
      let p := oscAB ((q + 2) / 2)
      (p.2, p.1)
    else
      let p1 := oscAB ((q + 2) / 2)
      let p2 := oscAB ((q + 2) / 2 + 1)
      (-p2.2, -p1.1)
termination_by q => q

def oscA (q : Nat) : Int := (oscAB q).1
def oscB (q : Nat) : Int := (oscAB q).2

@[simp] theorem oscAB_zero : oscAB 0 = (1, 1) := by rw [oscAB]
@[simp] theorem oscAB_one : oscAB 1 = (1, -1) := by rw [oscAB]
@[simp] theorem oscA_zero : oscA 0 = 1 := by simp [oscA]
@[simp] theorem oscB_zero : oscB 0 = 1 := by simp [oscB]
@[simp] theorem oscA_one : oscA 1 = 1 := by simp [oscA]
@[simp] theorem oscB_one : oscB 1 = -1 := by simp [oscB]

theorem oscAB_two_mul (q : Nat) : oscAB (2 * q) = (oscB q, oscA q) := by
  cases q with
  | zero => simp [oscA, oscB]
  | succ k =>
    have h : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h]
    conv => lhs; rw [oscAB]
    have h1 : (2 * k + 2) % 2 = 0 := by omega
    have h2 : (2 * k + 2) / 2 = k + 1 := by omega
    simp [h1, h2, oscA, oscB]

theorem oscAB_two_mul_add_one (q : Nat) : oscAB (2 * q + 1) = (-oscB (q + 1), -oscA q) := by
  cases q with
  | zero => simp [oscA, oscB]
  | succ k =>
    have h : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [h]
    conv => lhs; rw [oscAB]
    have h1 : (2 * k + 1 + 2) % 2 = 1 := by omega
    have h2 : (2 * k + 1 + 2) / 2 = k + 1 := by omega
    simp [h1, h2, oscA, oscB]

theorem oscA_two_mul (q : Nat) : oscA (2 * q) = oscB q := by simp [oscA, oscAB_two_mul]
theorem oscB_two_mul (q : Nat) : oscB (2 * q) = oscA q := by simp [oscB, oscAB_two_mul]
theorem oscA_two_mul_add_one (q : Nat) : oscA (2 * q + 1) = -oscB (q + 1) := by
  simp [oscA, oscAB_two_mul_add_one]
theorem oscB_two_mul_add_one (q : Nat) : oscB (2 * q + 1) = -oscA q := by
  simp [oscB, oscAB_two_mul_add_one]

theorem oscAB_pm1 (q : Nat) : (oscA q = 1 ∨ oscA q = -1) ∧ (oscB q = 1 ∨ oscB q = -1) := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
    match q with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      by_cases hpar : (k + 2) % 2 = 0
      · let m := (k + 2) / 2
        have hm : k + 2 = 2 * m := by omega
        have ihm := ih m (by omega)
        rw [hm, oscA_two_mul, oscB_two_mul]
        exact ⟨ihm.2, ihm.1⟩
      · let m := (k + 2) / 2
        have hm : k + 2 = 2 * m + 1 := by omega
        have ih1 := ih m (by omega)
        have ih2 := ih (m + 1) (by omega)
        rw [hm, oscA_two_mul_add_one, oscB_two_mul_add_one]
        constructor
        · rcases ih2.2 with h | h <;> rw [h] <;> simp
        · rcases ih1.1 with h | h <;> rw [h] <;> simp

/-- Structural mod-3 specification of the slope and oscillation components of `sternCert c`. -/
def Mod3Spec (c : Nat) : Prop :=
  match c % 3 with
  | 0 => (sternCert c).a1 = 0 ∧ (sternCert c).a2 = 0 ∧
         (sternCert c).p1 = oscA (c / 3) ∧ (sternCert c).q1 = 0 ∧
         (sternCert c).p2 = 0 ∧ (sternCert c).q2 = oscB (c / 3)
  | 1 => (sternCert c).a1 = -2 * tmSign (c / 3) ∧ (sternCert c).a2 = 0 ∧
         (sternCert c).p1 = 0 ∧ (sternCert c).q1 = 0 ∧
         (sternCert c).p2 = oscA (c / 3) ∧ (sternCert c).q2 = 0
  | _ => (sternCert c).a1 = 0 ∧ (sternCert c).a2 = -2 * tmSign (c / 3) ∧
         (sternCert c).p1 = 0 ∧ (sternCert c).q1 = oscB (c / 3 + 1) ∧
         (sternCert c).p2 = 0 ∧ (sternCert c).q2 = 0

/-- **MASTER MOD-3 INVARIANT THEOREM:**
    Every compiled carry-shift certificate `sternCert c` satisfies `Mod3Spec c` for ALL `c ∈ ℕ`.
    Proved by 6-class mod-6 strong induction directly on the `ℤ⁸` operators `stepEven` and `stepOdd`. -/
theorem sternCert_mod3_spec (c : Nat) : Mod3Spec c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    match c with
    | 0 => simp [Mod3Spec, sternCert, baseCert0]
    | 1 => simp [Mod3Spec, sternCert, baseCert1]
    | 2 =>
      have hsc2 : sternCert 2 = stepEven baseCert1 := by
        have h := compileCert_two_mul baseCert0 baseCert1 1 (by omega)
        simpa [sternCert] using h
      simp [Mod3Spec, hsc2, stepEven, baseCert1]
    | n + 3 =>
      have hr : (n + 3) % 6 = 0 ∨ (n + 3) % 6 = 1 ∨ (n + 3) % 6 = 2 ∨
                (n + 3) % 6 = 3 ∨ (n + 3) % 6 = 4 ∨ (n + 3) % 6 = 5 := by omega
      rcases hr with hr | hr | hr | hr | hr | hr
      · -- Case c = 6q = 2 * (3q), q ≥ 1
        let q := (n + 3) / 6
        have hc : n + 3 = 2 * (3 * q) := by omega
        have ih1 := ih (3 * q) (by omega)
        simp only [Mod3Spec, Nat.mul_mod_right, Nat.mul_div_cancel_left q (by decide : 0 < 3)] at ih1
        rcases ih1 with ⟨ha1, ha2, hp1, hq1', hp2, hq2⟩
        have hcert : sternCert (n + 3) = stepEven (sternCert (3 * q)) := by
          rw [hc]; exact compileCert_two_mul baseCert0 baseCert1 (3 * q) (by omega)
        have hmod3 : (n + 3) % 3 = 0 := by omega
        have hdiv3 : (n + 3) / 3 = 2 * q := by omega
        simp only [Mod3Spec, hmod3, hdiv3, hcert, stepEven, ha1, ha2, hp1, hq1', hp2, hq2,
                   oscA_two_mul, oscB_two_mul]
        simp
      · -- Case c = 6q + 1 = 2 * (3q) + 1, q ≥ 1
        let q := (n + 3) / 6
        have hc : n + 3 = 2 * (3 * q) + 1 := by omega
        have ih1 := ih (3 * q) (by omega)
        have ih2 := ih (3 * q + 1) (by omega)
        simp only [Mod3Spec, Nat.mul_mod_right, Nat.mul_div_cancel_left q (by decide : 0 < 3)] at ih1
        have hmod1 : (3 * q + 1) % 3 = 1 := by omega
        have hdiv1 : (3 * q + 1) / 3 = q := by omega
        simp only [Mod3Spec, hmod1, hdiv1] at ih2
        rcases ih1 with ⟨ua1, ua2, up1, uq1, up2, uq2⟩
        rcases ih2 with ⟨va1, va2, vp1, vq1, vp2, vq2⟩
        have hcert : sternCert (n + 3) = stepOdd (sternCert (3 * q)) (sternCert (3 * q + 1)) := by
          rw [hc]; exact compileCert_two_mul_add_one baseCert0 baseCert1 (3 * q) (by omega)
        have hmod3 : (n + 3) % 3 = 1 := by omega
        have hdiv3 : (n + 3) / 3 = 2 * q := by omega
        simp only [Mod3Spec, hmod3, hdiv3, hcert, stepOdd,
                   ua1, ua2, up1, uq1, up2, uq2, va1, va2, vp1, vq1, vp2, vq2,
                   tmSign_two_mul, oscA_two_mul]
        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · -- Case c = 6q + 2 = 2 * (3q + 1), q ≥ 1
        let q := (n + 3) / 6
        have hc : n + 3 = 2 * (3 * q + 1) := by omega
        have ih1 := ih (3 * q + 1) (by omega)
        have hmod1 : (3 * q + 1) % 3 = 1 := by omega
        have hdiv1 : (3 * q + 1) / 3 = q := by omega
        simp only [Mod3Spec, hmod1, hdiv1] at ih1
        rcases ih1 with ⟨ha1, ha2, hp1, hq1', hp2, hq2⟩
        have hcert : sternCert (n + 3) = stepEven (sternCert (3 * q + 1)) := by
          rw [hc]; exact compileCert_two_mul baseCert0 baseCert1 (3 * q + 1) (by omega)
        have hmod3 : (n + 3) % 3 = 2 := by omega
        have hdiv3 : (n + 3) / 3 = 2 * q := by omega
        simp only [Mod3Spec, hmod3, hdiv3, hcert, stepEven, ha1, ha2, hp1, hq1', hp2, hq2,
                   tmSign_two_mul, oscB_two_mul_add_one]
        simp
      · -- Case c = 6q + 3 = 2 * (3q + 1) + 1
        let q := (n + 3) / 6
        have hc : n + 3 = 2 * (3 * q + 1) + 1 := by omega
        have ih1 := ih (3 * q + 1) (by omega)
        have ih2 := ih (3 * q + 2) (by omega)
        have hmod1 : (3 * q + 1) % 3 = 1 := by omega
        have hdiv1 : (3 * q + 1) / 3 = q := by omega
        have hmod2 : (3 * q + 2) % 3 = 2 := by omega
        have hdiv2 : (3 * q + 2) / 3 = q := by omega
        simp only [Mod3Spec, hmod1, hdiv1] at ih1
        simp only [Mod3Spec, hmod2, hdiv2] at ih2
        rcases ih1 with ⟨ua1, ua2, up1, uq1, up2, uq2⟩
        rcases ih2 with ⟨va1, va2, vp1, vq1, vp2, vq2⟩
        have hcert : sternCert (n + 3) = stepOdd (sternCert (3 * q + 1)) (sternCert (3 * q + 2)) := by
          rw [hc]; exact compileCert_two_mul_add_one baseCert0 baseCert1 (3 * q + 1) (by omega)
        have hmod3 : (n + 3) % 3 = 0 := by omega
        have hdiv3 : (n + 3) / 3 = 2 * q + 1 := by omega
        simp only [Mod3Spec, hmod3, hdiv3, hcert, stepOdd,
                   ua1, ua2, up1, uq1, up2, uq2, va1, va2, vp1, vq1, vp2, vq2,
                   oscA_two_mul_add_one, oscB_two_mul_add_one]
        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · -- Case c = 6q + 4 = 2 * (3q + 2)
        let q := (n + 3) / 6
        have hc : n + 3 = 2 * (3 * q + 2) := by omega
        have ih1 := ih (3 * q + 2) (by omega)
        have hmod2 : (3 * q + 2) % 3 = 2 := by omega
        have hdiv2 : (3 * q + 2) / 3 = q := by omega
        simp only [Mod3Spec, hmod2, hdiv2] at ih1
        rcases ih1 with ⟨ha1, ha2, hp1, hq1', hp2, hq2⟩
        have hcert : sternCert (n + 3) = stepEven (sternCert (3 * q + 2)) := by
          rw [hc]; exact compileCert_two_mul baseCert0 baseCert1 (3 * q + 2) (by omega)
        have hmod3 : (n + 3) % 3 = 1 := by omega
        have hdiv3 : (n + 3) / 3 = 2 * q + 1 := by omega
        simp only [Mod3Spec, hmod3, hdiv3, hcert, stepEven, ha1, ha2, hp1, hq1', hp2, hq2,
                   tmSign_two_mul_add_one, oscA_two_mul_add_one]
        simp; omega
      · -- Case c = 6q + 5 = 2 * (3q + 2) + 1
        let q := (n + 3) / 6
        have hc : n + 3 = 2 * (3 * q + 2) + 1 := by omega
        have ih1 := ih (3 * q + 2) (by omega)
        have ih2 := ih (3 * q + 3) (by omega)
        have hmod2 : (3 * q + 2) % 3 = 2 := by omega
        have hdiv2 : (3 * q + 2) / 3 = q := by omega
        have hmod0 : (3 * q + 3) % 3 = 0 := by omega
        have hdiv0 : (3 * q + 3) / 3 = q + 1 := by omega
        simp only [Mod3Spec, hmod2, hdiv2] at ih1
        simp only [Mod3Spec, hmod0, hdiv0] at ih2
        rcases ih1 with ⟨ua1, ua2, up1, uq1, up2, uq2⟩
        rcases ih2 with ⟨va1, va2, vp1, vq1, vp2, vq2⟩
        have hcert : sternCert (n + 3) = stepOdd (sternCert (3 * q + 2)) (sternCert (3 * q + 3)) := by
          rw [hc]; exact compileCert_two_mul_add_one baseCert0 baseCert1 (3 * q + 2) (by omega)
        have hmod3 : (n + 3) % 3 = 2 := by omega
        have hdiv3 : (n + 3) / 3 = 2 * q + 1 := by omega
        have h2q2 : 2 * q + 1 + 1 = 2 * (q + 1) := by omega
        simp only [Mod3Spec, hmod3, hdiv3, h2q2, hcert, stepOdd,
                   ua1, ua2, up1, uq1, up2, uq2, va1, va2, vp1, vq1, vp2, vq2,
                   tmSign_two_mul_add_one, oscB_two_mul]
        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **THEOREM 2A (Mod-3 Carry-Shift Resonance — Class `c = 3q`):**
    For ALL `q, k ∈ ℕ` with `2^k ≥ 3q`, BOTH `F_{3q}(k)` and `G_{3q}(k)` have ZERO linear drift
    and satisfy strict period-4 conservation (`F(k+4)=F(k), G(k+4)=G(k)`), AND `F_{3q}` is strictly
    non-constant (`F_{3q}(k+2) ≠ F_{3q}(k)`). -/
theorem carryStern_mod0_periodic (q k : Nat) (hk : 2 ^ k ≥ 3 * q) :
    carrySternF (3 * q) (k + 4) = carrySternF (3 * q) k ∧
    carrySternG (3 * q) (k + 4) = carrySternG (3 * q) k ∧
    carrySternF (3 * q) (k + 2) ≠ carrySternF (3 * q) k := by
  have hk2 : 2 ^ (k + 2) ≥ 3 * q := by
    have : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [Nat.pow_succ, Nat.pow_succ]; omega
    omega
  have hk4 : 2 ^ (k + 4) ≥ 3 * q := by
    have : 2 ^ (k + 4) = 16 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega
    omega
  have hspec := sternCert_mod3_spec (3 * q)
  simp only [Mod3Spec, Nat.mul_mod_right, Nat.mul_div_cancel_left q (by decide : 0 < 3)] at hspec
  rcases hspec with ⟨ha1, ha2, hp1, hq1, hp2, hq2⟩
  have ek := carrySternVec_exact (3 * q) k hk
  have ek2 := carrySternVec_exact (3 * q) (k + 2) hk2
  have ek4 := carrySternVec_exact (3 * q) (k + 4) hk4
  unfold carrySternF carrySternG
  rw [ek, ek2, ek4]
  simp only [evalOrbit, ha1, ha2, hp1, hq1, hp2, hq2, phi4_add4, psi4_add4, phi4_add2]
  refine ⟨by omega, by omega, ?_⟩
  intro heq
  have hpm := (oscAB_pm1 q).1
  have hphi := phi4_ne_zero k
  rcases hpm with h | h <;> rw [h] at heq <;> omega

/-- **THEOREM 2B (Mod-3 Carry-Shift Resonance — Class `c = 3q + 1`):**
    For ALL `q, k ∈ ℕ` with `2^k ≥ 3q + 1`:
    1. COMPLETE period-4 oscillation annihilation in `F`: `F_{3q+1}(k)` is an EXACT affine arithmetic
       progression with Thue-Morse slope `F_{3q+1}(k+1) - F_{3q+1}(k) = -2 * (-1)^pop(q)`.
    2. Strict period-4 conservation in `G`: `G_{3q+1}(k+4) = G_{3q+1}(k)`. -/
theorem carryStern_mod1_affine (q k : Nat) (hk : 2 ^ k ≥ 3 * q + 1) :
    carrySternF (3 * q + 1) (k + 1) - carrySternF (3 * q + 1) k = -2 * tmSign q ∧
    carrySternG (3 * q + 1) (k + 4) = carrySternG (3 * q + 1) k := by
  have hk1 : 2 ^ (k + 1) ≥ 3 * q + 1 := by rw [Nat.pow_succ]; omega
  have hk4 : 2 ^ (k + 4) ≥ 3 * q + 1 := by
    have : 2 ^ (k + 4) = 16 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega
    omega
  have hspec := sternCert_mod3_spec (3 * q + 1)
  have hmod : (3 * q + 1) % 3 = 1 := by omega
  have hdiv : (3 * q + 1) / 3 = q := by omega
  simp only [Mod3Spec, hmod, hdiv] at hspec
  rcases hspec with ⟨ha1, ha2, hp1, hq1, hp2, hq2⟩
  have ek := carrySternVec_exact (3 * q + 1) k hk
  have ek1 := carrySternVec_exact (3 * q + 1) (k + 1) hk1
  have ek4 := carrySternVec_exact (3 * q + 1) (k + 4) hk4
  have hks : Int.ofNat (k + 1) = Int.ofNat k + 1 := ofNat_add k 1
  unfold carrySternF carrySternG
  rw [ek, ek1, ek4]
  simp only [evalOrbit, ha1, ha2, hp1, hq1, hp2, hq2, phi4_add4, hks]
  exact ⟨by grind, by omega⟩

/-- **THEOREM 2C (Mod-3 Carry-Shift Resonance — Class `c = 3q + 2`):**
    Exact mirror dual of Theorem 2B: for ALL `q, k ∈ ℕ` with `2^k ≥ 3q + 2`:
    1. Strict period-4 conservation in `F`: `F_{3q+2}(k+4) = F_{3q+2}(k)`.
    2. COMPLETE period-4 oscillation annihilation in `G`: `G_{3q+2}(k+1) - G_{3q+2}(k) = -2 * (-1)^pop(q)`. -/
theorem carryStern_mod2_affine_dual (q k : Nat) (hk : 2 ^ k ≥ 3 * q + 2) :
    carrySternF (3 * q + 2) (k + 4) = carrySternF (3 * q + 2) k ∧
    carrySternG (3 * q + 2) (k + 1) - carrySternG (3 * q + 2) k = -2 * tmSign q := by
  have hk1 : 2 ^ (k + 1) ≥ 3 * q + 2 := by rw [Nat.pow_succ]; omega
  have hk4 : 2 ^ (k + 4) ≥ 3 * q + 2 := by
    have : 2 ^ (k + 4) = 16 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega
    omega
  have hspec := sternCert_mod3_spec (3 * q + 2)
  have hmod : (3 * q + 2) % 3 = 2 := by omega
  have hdiv : (3 * q + 2) / 3 = q := by omega
  simp only [Mod3Spec, hmod, hdiv] at hspec
  rcases hspec with ⟨ha1, ha2, hp1, hq1, hp2, hq2⟩
  have ek := carrySternVec_exact (3 * q + 2) k hk
  have ek1 := carrySternVec_exact (3 * q + 2) (k + 1) hk1
  have ek4 := carrySternVec_exact (3 * q + 2) (k + 4) hk4
  have hks : Int.ofNat (k + 1) = Int.ofNat k + 1 := ofNat_add k 1
  unfold carrySternF carrySternG
  rw [ek, ek1, ek4]
  simp only [evalOrbit, ha1, ha2, hp1, hq1, hp2, hq2, psi4_add4, hks]
  exact ⟨by omega, by grind⟩

def Mat3.iter (M : Mat3) : Nat → Vec3 → Vec3
  | 0, v => v
  | k + 1, v => M.mulV (M.iter k v)

theorem Mat3.mulV_add (M : Mat3) (u v : Vec3) :
    M.mulV (u.add v) = (M.mulV u).add (M.mulV v) := by
  cases M with | mk r1 r2 r3 =>
  cases r1; cases r2; cases r3; cases u; cases v
  simp only [Mat3.mulV, Vec3.dot, Vec3.add, Vec3.mk.injEq]
  exact ⟨by grind, by grind, by grind⟩

theorem Mat3.mulV_smul (M : Mat3) (s : Int) (v : Vec3) :
    M.mulV (v.smul s) = (M.mulV v).smul s := by
  cases M with | mk r1 r2 r3 =>
  cases r1; cases r2; cases r3; cases v
  simp only [Mat3.mulV, Vec3.dot, Vec3.smul, Vec3.mk.injEq]
  exact ⟨by grind, by grind, by grind⟩

/-- Finite `3 × 3` spectral-collapse certificate: `M³ v = λ (M v)` and left-kernel `ℓ · (M v) = 0`. -/
structure Sym2CollapseCert (M : Mat3) (lam : Int) (ell : Vec3) : Prop where
  annihilator : ∀ v : Vec3, M.mulV (M.mulV (M.mulV v)) = (M.mulV v).smul lam
  left_kernel : ∀ v : Vec3, ell.dot (M.mulV v) = 0

/-- **REUSABLE INFINITE PROOF ENGINE III (`Sym²` Spectral-Collapse & Left-Kernel Conservation Lifter):**
    Any finite `Sym2CollapseCert` lifts to exact geometric scaling `M^(k+2) v₀ = λ • M^k v₀`
    and exact conservation `ℓ · (M^k v₀) = 0` for ALL `k ≥ 1`! -/
theorem sym2_collapse_lifter (M : Mat3) (lam : Int) (ell : Vec3)
    (hcert : Sym2CollapseCert M lam ell) (v0 : Vec3) :
    (∀ k : Nat, k ≥ 1 → M.iter (k + 2) v0 = (M.iter k v0).smul lam) ∧
    (∀ k : Nat, k ≥ 1 → ell.dot (M.iter k v0) = 0) := by
  constructor
  · intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [Mat3.iter]
    exact hcert.annihilator (M.iter k' v0)
  · intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [Mat3.iter]
    exact hcert.left_kernel (M.iter k' v0)

theorem sumVec3_even_odd (n : Nat) (f : Nat → Vec3) :
    sumVec3 (2 * n) f = (sumVec3 n (fun i => f (2 * i))).add (sumVec3 n (fun i => f (2 * i + 1))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [h2]; simp only [sumVec3]; rw [ih]
    cases (sumVec3 n (fun i => f (2 * i))); cases (sumVec3 n (fun i => f (2 * i + 1)))
    cases (f (2 * n)); cases (f (2 * n + 1))
    simp only [Vec3.add, Vec3.mk.injEq]
    exact ⟨by omega, by omega, by omega⟩

theorem sumVec3_mulV (M : Mat3) (n : Nat) (f : Nat → Vec3) :
    sumVec3 n (fun i => M.mulV (f i)) = M.mulV (sumVec3 n f) := by
  induction n with
  | zero => cases M with | mk r1 r2 r3 => cases r1; cases r2; cases r3; simp [sumVec3, Vec3.zero, Mat3.mulV, Vec3.dot]
  | succ n ih => simp [sumVec3, ih, Mat3.mulV_add]

theorem sumVec3_congr (n : Nat) (f g : Nat → Vec3) (h : ∀ i < n, f i = g i) :
    sumVec3 n f = sumVec3 n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumVec3]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

/-- The quadratic Thue-Morse Stern transfer matrix `M_quad = L^[2] - R^[2]`. -/
def Mquad : Mat3 :=
  ⟨⟨0, -2, -1⟩,
   ⟨1,  0, -1⟩,
   ⟨1,  2,  0⟩⟩

def ellQuad : Vec3 := ⟨1, -1, 1⟩

theorem Mquad_sym2_step (v : Vec2) :
    (vec2Sym2 (L1.mulV v)).add ((vec2Sym2 (R1.mulV v)).smul (-1)) = Mquad.mulV (vec2Sym2 v) := by
  cases v
  simp only [vec2Sym2, L1, R1, Lmat, Rmat, Mat2.mulV, Vec3.add, Vec3.smul, Mquad, Mat3.mulV, Vec3.dot,
             Vec3.mk.injEq]
  exact ⟨by grind, by grind, by grind⟩

theorem Mquad_cert : Sym2CollapseCert Mquad (-5) ellQuad where
  annihilator := by
    intro v; cases v
    simp only [Mquad, Mat3.mulV, Vec3.dot, Vec3.smul, Vec3.mk.injEq]
    exact ⟨by omega, by omega, by omega⟩
  left_kernel := by
    intro v; cases v
    simp [Mquad, ellQuad, Mat3.mulV, Vec3.dot]; omega

theorem quadSternVec_eq_iter (k : Nat) : quadSternVec k = Mquad.iter k ⟨1, 1, 1⟩ := by
  induction k with
  | zero =>
    simp [quadSternVec, sumVec3, Vec3.zero, Vec3.add, vec2Sym2, cwVec, cwMat, treeMat,
          Mat2.id, Mat2.mulV, ePlus, Vec3.smul, Mat3.iter]
  | succ k ih =>
    unfold quadSternVec
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [hpow, sumVec3_even_odd]
    have hcomb : (sumVec3 (2 ^ k) (fun i => (vec2Sym2 (cwVec 1 (k + 1) (2 * i))).smul (tmSign (2 * i)))).add
        (sumVec3 (2 ^ k) (fun i => (vec2Sym2 (cwVec 1 (k + 1) (2 * i + 1))).smul (tmSign (2 * i + 1)))) =
        sumVec3 (2 ^ k) (fun i => Mquad.mulV ((vec2Sym2 (cwVec 1 k i)).smul (tmSign i))) := by
      have hadd : ∀ n (f g : Nat → Vec3), (sumVec3 n f).add (sumVec3 n g) =
          sumVec3 n (fun i => (f i).add (g i)) := by
        intro n f g; induction n with
        | zero => rfl
        | succ n ih' =>
          simp only [sumVec3]; rw [← ih']
          cases (sumVec3 n f); cases (sumVec3 n g); cases (f n); cases (g n)
          simp only [Vec3.add, Vec3.mk.injEq]; exact ⟨by omega, by omega, by omega⟩
      rw [hadd]
      apply sumVec3_congr
      intro i _
      rw [tmSign_two_mul, tmSign_two_mul_add_one]
      have hL : cwVec 1 (k + 1) (2 * i) = L1.mulV (cwVec 1 k i) := by
        unfold cwVec cwMat; rw [treeMat_two_mul, Mat2.mul_mulV]; rfl
      have hR : cwVec 1 (k + 1) (2 * i + 1) = R1.mulV (cwVec 1 k i) := by
        unfold cwVec cwMat; rw [treeMat_two_mul_add_one, Mat2.mul_mulV]; rfl
      rw [hL, hR, Mat3.mulV_smul, ← Mquad_sym2_step]
      cases (vec2Sym2 (L1.mulV (cwVec 1 k i)))
      cases (vec2Sym2 (R1.mulV (cwVec 1 k i)))
      simp only [Vec3.add, Vec3.smul, Vec3.mk.injEq]
      exact ⟨by grind, by grind, by grind⟩
    rw [hcomb, sumVec3_mulV]
    change Mquad.mulV (quadSternVec k) = Mquad.iter (k + 1) ⟨1, 1, 1⟩
    rw [ih]; rfl

/-- **THEOREM 3A (Exact Quadratic Thue-Morse `(-5)`-Power Law):**
    For ALL `k ≥ 1`:
    * `∑_{x < 2^k} (-1)^pop(x) s(2^k + x)² = -3 * (-5)^((k - 1)/2)`
    * `∑_{x < 2^k} (-1)^pop(x) s(2^k + x) s(2^k + x + 1) = if k % 2 = 1 then 0 else -6 * (-5)^(k/2 - 1)` -/
theorem quadStern_tm_closed_form (k : Nat) (hk : k ≥ 1) :
    (quadSternVec k).x = -3 * (-5 : Int) ^ ((k - 1) / 2) ∧
    (quadSternVec k).y = if k % 2 = 1 then 0 else -6 * (-5 : Int) ^ (k / 2 - 1) := by
  have hstep := (sym2_collapse_lifter Mquad (-5) ellQuad Mquad_cert ⟨1, 1, 1⟩).1
  rw [quadSternVec_eq_iter]
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 => omega
    | 1 => decide
    | 2 => decide
    | m + 3 =>
      have hm1 : m + 1 ≥ 1 := by omega
      have hcol := hstep (m + 1) hm1
      have ihm := ih (m + 1) (by omega) hm1
      rw [hcol]
      simp only [Vec3.smul]
      constructor
      · rw [ihm.1]
        have hdiv : (m + 3 - 1) / 2 = (m + 1 - 1) / 2 + 1 := by omega
        rw [hdiv, Int.pow_succ]; grind
      · rw [ihm.2]
        by_cases hpar : (m + 1) % 2 = 1
        · have hpar3 : (m + 3) % 2 = 1 := by omega
          simp [hpar, hpar3]
        · have hpar3 : (m + 3) % 2 = 0 := by omega
          have hdiv : (m + 3) / 2 - 1 = (m + 1) / 2 - 1 + 1 := by omega
          simp only [hpar, hpar3, Nat.zero_ne_one, ↓reduceIte, hdiv, Int.pow_succ]
          grind

/-- **THEOREM 3B (Exact Quadratic-Form Thue-Morse Conservation Law):**
    For ALL `k ≥ 1`, `∑_{x < 2^k} (-1)^pop(x) (s(2^k+x)² - s(2^k+x)s(2^k+x+1) + s(2^k+x+1)²) = 0`. -/
theorem quadStern_tm_conservation (k : Nat) (hk : k ≥ 1) :
    ellQuad.dot (quadSternVec k) = 0 := by
  rw [quadSternVec_eq_iter]
  exact (sym2_collapse_lifter Mquad (-5) ellQuad Mquad_cert ⟨1, 1, 1⟩).2 k hk

/-! ## Section 5: Non-Vacuity Witnesses & Kernel-Checked Sharpness Counterexamples -/

/-- Non-vacuity witness for Engine I (`HadamardCert` inhabited at `a = 1`). -/
theorem nonvacuity_engine1 : Nonempty (HadamardCert L1 R1 ePlus eMinus 3 1 1) :=
  ⟨aStern_hadamardCert 1⟩

/-- Helper lemma: exact values of `sternCert 2, 3, 4`. -/
theorem sternCert_two : sternCert 2 = ⟨0, 2, 0, -1, -2, 1, 0, 0⟩ := by
  have h := compileCert_two_mul baseCert0 baseCert1 1 (by omega)
  simpa [sternCert, stepEven, baseCert1] using h

theorem sternCert_three : sternCert 3 = ⟨0, 4, 1, 0, 0, 4, 0, -1⟩ := by
  have h := compileCert_two_mul_add_one baseCert0 baseCert1 1 (by omega)
  change sternCert 3 = stepOdd (sternCert 1) (sternCert 2) at h
  rw [h, sternCert_two]
  simp [sternCert, stepOdd, baseCert1]

theorem sternCert_four : sternCert 4 = ⟨2, -3, 0, 0, 0, 2, 1, 0⟩ := by
  have h := compileCert_two_mul baseCert0 baseCert1 2 (by omega)
  change sternCert 4 = stepEven (sternCert 2) at h
  rw [h, sternCert_two]
  decide

/-- Non-vacuity witness for Engine II (`sternCert 4` achieves non-zero affine slope `+2`). -/
theorem nonvacuity_engine2 :
    (sternCert 4).a1 = 2 ∧ carrySternF 4 3 - carrySternF 4 2 = 2 := by
  have h2 := carryStern_mod1_affine 1 2 (by decide)
  have htm1 : tmSign 1 = -1 := tmSign_one
  refine ⟨by rw [sternCert_four], ?_⟩
  have h1 := h2.1
  rw [htm1] at h1
  simpa using h1

/-- Non-vacuity witness for Engine III (`Sym2CollapseCert` inhabited at `Mquad`). -/
theorem nonvacuity_engine3 : Nonempty (Sym2CollapseCert Mquad (-5) ellQuad) :=
  ⟨Mquad_cert⟩

/-- **SHARPNESS COUNTEREXAMPLE 1 (Engine I):** Asymmetric `(a = 1, b = 2)` breaks Hadamard
    monomialization — `(L₁ + R₂) e_+ = (4, 3)` is not a scalar multiple of `e_+ = (1, 1)`. -/
theorem sharpness_asymmetric_no_hadamard :
    ∀ lamP lamM mu : Int, ¬ HadamardCert (Lmat 1) (Rmat 2) ePlus eMinus lamP lamM mu := by
  intro lamP lamM mu h
  have hp := h.add_plus
  simp [Lmat, Rmat, Mat2.add, Mat2.mulV, ePlus, Vec2.smul] at hp
  omega

/-- **SHARPNESS COUNTEREXAMPLE 2 (Engine II — Threshold `2^k ≥ c` is SHARP):**
    At `c = 3, k = 1` (`2^1 = 2 < 3`), `carrySternF 3 1 = -1` whereas `(evalOrbit (sternCert 3) 1).x = 3`. -/
theorem sharpness_threshold_c3_k1 :
    2 ^ 1 < 3 ∧ carrySternF 3 1 = -1 ∧ (evalOrbit (sternCert 3) 1).x = 3 ∧
    carrySternF 3 1 ≠ (evalOrbit (sternCert 3) 1).x := by
  have hf : carrySternF 3 1 = -1 := by
    simp [carrySternF, carrySternVec, sumVec, Vec2.zero, Vec2.add, cwVec, cwMat, treeMat,
          Lmat, Rmat, Mat2.id, Mat2.mul, Mat2.mulV, ePlus, Vec2.smul, tmSign]
  have he : (evalOrbit (sternCert 3) 1).x = 3 := by
    rw [sternCert_three]; decide
  exact ⟨by decide, hf, he, by omega⟩

/-- **SHARPNESS COUNTEREXAMPLE 3 (Engine II — Threshold `2^k ≥ c` on affine class `c = 4`):**
    At `c = 4, k = 1` (`2^1 = 2 < 4`), `carrySternF 4 1 = 1` whereas `(evalOrbit (sternCert 4) 1).x = -1`. -/
theorem sharpness_threshold_c4_k1 :
    2 ^ 1 < 4 ∧ carrySternF 4 1 = 1 ∧ (evalOrbit (sternCert 4) 1).x = -1 ∧
    carrySternF 4 1 ≠ (evalOrbit (sternCert 4) 1).x := by
  have hf : carrySternF 4 1 = 1 := by
    simp [carrySternF, carrySternVec, sumVec, Vec2.zero, Vec2.add, cwVec, cwMat, treeMat,
          Lmat, Rmat, Mat2.id, Mat2.mul, Mat2.mulV, ePlus, Vec2.smul, tmSign]
  have he : (evalOrbit (sternCert 4) 1).x = -1 := by
    rw [sternCert_four]; decide
  exact ⟨by decide, hf, he, by omega⟩

/-- **SHARPNESS COUNTEREXAMPLE 4 (Engine II — Parameter `a = 1` is SHARP):**
    For `a = 2`, the unshifted Thue-Morse sum at `c = 0` is NOT period-4 bounded:
    at `k = 1` it is `-2`, whereas at `k = 5` it is `-32` (proved via Engine I!). -/
theorem sharpness_param_a2_not_periodic :
    (walshSum (Lmat 2) (Rmat 2) ePlus 1 1).x = -2 ∧
    (walshSum (Lmat 2) (Rmat 2) ePlus 5 31).x = -32 ∧
    (walshSum (Lmat 2) (Rmat 2) ePlus 1 1).x ≠
    (walshSum (Lmat 2) (Rmat 2) ePlus 5 31).x := by
  have h1 := aStern_walsh_spectrum 2 1 1 (by decide)
  have h5 := aStern_walsh_spectrum 2 5 31 (by decide)
  have hp1 : popcount 1 = 1 := by simp
  have hp31 : popcount 31 = 5 := by simp
  have hig1 : igray 1 = 1 := by rw [igray_eq_xor]; simp
  have hig31 : igray 31 = 21 := by
    rw [igray_eq_xor]; simp only [Nat.reduceDiv]
    rw [igray_eq_xor]; simp only [Nat.reduceDiv]
    rw [igray_eq_xor]; simp only [Nat.reduceDiv]
    rw [igray_eq_xor]; simp only [Nat.reduceDiv]
    rw [igray_eq_xor]; simp
  have he1p : expPlus 1 1 = 0 := by simp [expPlus, hig1]
  have he1m : expMinus 1 = 0 := by simp [expMinus, hig1]
  have he5p : expPlus 5 31 = 0 := by simp [expPlus, hig31]
  have he5m : expMinus 31 = 0 := by simp [expMinus, hig31]
  rw [hp1, he1p, he1m] at h1
  rw [hp31, he5p, he5m] at h5
  simp only [triSign] at h1 h5
  have hv1 : (walshSum (Lmat 2) (Rmat 2) ePlus 1 1).x = -2 := by simpa using h1
  have hv5 : (walshSum (Lmat 2) (Rmat 2) ePlus 5 31).x = -32 := by simpa using h5
  exact ⟨hv1, hv5, by omega⟩

/-- **SHARPNESS COUNTEREXAMPLE 5 (Engine III — Hypothesis `k ≥ 1` is SHARP):**
    At `k = 0`, `ellQuad · quadSternVec 0 = 1 ≠ 0`. -/
theorem sharpness_quad_k0 :
    ellQuad.dot (quadSternVec 0) = 1 ∧ ellQuad.dot (quadSternVec 0) ≠ 0 := by
  rw [quadSternVec_eq_iter]; decide

/-- Bitwise XOR parity additivity: `popcount (a ^^^ b) % 2 = (popcount a + popcount b) % 2`. -/
theorem popcount_xor_parity (a b : Nat) :
    popcount (a ^^^ b) % 2 = (popcount a + popcount b) % 2 := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    cases a with
    | zero => simp
    | succ a' =>
      rw [popcount_div2 (a' + 1 ^^^ b), popcount_div2 (a' + 1), popcount_div2 b]
      have hdiv : (a' + 1 ^^^ b) / 2 = (a' + 1) / 2 ^^^ b / 2 := by
        apply Nat.eq_of_testBit_eq
        intro i
        rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ,
            ← Nat.testBit_xor]
      have hmod : (a' + 1 ^^^ b) % 2 = ((a' + 1) % 2 + b % 2) % 2 := by
        have htb := Nat.testBit_xor (a' + 1) b 0
        simp only [Nat.testBit_zero] at htb
        have h1 : (a' + 1) % 2 = 0 ∨ (a' + 1) % 2 = 1 := by omega
        have h2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
        have h3 : (a' + 1 ^^^ b) % 2 = 0 ∨ (a' + 1 ^^^ b) % 2 = 1 := by omega
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
          simp_all
      have hlt : (a' + 1) / 2 < a' + 1 := by omega
      have hrec := ih _ hlt (b / 2)
      rw [hdiv, hmod]
      omega

/-- Multiplicativity of the Thue-Morse sign under carry-free XOR: `tmSign (a ^^^ b) = tmSign a * tmSign b`. -/
theorem tmSign_xor (a b : Nat) : tmSign (a ^^^ b) = tmSign a * tmSign b := by
  unfold tmSign
  rw [popcount_xor_parity]
  have ha : popcount a % 2 = 0 ∨ popcount a % 2 = 1 := by omega
  have hb : popcount b % 2 = 0 ∨ popcount b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    (have hs : (popcount a + popcount b) % 2 = (popcount a % 2 + popcount b % 2) % 2 := by omega;
     rw [hs, ha, hb]; simp)

/-- Carry-free XOR-shifted Thue-Morse Stern vector `∑_{x < 2^k} (-1)^pop(x ^^^ c) • cwVec 1 k x`. -/
def xorSternVec (c k : Nat) : Vec2 :=
  sumVec (2 ^ k) (fun x => (cwVec 1 k x).smul (tmSign (x ^^^ c)))

def xorSternF (c k : Nat) : Int := (xorSternVec c k).x

/-- **SHARPNESS THEOREM 6 (Engine II — Carry-Free XOR Contrast):**
    Replacing carried addition `x + c` by carry-free XOR `x ^^^ c` completely eliminates BOTH
    the `2^k ≥ c` threshold AND the mod-3 affine drift: for ALL `c, k ∈ ℕ`,
    * `xorSternF c k = tmSign c * carrySternF 0 k`,
    * `xorSternF c (k + 4) = xorSternF c k`, and `xorSternF c (k + 2) = -xorSternF c k`
    (zero linear drift for every `c`, certifying that the `-2 * (-1)^pop(q)` drift at `c = 3q + 1`
    is 100% a carry-propagation phenomenon). -/
theorem xorSternF_periodic_zero_drift (c k : Nat) :
    xorSternF c k = tmSign c * carrySternF 0 k ∧
    xorSternF c (k + 4) = xorSternF c k ∧
    xorSternF c (k + 2) = -xorSternF c k := by
  have hvec : ∀ n, xorSternVec c n = (carrySternVec 0 n).smul (tmSign c) := by
    intro n
    unfold xorSternVec carrySternVec
    rw [sumVec_smul]
    apply sumVec_congr
    intro x _
    rw [Nat.add_zero, tmSign_xor]
    cases (cwVec 1 n x)
    simp only [Vec2.smul, Vec2.mk.injEq]
    exact ⟨by grind, by grind⟩
  have hx : ∀ n, xorSternF c n = tmSign c * carrySternF 0 n := by
    intro n; unfold xorSternF carrySternF; rw [hvec n]; rfl
  have hz : ∀ n, carrySternF 0 n = phi4 n := by
    intro n
    have he := carrySternVec_zero_eval n
    unfold carrySternF; rw [he]
    simp [evalOrbit, baseCert0]
  refine ⟨hx k, ?_, ?_⟩
  · rw [hx (k + 4), hx k, hz (k + 4), hz k, phi4_add4]
  · rw [hx (k + 2), hx k, hz (k + 2), hz k, phi4_add2]; grind

end SternCW
