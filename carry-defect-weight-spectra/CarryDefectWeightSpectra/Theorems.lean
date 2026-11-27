/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryDefectWeightSpectra.Defs

/-!
# Theorems (`carry-defect-weight-spectra`)

Full proofs of the headline infinite theorems of Carry-defect weight spectra of constant multiplication by a Mersenne-type multiplier.
-/

namespace CarryDefectEngine

theorem clmulFuel_eq (c : Nat) : ∀ (k1 k2 x : Nat), x ≤ k1 → x ≤ k2 →
    clmulFuel k1 c x = clmulFuel k2 c x := by
  intro k1
  induction k1 with
  | zero =>
    intro k2 x hx1 _
    have hx0 : x = 0 := by omega
    subst hx0
    cases k2 <;> simp [clmulFuel]
  | succ k1 ih =>
    intro k2 x hx1 hx2
    cases k2 with
    | zero =>
      have hx0 : x = 0 := by omega
      subst hx0
      simp [clmulFuel]
    | succ k2 =>
      simp only [clmulFuel]
      by_cases hx0 : x = 0
      · simp [hx0]
      · simp only [hx0, ↓reduceIte]
        have h1 : x / 2 ≤ k1 := by omega
        have h2 : x / 2 ≤ k2 := by omega
        rw [ih k2 (x / 2) h1 h2]

theorem popcountFuel_eq : ∀ (k1 k2 n : Nat), n ≤ k1 → n ≤ k2 →
    popcountFuel k1 n = popcountFuel k2 n := by
  intro k1
  induction k1 with
  | zero =>
    intro k2 n hn1 _
    have hn0 : n = 0 := by omega
    subst hn0
    cases k2 <;> simp [popcountFuel]
  | succ k1 ih =>
    intro k2 n hn1 hn2
    cases k2 with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0
      simp [popcountFuel]
    | succ k2 =>
      simp only [popcountFuel]
      by_cases hn0 : n = 0
      · simp [hn0]
      · simp only [hn0, ↓reduceIte]
        have h1 : n / 2 ≤ k1 := by omega
        have h2 : n / 2 ≤ k2 := by omega
        rw [ih k2 (n / 2) h1 h2]

theorem clmul_zero (c : Nat) : clmul c 0 = 0 := rfl

theorem clmul_pos (c x : Nat) (hx : x ≠ 0) :
    clmul c x = (x % 2) * c ^^^ (2 * clmul c (x / 2)) := by
  cases x with
  | zero => exact absurd rfl hx
  | succ x' =>
    unfold clmul
    simp only [clmulFuel, Nat.succ_ne_zero, ↓reduceIte]
    have hfuel : clmulFuel x' c ((x' + 1) / 2) = clmulFuel ((x' + 1) / 2) c ((x' + 1) / 2) :=
      clmulFuel_eq c x' ((x' + 1) / 2) ((x' + 1) / 2) (by omega) (Nat.le_refl _)
    rw [hfuel]
    have hmod : (x' + 1) % 2 = 0 ∨ (x' + 1) % 2 = 1 := by omega
    rcases hmod with h | h <;> simp [h]

theorem clmul_one (c : Nat) : clmul c 1 = c := by
  rw [clmul_pos c 1 (by omega)]
  simp [clmul_zero]

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_eq_mod_add_div (n : Nat) : popcount n = n % 2 + popcount (n / 2) := by
  cases n with
  | zero => rfl
  | succ n' =>
    unfold popcount
    simp only [popcountFuel, Nat.succ_ne_zero, ↓reduceIte]
    have hfuel : popcountFuel n' ((n' + 1) / 2) = popcountFuel ((n' + 1) / 2) ((n' + 1) / 2) :=
      popcountFuel_eq n' ((n' + 1) / 2) ((n' + 1) / 2) (by omega) (Nat.le_refl _)
    rw [hfuel]

theorem popcount_two_mul (n : Nat) : popcount (2 * n) = popcount n := by
  rw [popcount_eq_mod_add_div]
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  rw [h1, h2]; omega

theorem popcount_two_mul_add_one (n : Nat) : popcount (2 * n + 1) = 1 + popcount n := by
  rw [popcount_eq_mod_add_div]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]

theorem popcount_pow_two (k : Nat) : popcount (2 ^ k) = 1 := by
  induction k with
  | zero =>
    rw [Nat.pow_zero, popcount_eq_mod_add_div]
    simp [popcount_zero]
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_comm, popcount_two_mul, ih]

theorem popcount_eq_zero_iff (n : Nat) : popcount n = 0 ↔ n = 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n = 0
    · subst h; simp [popcount_zero]
    · rw [popcount_eq_mod_add_div]
      constructor
      · intro hp
        have hm : n % 2 = 0 := by omega
        have hd : popcount (n / 2) = 0 := by omega
        have hlt : n / 2 < n := by omega
        have hdiv0 : n / 2 = 0 := (ih (n / 2) hlt).mp hd
        omega
      · intro hn; exact absurd hn h

theorem popcount_pos_of_ne_zero {n : Nat} (h : n ≠ 0) : 1 ≤ popcount n := by
  have hp : popcount n ≠ 0 := by
    intro hz
    exact h ((popcount_eq_zero_iff n).mp hz)
  omega

theorem xor_mod_two (a b : Nat) : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  have h1 : (a ^^^ b) % 2 = 1 ↔ ¬(a % 2 = 1 ↔ b % 2 = 1) := Nat.xor_mod_two_eq_one
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hab : (a ^^^ b) % 2 = 0 ∨ (a ^^^ b) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;>
    simp [ha, hb, hab] at h1 ⊢

theorem xor_two_mul_add (a b r s : Nat) (hr : r < 2) (hs : s < 2) :
    (2 * a + r) ^^^ (2 * b + s) = 2 * (a ^^^ b) + (r ^^^ s) := by
  have hdiv : ((2 * a + r) ^^^ (2 * b + s)) / 2 = a ^^^ b := by
    rw [Nat.xor_div_two]
    have h1 : (2 * a + r) / 2 = a := by omega
    have h2 : (2 * b + s) / 2 = b := by omega
    rw [h1, h2]
  have hmod : ((2 * a + r) ^^^ (2 * b + s)) % 2 = r ^^^ s := by
    rw [xor_mod_two]
    have h1 : (2 * a + r) % 2 = r := by omega
    have h2 : (2 * b + s) % 2 = s := by omega
    rw [h1, h2]
  have hrec := Nat.div_add_mod ((2 * a + r) ^^^ (2 * b + s)) 2
  rw [hdiv, hmod] at hrec
  omega

theorem xor_two_mul (a b : Nat) : (2 * a) ^^^ (2 * b) = 2 * (a ^^^ b) := by
  have h := xor_two_mul_add a b 0 0 (by omega) (by omega)
  simpa using h

theorem xor_eq_zero_iff {a b : Nat} : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a ^^^ 0 := (Nat.xor_zero a).symm
      _ = a ^^^ (a ^^^ b) := by rw [h]
      _ = (a ^^^ a) ^^^ b := (Nat.xor_assoc a a b).symm
      _ = 0 ^^^ b := by rw [Nat.xor_self]
      _ = b := Nat.zero_xor b
  · intro h; subst h; exact Nat.xor_self a

theorem xor_le_add (a b : Nat) : a ^^^ b ≤ a + b := by
  induction hsum : a + b using Nat.strongRecOn generalizing a b with
  | ind s ih =>
    by_cases ha : a = 0
    · subst ha; simp [← hsum]
    · by_cases hb : b = 0
      · subst hb; simp [← hsum]
      · have hdiv := ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
        have hdecomp : a ^^^ b = 2 * (a / 2 ^^^ b / 2) + (a % 2 ^^^ b % 2) := by
          have h := xor_two_mul_add (a / 2) (b / 2) (a % 2) (b % 2) (by omega) (by omega)
          have ha' : 2 * (a / 2) + a % 2 = a := by omega
          have hb' : 2 * (b / 2) + b % 2 = b := by omega
          rw [ha', hb'] at h
          exact h
        have hmod : a % 2 ^^^ b % 2 ≤ a % 2 + b % 2 := by
          have h1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
          have h2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]
        omega

theorem xor_lt_pow_two {a b K : Nat} (ha : a < 2 ^ K) (hb : b < 2 ^ K) :
    a ^^^ b < 2 ^ K := by
  induction K generalizing a b with
  | zero =>
    simp at ha hb
    subst ha; subst hb; simp
  | succ K ih =>
    have ha' : a / 2 < 2 ^ K := by rw [Nat.pow_succ] at ha; omega
    have hb' : b / 2 < 2 ^ K := by rw [Nat.pow_succ] at hb; omega
    have hdiv := ih ha' hb'
    have hdecomp : a ^^^ b = 2 * (a / 2 ^^^ b / 2) + (a % 2 ^^^ b % 2) := by
      have h := xor_two_mul_add (a / 2) (b / 2) (a % 2) (b % 2) (by omega) (by omega)
      have ha2 : 2 * (a / 2) + a % 2 = a := by omega
      have hb2 : 2 * (b / 2) + b % 2 = b := by omega
      rw [ha2, hb2] at h
      exact h
    have hmod : a % 2 ^^^ b % 2 < 2 := by
      have h1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have h2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]
    rw [hdecomp, Nat.pow_succ]
    omega

theorem xor_block {a1 a2 b1 b2 K : Nat} (h1 : a1 < 2 ^ K) (h2 : a2 < 2 ^ K) :
    (a1 + 2 ^ K * b1) ^^^ (a2 + 2 ^ K * b2) = (a1 ^^^ a2) + 2 ^ K * (b1 ^^^ b2) := by
  induction K generalizing a1 a2 with
  | zero =>
    simp at h1 h2
    subst h1; subst h2; simp
  | succ K ih =>
    have ha1 : a1 / 2 < 2 ^ K := by rw [Nat.pow_succ] at h1; omega
    have ha2 : a2 / 2 < 2 ^ K := by rw [Nat.pow_succ] at h2; omega
    have hrec := ih ha1 ha2
    have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [Nat.pow_succ]; omega
    have hmul1 : 2 ^ (K + 1) * b1 = 2 * (2 ^ K * b1) := by rw [hpow, Nat.mul_assoc]
    have hmul2 : 2 ^ (K + 1) * b2 = 2 * (2 ^ K * b2) := by rw [hpow, Nat.mul_assoc]
    have hmul12 : 2 ^ (K + 1) * (b1 ^^^ b2) = 2 * (2 ^ K * (b1 ^^^ b2)) := by
      rw [hpow, Nat.mul_assoc]
    have heq1 : a1 + 2 ^ (K + 1) * b1 = 2 * (a1 / 2 + 2 ^ K * b1) + a1 % 2 := by
      rw [hmul1]; omega
    have heq2 : a2 + 2 ^ (K + 1) * b2 = 2 * (a2 / 2 + 2 ^ K * b2) + a2 % 2 := by
      rw [hmul2]; omega
    have hstep := xor_two_mul_add (a1 / 2 + 2 ^ K * b1) (a2 / 2 + 2 ^ K * b2)
                    (a1 % 2) (a2 % 2) (by omega) (by omega)
    rw [heq1, heq2, hstep, hrec]
    have ha12 : a1 ^^^ a2 = 2 * (a1 / 2 ^^^ a2 / 2) + (a1 % 2 ^^^ a2 % 2) := by
      have h := xor_two_mul_add (a1 / 2) (a2 / 2) (a1 % 2) (a2 % 2) (by omega) (by omega)
      have ha1' : 2 * (a1 / 2) + a1 % 2 = a1 := by omega
      have ha2' : 2 * (a2 / 2) + a2 % 2 = a2 := by omega
      rw [ha1', ha2'] at h; exact h
    rw [ha12, hmul12]
    omega

theorem xor_disjoint_add {a b K : Nat} (ha : a < 2 ^ K) :
    a ^^^ (2 ^ K * b) = a + 2 ^ K * b := by
  have h := xor_block (a1 := a) (a2 := 0) (b1 := 0) (b2 := b) ha (Nat.two_pow_pos K)
  simpa using h

theorem popcount_block {a b K : Nat} (ha : a < 2 ^ K) :
    popcount (a + 2 ^ K * b) = popcount a + popcount b := by
  induction K generalizing a with
  | zero =>
    simp at ha; subst ha; simp [popcount_zero]
  | succ K ih =>
    have ha' : a / 2 < 2 ^ K := by rw [Nat.pow_succ] at ha; omega
    have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [Nat.pow_succ]; omega
    have hmul : 2 ^ (K + 1) * b = 2 * (2 ^ K * b) := by rw [hpow, Nat.mul_assoc]
    have hmod : (a + 2 ^ (K + 1) * b) % 2 = a % 2 := by rw [hmul]; omega
    have hdiv : (a + 2 ^ (K + 1) * b) / 2 = a / 2 + 2 ^ K * b := by rw [hmul]; omega
    rw [popcount_eq_mod_add_div (a + 2 ^ (K + 1) * b), hmod, hdiv, ih ha']
    rw [popcount_eq_mod_add_div a]
    omega

theorem clmul_le_mul (c x : Nat) : clmul c x ≤ c * x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases hx : x = 0
    · subst hx; simp [clmul_zero]
    · rw [clmul_pos c x hx]
      have h1 := xor_le_add ((x % 2) * c) (2 * clmul c (x / 2))
      have h2 := ih (x / 2) (by omega)
      have h3 : (x % 2) * c + 2 * (c * (x / 2)) = c * x := by
        have hdecomp : x = 2 * (x / 2) + x % 2 := by omega
        calc (x % 2) * c + 2 * (c * (x / 2))
            = c * (2 * (x / 2) + x % 2) := by
              rw [Nat.mul_add, Nat.mul_comm (x % 2) c, ← Nat.mul_assoc, Nat.mul_comm 2 c, Nat.mul_assoc]
              omega
          _ = c * x := by rw [← hdecomp]
      omega

theorem clmul_two_mul (c x : Nat) : clmul (2 * c) x = 2 * clmul c x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases hx : x = 0
    · subst hx; simp [clmul_zero]
    · rw [clmul_pos (2 * c) x hx, clmul_pos c x hx, ih (x / 2) (by omega)]
      have hmul : (x % 2) * (2 * c) = 2 * ((x % 2) * c) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (x % 2) 2, Nat.mul_assoc]
      rw [hmul, xor_two_mul]

/-- Exact 2-adic shift invariance: doubling the multiplier leaves carry-defect weight unchanged. -/
theorem defectWeight_two_mul (c x : Nat) : defectWeight (2 * c) x = defectWeight c x := by
  unfold defectWeight defect
  rw [clmul_two_mul, Nat.mul_assoc, xor_two_mul, popcount_two_mul]

theorem defect_zero_right (c : Nat) : defect c 0 = 0 := by
  simp [defect, clmul_zero]

theorem defectWeight_zero_right (c : Nat) : defectWeight c 0 = 0 := by
  simp [defectWeight, defect_zero_right, popcount_zero]

theorem clmul_one_left (x : Nat) : clmul 1 x = x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases hx : x = 0
    · subst hx; exact clmul_zero 1
    · rw [clmul_pos 1 x hx, ih (x / 2) (by omega), Nat.mul_one]
      have h := xor_two_mul_add 0 (x / 2) (x % 2) 0 (by omega) (by omega)
      simp at h
      rw [h]; omega

theorem defectWeight_one_left (x : Nat) : defectWeight 1 x = 0 := by
  simp [defectWeight, defect, clmul_one_left, popcount_zero]


/-! ## Section 2: Universal Residual Carry-Defect Bit-Slice Transducer T_c -/

theorem genDefect_zero (c u v : Nat) : genDefect c u v 0 = u ^^^ v := by
  simp [genDefect, clmul_zero]

theorem genDefect_zero_state (c x : Nat) : genDefect c 0 0 x = defect c x := by
  simp [genDefect, defect]

theorem emit_le_one (u v : Nat) : emit u v ≤ 1 := by
  unfold emit
  have hu : u % 2 = 0 ∨ u % 2 = 1 := by omega
  have hv : v % 2 = 0 ∨ v % 2 = 1 := by omega
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp [hu, hv]

theorem genDefect_mod_two (c u v x : Nat) (hx : x ≠ 0) :
    genDefect c u v x % 2 = emit u v := by
  unfold genDefect emit
  rw [clmul_pos c x hx, xor_mod_two]
  have h1 : (u + c * x) % 2 = (u + (x % 2) * c) % 2 := by
    have hdecomp : c * x = (x % 2) * c + 2 * (c * (x / 2)) := by
      have hx2 : x = 2 * (x / 2) + x % 2 := by omega
      calc c * x = c * (2 * (x / 2) + x % 2) := by rw [← hx2]
        _ = c * (2 * (x / 2)) + c * (x % 2) := Nat.mul_add c _ _
        _ = (x % 2) * c + 2 * (c * (x / 2)) := by
          rw [Nat.mul_comm c (x % 2), ← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc]
          omega
    rw [hdecomp]; omega
  have h2 : (v ^^^ ((x % 2) * c ^^^ 2 * clmul c (x / 2))) % 2 = (v ^^^ (x % 2) * c) % 2 := by
    rw [← Nat.xor_assoc, xor_mod_two]
    have hev : (2 * clmul c (x / 2)) % 2 = 0 := by omega
    rw [hev, Nat.xor_zero]
  rw [h1, h2, xor_mod_two]
  have hu : u % 2 = 0 ∨ u % 2 = 1 := by omega
  have hv : v % 2 = 0 ∨ v % 2 = 1 := by omega
  have hbc : ((x % 2) * c) % 2 = 0 ∨ ((x % 2) * c) % 2 = 1 := by omega
  have hadd : (u + (x % 2) * c) % 2 = (u % 2 + ((x % 2) * c) % 2) % 2 := by omega
  rw [hadd]
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rcases hbc with hbc | hbc <;>
    simp [hu, hv, hbc]

theorem genDefect_div_two (c u v x : Nat) (hx : x ≠ 0) :
    genDefect c u v x / 2 =
      genDefect c (stepU c u (x % 2)) (stepV c v (x % 2)) (x / 2) := by
  unfold genDefect stepU stepV
  rw [clmul_pos c x hx, Nat.xor_div_two]
  have hdecomp : c * x = (x % 2) * c + 2 * (c * (x / 2)) := by
    have hx2 : x = 2 * (x / 2) + x % 2 := by omega
    calc c * x = c * (2 * (x / 2) + x % 2) := by rw [← hx2]
      _ = c * (2 * (x / 2)) + c * (x % 2) := Nat.mul_add c _ _
      _ = (x % 2) * c + 2 * (c * (x / 2)) := by
        rw [Nat.mul_comm c (x % 2), ← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc]
        omega
  have h1 : (u + c * x) / 2 = (u + (x % 2) * c) / 2 + c * (x / 2) := by
    rw [hdecomp]; omega
  have h2 : (v ^^^ ((x % 2) * c ^^^ 2 * clmul c (x / 2))) / 2 =
      (v ^^^ (x % 2) * c) / 2 ^^^ clmul c (x / 2) := by
    rw [← Nat.xor_assoc, Nat.xor_div_two]
    have hdiv : (2 * clmul c (x / 2)) / 2 = clmul c (x / 2) := by omega
    rw [hdiv]
  rw [h1, h2]

/-- Universal Residual Carry-Defect Transducer Weight Recurrence (holds for all c, u, v, x). -/
theorem popcount_genDefect_step (c u v x : Nat) (hx : x ≠ 0) :
    popcount (genDefect c u v x) =
      emit u v + popcount (genDefect c (stepU c u (x % 2)) (stepV c v (x % 2)) (x / 2)) := by
  rw [popcount_eq_mod_add_div, genDefect_mod_two c u v x hx, genDefect_div_two c u v x hx]

/-- State-Space Monotonicity: v <= u is an invariant of T_c for all c and input bits b. -/
theorem stepV_le_stepU (c u v b : Nat) (hvu : v ≤ u) : stepV c v b ≤ stepU c u b := by
  unfold stepV stepU
  have h := xor_le_add v (b * c)
  omega

/-- State-Space Finiteness: for c > 0, the residual states stay inside {(u, v) | v <= u < c}. -/
theorem stepU_lt (c u b : Nat) (hu : u < c) (hb : b ≤ 1) : stepU c u b < c := by
  unfold stepU
  have hbc : b * c ≤ c := by
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp
  omega

/-- Zero-Defect Diagonal Barrier: from any residual state with v <= u,
    zero carry-defect forces u = v (off-diagonal states can never achieve zero defect). -/
theorem genDefect_eq_zero_imp_eq {c u v x : Nat} (hvu : v ≤ u)
    (h0 : genDefect c u v x = 0) : u = v := by
  have heq : u + c * x = v ^^^ clmul c x := xor_eq_zero_iff.mp h0
  have hle1 : v ^^^ clmul c x ≤ v + clmul c x := xor_le_add v (clmul c x)
  have hle2 : clmul c x ≤ c * x := clmul_le_mul c x
  omega


/-! ## Section 3: Reusable Finite-Certificate -> Infinite Lower-Bound Compiler -/

theorem lookup_checkEntry (c depth : Nat) (rootTree : BinTree StateEntry) :
    ∀ (d : Nat) (t : BinTree StateEntry) (k : Nat) (ent : StateEntry),
      checkTree c depth rootTree t = true →
      BinTree.lookup d t k = some ent →
      checkEntry c depth rootTree ent = true := by
  intro d
  induction d with
  | zero =>
    intro t k ent hT hL
    cases t with
    | e => simp [BinTree.lookup] at hL
    | l a =>
      simp [BinTree.lookup] at hL
      subst hL
      simpa [checkTree] using hT
    | n l r => simp [BinTree.lookup] at hL
  | succ d ih =>
    intro t k ent hT hL
    cases t with
    | e => simp [BinTree.lookup] at hL
    | l a => simp [BinTree.lookup] at hL
    | n left right =>
      simp only [checkTree, Bool.and_eq_true] at hT
      simp only [BinTree.lookup] at hL
      split at hL
      · exact ih left (k / 2) ent hT.1 hL
      · exact ih right (k / 2) ent hT.2 hL

/-- Core inductive soundness of a finite backward-potential certificate over all x in Nat. -/
theorem potentialCert_sound_aux (c depth : Nat) (tree : BinTree StateEntry)
    (hTree : checkTree c depth tree tree = true) :
    ∀ (x : Nat) (idx : Nat) (ent : StateEntry),
      BinTree.lookup depth tree idx = some ent →
      ent.aVal ≤ popcount (genDefect c ent.u ent.v x) ∧
      (genDefect c ent.u ent.v x ≠ 0 →
        ent.bVal ≤ popcount (genDefect c ent.u ent.v x)) := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro idx ent hLookup
    have hEnt := lookup_checkEntry c depth tree depth tree idx ent hTree hLookup
    simp only [checkEntry, Bool.and_eq_true, decide_eq_true_eq] at hEnt
    rcases hEnt with ⟨⟨⟨hBaseA, hBaseB⟩, hBr0⟩, hBr1⟩
    by_cases hx : x = 0
    · subst hx
      rw [genDefect_zero]
      refine ⟨hBaseA, ?_⟩
      intro hne
      have huv : ent.u ≠ ent.v := by
        intro heq; rw [heq] at hne; exact hne (Nat.xor_self ent.v)
      have hneBool : (ent.u != ent.v) = true := by
        simp [bne, huv]
      rw [hneBool] at hBaseB
      simpa using hBaseB
    · have hRec := popcount_genDefect_step c ent.u ent.v x hx
      have hMod := genDefect_mod_two c ent.u ent.v x hx
      have hDiv := genDefect_div_two c ent.u ent.v x hx
      have hbit : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hStep : ∀ (b nextId : Nat), x % 2 = b →
          checkBranch c depth tree ent b nextId = true →
          ent.aVal ≤ popcount (genDefect c ent.u ent.v x) ∧
          (genDefect c ent.u ent.v x ≠ 0 →
            ent.bVal ≤ popcount (genDefect c ent.u ent.v x)) := by
        intro b nextId hxb hBr
        unfold checkBranch at hBr
        cases hNxt : BinTree.lookup depth tree nextId with
        | none => simp [hNxt] at hBr
        | some nxt =>
          simp only [hNxt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hBr
          rcases hBr with ⟨⟨⟨hU, hV⟩, hA⟩, hB⟩
          have hIH := ih (x / 2) (by omega) nextId nxt hNxt
          rw [hU, hV, ← hxb] at hIH
          rw [hRec]
          constructor
          · omega
          · intro hnz
            have he01 : emit ent.u ent.v = 0 ∨ emit ent.u ent.v = 1 := by
              have := emit_le_one ent.u ent.v; omega
            rcases he01 with he0 | he1
            · simp only [he0, Nat.zero_ne_one, ↓reduceIte, decide_eq_true_eq] at hB
              have hdivNz : genDefect c (stepU c ent.u (x % 2)) (stepV c ent.v (x % 2)) (x / 2) ≠ 0 := by
                rw [← hDiv]
                intro hdz
                have hzero : genDefect c ent.u ent.v x = 0 := by
                  have hd := Nat.div_add_mod (genDefect c ent.u ent.v x) 2
                  rw [hdz, hMod, he0] at hd
                  omega
                exact hnz hzero
              have hIHB := hIH.2 hdivNz
              omega
            · simp only [he1, ↓reduceIte, decide_eq_true_eq] at hB
              have hIHA := hIH.1
              omega
      rcases hbit with hb0 | hb1
      · exact hStep 0 ent.n0 hb0 hBr0
      · exact hStep 1 ent.n1 hb1 hBr1

/-- Master Finite -> Infinite Soundness Theorem for the Carry-Defect Potential Compiler. -/
theorem PotentialCert.sound (c depth root : Nat) (tree : BinTree StateEntry)
    (e0 : StateEntry)
    (hTree : checkTree c depth tree tree = true)
    (hRoot : BinTree.lookup depth tree root = some e0)
    (hu0 : e0.u = 0) (hv0 : e0.v = 0) :
    ∀ x : Nat, defect c x ≠ 0 → e0.bVal ≤ defectWeight c x := by
  intro x hnz
  have h := (potentialCert_sound_aux c depth tree hTree x root e0 hRoot).2
  rw [hu0, hv0, genDefect_zero_state] at h
  exact h hnz


/-! ## Section 4: Shift-Separation Semigroup Additivity & Frobenius Lifting Engine -/

theorem clmul_add_shift (c x y K : Nat) (hx : x < 2 ^ K) :
    clmul c (x + 2 ^ K * y) = clmul c x ^^^ (2 ^ K * clmul c y) := by
  induction K generalizing x with
  | zero =>
    simp at hx; subst hx; simp [clmul_zero]
  | succ K ih =>
    by_cases hxy : x + 2 ^ (K + 1) * y = 0
    · have hx0 : x = 0 := by omega
      have hy0 : y = 0 := by
        cases y with
        | zero => rfl
        | succ y' =>
          have hpos : 0 < 2 ^ (K + 1) := Nat.two_pow_pos (K + 1)
          have hge : 2 ^ (K + 1) ≤ 2 ^ (K + 1) * (y' + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          omega
      subst hx0; subst hy0; simp [clmul_zero]
    · have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [Nat.pow_succ]; omega
      have hmul : 2 ^ (K + 1) * y = 2 * (2 ^ K * y) := by rw [hpow, Nat.mul_assoc]
      have hmod : (x + 2 ^ (K + 1) * y) % 2 = x % 2 := by rw [hmul]; omega
      have hdiv : (x + 2 ^ (K + 1) * y) / 2 = x / 2 + 2 ^ K * y := by rw [hmul]; omega
      have hx' : x / 2 < 2 ^ K := by rw [hpow] at hx; omega
      rw [clmul_pos c (x + 2 ^ (K + 1) * y) hxy, hmod, hdiv, ih (x / 2) hx']
      rw [← xor_two_mul, ← Nat.xor_assoc, ← Nat.mul_assoc, ← hpow]
      by_cases hx0 : x = 0
      · subst hx0; simp [clmul_zero]
      · rw [← clmul_pos c x hx0]

/-- Exact Shift-Separation Additivity: non-overlapping blocks add carry-defect weights. -/
theorem defectWeight_shift_add (c x y K : Nat) (hx : x < 2 ^ K) (hcx : c * x < 2 ^ K) :
    defectWeight c (x + 2 ^ K * y) = defectWeight c x + defectWeight c y := by
  unfold defectWeight defect
  have hmul : c * (x + 2 ^ K * y) = c * x + 2 ^ K * (c * y) := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm c (2 ^ K), Nat.mul_assoc]
  have hclm_lt : clmul c x < 2 ^ K := Nat.lt_of_le_of_lt (clmul_le_mul c x) hcx
  have hclm : clmul c (x + 2 ^ K * y) = clmul c x + 2 ^ K * clmul c y := by
    rw [clmul_add_shift c x y K hx, xor_disjoint_add hclm_lt]
  rw [hmul, hclm, xor_block hcx hclm_lt]
  have hdef_lt : (c * x) ^^^ (clmul c x) < 2 ^ K := xor_lt_pow_two hcx hclm_lt
  exact popcount_block hdef_lt

theorem lt_two_pow_self (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ]
    have hpos : 1 ≤ 2 ^ n := Nat.two_pow_pos n
    omega

/-- The carry-defect weight spectrum W(c) is an additive submonoid of (Nat, +, 0). -/
theorem defectWeight_add_closed (c w1 w2 : Nat)
    (h1 : ∃ x, defectWeight c x = w1) (h2 : ∃ y, defectWeight c y = w2) :
    ∃ z, defectWeight c z = w1 + w2 := by
  rcases h1 with ⟨x, hx⟩
  rcases h2 with ⟨y, hy⟩
  let K := c * x + x + 1
  have hK1 : x < 2 ^ K := Nat.lt_of_le_of_lt (by omega) (lt_two_pow_self K)
  have hK2 : c * x < 2 ^ K := Nat.lt_of_le_of_lt (by omega) (lt_two_pow_self K)
  refine ⟨x + 2 ^ K * y, ?_⟩
  rw [defectWeight_shift_add c x y K hK1 hK2, hx, hy]

/-- Frobenius Semigroup Lifting: achieving [mu, 2*mu - 1] lifts to ALL w >= mu. -/
theorem semigroup_all_ge (c mu : Nat) (hmu : 1 ≤ mu)
    (hblock : ∀ r, r < mu → ∃ x, defectWeight c x = mu + r) :
    ∀ w, mu ≤ w → ∃ x, defectWeight c x = w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < 2 * mu
    · have hr : w - mu < mu := by omega
      have h := hblock (w - mu) hr
      have heq : mu + (w - mu) = w := by omega
      rw [heq] at h
      exact h
    · have hw' : mu ≤ w - mu := by omega
      have hlt' : w - mu < w := by omega
      have h1 : ∃ x, defectWeight c x = mu := by
        simpa using hblock 0 (by omega)
      have h2 : ∃ y, defectWeight c y = w - mu := ih (w - mu) hlt' hw'
      have h3 := defectWeight_add_closed c mu (w - mu) h1 h2
      have heq : mu + (w - mu) = w := by omega
      rw [heq] at h3
      exact h3

/-- Combined Exact Spectrum Classification Engine:
    Finite Potential Certificate + Finite Witness Block => Exact Infinite Spectrum Theorem. -/
theorem spectrum_classify_of_cert (c depth root : Nat) (tree : BinTree StateEntry)
    (e0 : StateEntry)
    (hTree : checkTree c depth tree tree = true)
    (hRoot : BinTree.lookup depth tree root = some e0)
    (hu0 : e0.u = 0) (hv0 : e0.v = 0)
    (hmu : 1 ≤ e0.bVal)
    (hblock : ∀ r, r < e0.bVal → ∃ x, defectWeight c x = e0.bVal + r) :
    ∀ w : Nat, (∃ x, defectWeight c x = w) ↔ (w = 0 ∨ e0.bVal ≤ w) := by
  intro w
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hz : defect c x = 0
    · left; simp [defectWeight, hz, popcount_zero]
    · right; exact PotentialCert.sound c depth root tree e0 hTree hRoot hu0 hv0 x hz
  · intro hw
    rcases hw with rfl | hge
    · exact ⟨0, defectWeight_zero_right c⟩
    · exact semigroup_all_ge c e0.bVal hmu hblock w hge


/-! ## Section 5: Infinite Theorem 1 — Complete Classification of c == 1 (mod 4), c >= 5 -/

theorem exists_bitlen {c : Nat} (hc : 5 ≤ c) :
    ∃ L, 3 ≤ L ∧ 2 ^ (L - 1) ≤ c ∧ c < 2 ^ L := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    by_cases h8 : c < 8
    · exact ⟨3, by omega, by omega, by omega⟩
    · have hhalf : 5 ≤ c / 2 ∨ c / 2 = 4 := by omega
      rcases hhalf with hge5 | heq4
      · rcases ih (c / 2) (by omega) hge5 with ⟨L, hL3, hlo, hhi⟩
        refine ⟨L + 1, by omega, ?_, ?_⟩
        · have hsub : L + 1 - 1 = L := by omega
          have hsub' : L - 1 + 1 = L := by omega
          rw [hsub, ← hsub', Nat.pow_succ]
          omega
        · rw [Nat.pow_succ]; omega
      · exact ⟨4, by omega, by omega, by omega⟩

/-- Exact carry-defect word for any c == 1 (mod 4) at x = 1 + 2^(L-1). -/
theorem defect_one_mod_four (c L : Nat) (hL : 3 ≤ L)
    (hlo : 2 ^ (L - 1) ≤ c) (hhi : c < 2 ^ L) (hmod : c % 4 = 1) :
    defect c (1 + 2 ^ (L - 1)) = 2 ^ L := by
  unfold defect
  have h1lt : 1 < 2 ^ (L - 1) := by
    have : 2 ^ 2 ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hclm' : clmul c (1 + 2 ^ (L - 1)) = c ^^^ (2 ^ (L - 1) * c) := by
    have h := clmul_add_shift c 1 1 (L - 1) h1lt
    simp only [Nat.mul_one, clmul_one] at h
    exact h
  rw [hclm']
  let r := c - 2 ^ (L - 1)
  let q := c / 4
  have hpowL : 2 ^ L = 2 * 2 ^ (L - 1) := by
    have heq : L = (L - 1) + 1 := by omega
    conv => lhs; rw [heq, Nat.pow_succ]
    omega
  have hpowL1 : 2 ^ (L + 1) = 4 * 2 ^ (L - 1) := by
    have heq : L + 1 = (L - 1) + 2 := by omega
    rw [heq, Nat.pow_add]; omega
  have hr_lt : r < 2 ^ (L - 1) := by omega
  have hc_r : c = r + 2 ^ (L - 1) := by omega
  have hc_q : c = 1 + 4 * q := by omega
  have hshift : 2 ^ (L - 1) * c = 2 ^ (L - 1) + 2 ^ (L + 1) * q := by
    calc 2 ^ (L - 1) * c = 2 ^ (L - 1) * (1 + 4 * q) := by rw [← hc_q]
      _ = 2 ^ (L - 1) + 4 * 2 ^ (L - 1) * q := by
        rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (L - 1)) 4]
      _ = 2 ^ (L - 1) + 2 ^ (L + 1) * q := by rw [← hpowL1]
  have hmul_val : c * (1 + 2 ^ (L - 1)) = (r + 2 ^ L) + 2 ^ (L + 1) * q := by
    calc c * (1 + 2 ^ (L - 1)) = c + 2 ^ (L - 1) * c := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm c (2 ^ (L - 1))]
      _ = (r + 2 ^ (L - 1)) + (2 ^ (L - 1) + 2 ^ (L + 1) * q) := by rw [← hc_r, hshift]
      _ = (r + 2 ^ L) + 2 ^ (L + 1) * q := by rw [hpowL]; omega
  have hxor_val : c ^^^ (2 ^ (L - 1) * c) = r + 2 ^ (L + 1) * q := by
    rw [hshift]
    conv => lhs; arg 1; rw [hc_r]
    have heq1 : r + 2 ^ (L - 1) = r + 2 ^ (L - 1) * 1 := by omega
    have heq2 : 2 ^ (L - 1) + 2 ^ (L + 1) * q = 0 + 2 ^ (L - 1) * (1 + 4 * q) := by
      rw [hpowL1, Nat.mul_add, Nat.mul_one, Nat.zero_add, ← Nat.mul_assoc,
          Nat.mul_comm (2 ^ (L - 1)) 4]
    rw [heq1, heq2, xor_block hr_lt (Nat.two_pow_pos (L - 1)), Nat.xor_zero]
    have h14 : 1 ^^^ (1 + 4 * q) = 4 * q := by
      have h := xor_block (a1 := 1) (a2 := 1) (b1 := 0) (b2 := q) (K := 2) (by omega) (by omega)
      simpa using h
    rw [h14, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (L - 1)) 4, ← hpowL1]
  rw [hmul_val, hxor_val]
  have hlt1 : r + 2 ^ L < 2 ^ (L + 1) := by rw [Nat.pow_succ]; omega
  have hlt2 : r < 2 ^ (L + 1) := by omega
  rw [xor_block hlt1 hlt2, Nat.xor_self, Nat.mul_zero, Nat.add_zero]
  have hrL : r < 2 ^ L := by omega
  have h := xor_block (a1 := r) (a2 := r) (b1 := 1) (b2 := 0) (K := L) hrL hrL
  simpa using h

/-- Infinite Theorem 1: Every multiplier c >= 5 with c == 1 (mod 4) has FULL carry-defect spectrum Nat. -/
theorem spectrum_one_mod_four (c : Nat) (hc : 5 ≤ c) (hmod : c % 4 = 1) :
    ∀ w : Nat, ∃ x : Nat, defectWeight c x = w := by
  rcases exists_bitlen hc with ⟨L, hL, hlo, hhi⟩
  have hw1 : ∃ x, defectWeight c x = 1 := by
    refine ⟨1 + 2 ^ (L - 1), ?_⟩
    unfold defectWeight
    rw [defect_one_mod_four c L hL hlo hhi hmod, popcount_pow_two]
  intro w
  by_cases hw : w = 0
  · subst hw; exact ⟨0, defectWeight_zero_right c⟩
  · exact semigroup_all_ge c 1 (by omega) (fun r hr => by
      have hr0 : r = 0 := by omega
      subst hr0; simpa using hw1) w (by omega)


/-! ## Section 6: Infinite Theorem 2 — Parametric Mersenne Family c = 2^m - 1 (all m >= 2) -/

/-- Exact bitwise complement identity for Mersenne masks: for u < 2^m, u ^^^ (2^m - 1) = (2^m - 1) - u. -/
theorem xor_mersenne {m u : Nat} (hu : u < 2 ^ m) :
    u ^^^ (2 ^ m - 1) = (2 ^ m - 1) - u := by
  induction m generalizing u with
  | zero =>
    simp at hu; subst hu; simp
  | succ m ih =>
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    have hpos : 1 ≤ 2 ^ m := Nat.two_pow_pos m
    have hu' : u / 2 < 2 ^ m := by rw [hpow] at hu; omega
    have hdecomp : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by rw [hpow]; omega
    have hu_eq : u = 2 * (u / 2) + u % 2 := by omega
    rw [hdecomp]
    conv => lhs; rw [hu_eq]
    rw [xor_two_mul_add (u / 2) (2 ^ m - 1) (u % 2) 1 (by omega) (by omega), ih hu']
    have hbit : u % 2 = 0 ∨ u % 2 = 1 := by omega
    rcases hbit with h | h <;> simp [h] <;> omega

theorem popcount_mersenne (m : Nat) : popcount (2 ^ m - 1) = m := by
  induction m with
  | zero => simp [popcount_zero]
  | succ m ih =>
    have hpos : 1 ≤ 2 ^ m := Nat.two_pow_pos m
    have heq : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by rw [Nat.pow_succ]; omega
    rw [heq, popcount_two_mul_add_one, ih]; omega

theorem mersenne_zero_defect_aux (m : Nat) (hm : 1 ≤ m) :
    ∀ (x r : Nat), r ≤ m - 1 →
      (genDefect (2 ^ m - 1) (2 ^ r - 1) (2 ^ r - 1) x = 0 ↔ isMSparse m r x = true) := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro r hr
    by_cases hx : x = 0
    · subst hx
      rw [genDefect_zero, Nat.xor_self, isMSparse]
      simp
    · have hmod := genDefect_mod_two (2 ^ m - 1) (2 ^ r - 1) (2 ^ r - 1) x hx
      have hemit : emit (2 ^ r - 1) (2 ^ r - 1) = 0 := by simp [emit]
      rw [hemit] at hmod
      have hdiv := genDefect_div_two (2 ^ m - 1) (2 ^ r - 1) (2 ^ r - 1) x hx
      have hzero_iff : genDefect (2 ^ m - 1) (2 ^ r - 1) (2 ^ r - 1) x = 0 ↔
          genDefect (2 ^ m - 1) (stepU (2 ^ m - 1) (2 ^ r - 1) (x % 2))
            (stepV (2 ^ m - 1) (2 ^ r - 1) (x % 2)) (x / 2) = 0 := by
        rw [← hdiv]
        constructor
        · intro hz; rw [hz]
        · intro hdz
          have hd := Nat.div_add_mod (genDefect (2 ^ m - 1) (2 ^ r - 1) (2 ^ r - 1) x) 2
          rw [hdz, hmod] at hd; omega
      rw [hzero_iff, isMSparse]
      simp only [hx, ↓reduceDIte]
      have hbit : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases hbit with hb0 | hb1
      · simp only [hb0, Nat.zero_ne_one, ↓reduceIte]
        have hstep : (2 ^ r - 1) / 2 = 2 ^ (r - 1) - 1 := by
          cases r with
          | zero => simp
          | succ r' =>
            have hpos : 1 ≤ 2 ^ r' := Nat.two_pow_pos r'
            have heq : 2 ^ (r' + 1) - 1 = 2 * (2 ^ r' - 1) + 1 := by rw [Nat.pow_succ]; omega
            simp only [Nat.add_sub_cancel]
            rw [heq]; omega
        have hU : stepU (2 ^ m - 1) (2 ^ r - 1) 0 = 2 ^ (r - 1) - 1 := by
          unfold stepU; simpa using hstep
        have hV : stepV (2 ^ m - 1) (2 ^ r - 1) 0 = 2 ^ (r - 1) - 1 := by
          unfold stepV; simpa using hstep
        rw [hU, hV]
        exact ih (x / 2) (by omega) (r - 1) (by omega)
      · simp only [hb1, ↓reduceIte]
        by_cases hr0 : r = 0
        · subst hr0
          simp only [↓reduceIte]
          have hstep : (2 ^ m - 1) / 2 = 2 ^ (m - 1) - 1 := by
            have heq : m = (m - 1) + 1 := by omega
            have hpos : 1 ≤ 2 ^ (m - 1) := Nat.two_pow_pos (m - 1)
            have h2 : 2 ^ m - 1 = 2 * (2 ^ (m - 1) - 1) + 1 := by
              conv => lhs; rw [heq, Nat.pow_succ]
              omega
            rw [h2]; omega
          have hU : stepU (2 ^ m - 1) (2 ^ 0 - 1) 1 = 2 ^ (m - 1) - 1 := by
            unfold stepU; simpa using hstep
          have hV : stepV (2 ^ m - 1) (2 ^ 0 - 1) 1 = 2 ^ (m - 1) - 1 := by
            unfold stepV; simpa using hstep
          rw [hU, hV]
          exact ih (x / 2) (by omega) (m - 1) (by omega)
        · simp only [hr0, ↓reduceIte, Bool.false_eq_true, iff_false]
          have hlt : 2 ^ r - 1 < 2 ^ m := by
            have : 2 ^ r ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
            have hpos : 1 ≤ 2 ^ r := Nat.two_pow_pos r
            omega
          have hvu : stepV (2 ^ m - 1) (2 ^ r - 1) 1 ≤ stepU (2 ^ m - 1) (2 ^ r - 1) 1 :=
            stepV_le_stepU _ _ _ 1 (Nat.le_refl _)
          intro hzd
          have heq := genDefect_eq_zero_imp_eq hvu hzd
          have hU : stepU (2 ^ m - 1) (2 ^ r - 1) 1 = (2 ^ r - 1 + (2 ^ m - 1)) / 2 := by
            simp [stepU]
          have hV : stepV (2 ^ m - 1) (2 ^ r - 1) 1 = ((2 ^ m - 1) - (2 ^ r - 1)) / 2 := by
            simp [stepV, xor_mersenne hlt]
          rw [hU, hV] at heq
          have hrpos : 2 ≤ 2 ^ r := by
            have : 2 ^ 1 ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) (by omega)
            omega
          have hmpos : 2 ^ r ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
          omega

/-- Exact Zero-Defect Characterization for Mersenne Multipliers:
    (2^m - 1) * x = clmul (2^m - 1) x  <->  x is m-sparse (generalized m-Fibbinary). -/
theorem mersenne_zero_defect_iff (m : Nat) (hm : 1 ≤ m) (x : Nat) :
    defect (2 ^ m - 1) x = 0 ↔ isMSparse m 0 x = true := by
  have h := mersenne_zero_defect_aux m hm x 0 (by omega)
  simpa [genDefect_zero_state] using h

/-- Parametric Diagonal-Escape Transducer Invariant:
    Once a Mersenne transducer leaves the diagonal (u = v) at b = 1, it lands on
    u' + v' = 2^m - 1 with u' >= 2^(m-1) > v', forcing >= 2 defect bits for ALL x. -/
theorem mersenne_no_weight_one_aux (m : Nat) (hm : 2 ≤ m) :
    ∀ (x r : Nat), r ≤ m - 1 →
      popcount (genDefect (2 ^ m - 1) (2 ^ r - 1) (2 ^ r - 1) x) ≠ 1 := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro r hr
    by_cases hx : x = 0
    · subst hx
      rw [genDefect_zero, Nat.xor_self, popcount_zero]
      omega
    · rw [popcount_genDefect_step (2 ^ m - 1) (2 ^ r - 1) (2 ^ r - 1) x hx]
      have hemit : emit (2 ^ r - 1) (2 ^ r - 1) = 0 := by simp [emit]
      rw [hemit, Nat.zero_add]
      have hbit : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases hbit with hb0 | hb1
      · rw [hb0]
        have hstep : (2 ^ r - 1) / 2 = 2 ^ (r - 1) - 1 := by
          cases r with
          | zero => simp
          | succ r' =>
            have hpos : 1 ≤ 2 ^ r' := Nat.two_pow_pos r'
            have heq : 2 ^ (r' + 1) - 1 = 2 * (2 ^ r' - 1) + 1 := by rw [Nat.pow_succ]; omega
            simp only [Nat.add_sub_cancel]
            rw [heq]; omega
        have hU : stepU (2 ^ m - 1) (2 ^ r - 1) 0 = 2 ^ (r - 1) - 1 := by
          unfold stepU; simpa using hstep
        have hV : stepV (2 ^ m - 1) (2 ^ r - 1) 0 = 2 ^ (r - 1) - 1 := by
          unfold stepV; simpa using hstep
        rw [hU, hV]
        exact ih (x / 2) (by omega) (r - 1) (by omega)
      · rw [hb1]
        by_cases hr0 : r = 0
        · subst hr0
          have hstep : (2 ^ m - 1) / 2 = 2 ^ (m - 1) - 1 := by
            have heq : m = (m - 1) + 1 := by omega
            have hpos : 1 ≤ 2 ^ (m - 1) := Nat.two_pow_pos (m - 1)
            have h2 : 2 ^ m - 1 = 2 * (2 ^ (m - 1) - 1) + 1 := by
              conv => lhs; rw [heq, Nat.pow_succ]
              omega
            rw [h2]; omega
          have hU : stepU (2 ^ m - 1) (2 ^ 0 - 1) 1 = 2 ^ (m - 1) - 1 := by
            unfold stepU; simpa using hstep
          have hV : stepV (2 ^ m - 1) (2 ^ 0 - 1) 1 = 2 ^ (m - 1) - 1 := by
            unfold stepV; simpa using hstep
          rw [hU, hV]
          exact ih (x / 2) (by omega) (m - 1) (by omega)
        · -- Escape off the diagonal: r >= 1, so u' + v' = 2^m - 1 and u' >= 2^(m-1) > v'
          let u' := stepU (2 ^ m - 1) (2 ^ r - 1) 1
          let v' := stepV (2 ^ m - 1) (2 ^ r - 1) 1
          have hpowm : 2 ^ m = 2 * 2 ^ (m - 1) := by
            have heq : m = (m - 1) + 1 := by omega
            conv => lhs; rw [heq, Nat.pow_succ]
            omega
          have hpowr : 2 ^ r = 2 * 2 ^ (r - 1) := by
            have heq : r = (r - 1) + 1 := by omega
            conv => lhs; rw [heq, Nat.pow_succ]
            omega
          have hpos_m1 : 2 ≤ 2 ^ (m - 1) := by
            have : 2 ^ 1 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
            omega
          have hpos_r1 : 1 ≤ 2 ^ (r - 1) := Nat.two_pow_pos (r - 1)
          have hr_le_m : 2 ^ (r - 1) ≤ 2 ^ (m - 1) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          have hlt : 2 ^ r - 1 < 2 ^ m := by omega
          have hu'_val : u' = 2 ^ (m - 1) + 2 ^ (r - 1) - 1 := by
            show (2 ^ r - 1 + 1 * (2 ^ m - 1)) / 2 = _
            rw [Nat.one_mul, hpowm, hpowr]; omega
          have hv'_val : v' = 2 ^ (m - 1) - 2 ^ (r - 1) := by
            show ((2 ^ r - 1) ^^^ (1 * (2 ^ m - 1))) / 2 = _
            rw [Nat.one_mul, xor_mersenne hlt, hpowm, hpowr]; omega
          have hsum : u' + v' = 2 ^ m - 1 := by omega
          have hu'_ge : 2 ^ (m - 1) ≤ u' := by omega
          have hv'_lt : v' < 2 ^ (m - 1) := by omega
          have hge2 : 2 ≤ popcount (genDefect (2 ^ m - 1) u' v' (x / 2)) := by
            by_cases hx2 : x / 2 = 0
            · rw [hx2, genDefect_zero]
              have hu'_lt : u' < 2 ^ m := by omega
              have hv'_eq : v' = u' ^^^ (2 ^ m - 1) := by
                rw [xor_mersenne hu'_lt]; omega
              have hxor : u' ^^^ v' = 2 ^ m - 1 := by
                rw [hv'_eq, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
              rw [hxor, popcount_mersenne]
              exact hm
            · rw [popcount_genDefect_step (2 ^ m - 1) u' v' (x / 2) hx2]
              have hemit' : emit u' v' = 1 := by
                unfold emit
                have hodd : (u' + v') % 2 = 1 := by rw [hsum, hpowm]; omega
                have hu2 : u' % 2 = 0 ∨ u' % 2 = 1 := by omega
                have hv2 : v' % 2 = 0 ∨ v' % 2 = 1 := by omega
                rcases hu2 with hu2 | hu2 <;> rcases hv2 with hv2 | hv2
                · omega
                · simp [hu2, hv2]
                · simp [hu2, hv2]
                · omega
              rw [hemit']
              let b' := (x / 2) % 2
              let u'' := stepU (2 ^ m - 1) u' b'
              let v'' := stepV (2 ^ m - 1) v' b'
              have hvu'' : v'' ≤ u'' := stepV_le_stepU _ _ _ b' (by omega)
              have hstrict : v'' < u'' := by
                have hb' : b' = 0 ∨ b' = 1 := by omega
                rcases hb' with hb'0 | hb'1
                · show (v' ^^^ (b' * (2 ^ m - 1))) / 2 < (u' + b' * (2 ^ m - 1)) / 2
                  rw [hb'0]; simp only [Nat.zero_mul, Nat.xor_zero, Nat.add_zero]
                  have hpow_m2 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
                    have heq : m - 1 = (m - 2) + 1 := by omega
                    conv => lhs; rw [heq, Nat.pow_succ]
                    omega
                  omega
                · show (v' ^^^ (b' * (2 ^ m - 1))) / 2 < (u' + b' * (2 ^ m - 1)) / 2
                  rw [hb'1, Nat.one_mul]
                  have hv'_ltm : v' < 2 ^ m := by omega
                  rw [xor_mersenne hv'_ltm]
                  omega
              have hnz : genDefect (2 ^ m - 1) u'' v'' (x / 2 / 2) ≠ 0 := by
                intro hzd
                have heq := genDefect_eq_zero_imp_eq hvu'' hzd
                omega
              have hpos := popcount_pos_of_ne_zero hnz
              exact Nat.add_le_add_left hpos 1
          exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega) hge2)

/-- Infinite Theorem 2 (Lower Bound): No Mersenne multiplier 2^m - 1 (m >= 2) ever produces weight 1. -/
theorem mersenne_no_weight_one (m : Nat) (hm : 2 ≤ m) (x : Nat) :
    defectWeight (2 ^ m - 1) x ≠ 1 := by
  have h := mersenne_no_weight_one_aux m hm x 0 (by omega)
  simpa [defectWeight, genDefect_zero_state] using h

theorem clmul_seven (c : Nat) : clmul c 7 = (c ^^^ (2 * c)) ^^^ (4 * c) := by
  have h : clmul c 7 = c ^^^ (2 * (c ^^^ (2 * c))) := by
    rw [clmul_pos c 7 (by omega), clmul_pos c 3 (by omega), clmul_pos c 1 (by omega), clmul_zero]
    change 1 * c ^^^ 2 * (1 * c ^^^ 2 * (1 * c ^^^ 2 * 0)) = _
    simp only [Nat.one_mul, Nat.mul_zero, Nat.xor_zero]
  rw [h, ← xor_two_mul, ← Nat.mul_assoc, ← Nat.xor_assoc]

theorem clmul_eleven (c : Nat) : clmul c 11 = (c ^^^ (2 * c)) ^^^ (8 * c) := by
  have h : clmul c 11 = c ^^^ (2 * (c ^^^ (2 * (2 * c)))) := by
    rw [clmul_pos c 11 (by omega), clmul_pos c 5 (by omega),
        clmul_pos c 2 (by omega), clmul_pos c 1 (by omega), clmul_zero]
    change 1 * c ^^^ 2 * (1 * c ^^^ 2 * (0 * c ^^^ 2 * (1 * c ^^^ 2 * 0))) = _
    simp only [Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.xor_zero, Nat.zero_xor]
  rw [h, ← xor_two_mul, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.xor_assoc]

theorem mersenne_xor_double (m : Nat) (hm : 1 ≤ m) :
    (2 ^ m - 1) ^^^ (2 * (2 ^ m - 1)) = 1 + 2 ^ m := by
  have hpos : 2 ≤ 2 ^ m := by
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    omega
  have heq : 2 * (2 ^ m - 1) = (2 ^ m - 2) + 2 ^ m * 1 := by omega
  have ha1 : 2 ^ m - 1 < 2 ^ m := by omega
  have ha2 : 2 ^ m - 2 < 2 ^ m := by omega
  rw [heq]
  have hb := xor_block (a1 := 2 ^ m - 1) (a2 := 2 ^ m - 2) (b1 := 0) (b2 := 1) ha1 ha2
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_xor] at hb
  rw [hb, Nat.mul_one, Nat.xor_comm, xor_mersenne ha2]
  omega

/-- Uniform closed-form weight-2 witness for all Mersenne multipliers c = 2^m - 1 (m >= 3). -/
theorem mersenne_defect_seven (m : Nat) (hm : 3 ≤ m) :
    defect (2 ^ m - 1) 7 = 2 ^ (m + 2) + 4 := by
  unfold defect
  rw [clmul_seven, mersenne_xor_double m (by omega)]
  have hpowm : 2 ^ m = 8 * 2 ^ (m - 3) := by
    have heq : m = (m - 3) + 3 := by omega
    conv => lhs; rw [heq, Nat.pow_add]
    omega
  have hpos3 : 1 ≤ 2 ^ (m - 3) := Nat.two_pow_pos (m - 3)
  have hclm_val : (1 + 2 ^ m) ^^^ (4 * (2 ^ m - 1)) = (2 ^ m - 3) + 2 ^ m * 2 := by
    have heq4 : 4 * (2 ^ m - 1) = (2 ^ m - 4) + 2 ^ m * 3 := by omega
    have h1eq : 1 + 2 ^ m = 1 + 2 ^ m * 1 := by omega
    have ha1 : 1 < 2 ^ m := by omega
    have ha2 : 2 ^ m - 4 < 2 ^ m := by omega
    rw [h1eq, heq4, xor_block ha1 ha2]
    have hx13 : (1 : Nat) ^^^ 3 = 2 := by decide
    have hx14 : 1 ^^^ (2 ^ m - 4) = 2 ^ m - 3 := by
      have h4d : 2 ^ m - 4 = 4 + 8 * (2 ^ (m - 3) - 1) := by rw [hpowm]; omega
      rw [h4d]
      have hb := xor_block (a1 := 1) (a2 := 4) (b1 := 0) (b2 := 2 ^ (m - 3) - 1)
                   (K := 3) (by omega) (by omega)
      have h23 : 2 ^ 3 = 8 := by decide
      have h14 : (1 : Nat) ^^^ 4 = 5 := by decide
      simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_xor, h23, h14] at hb
      rw [hb, hpowm]; omega
    rw [hx13, hx14]
  rw [hclm_val]
  have hmul7 : (2 ^ m - 1) * 7 = (2 ^ m - 7) + 2 ^ m * 6 := by omega
  rw [hmul7]
  have hlt7 : 2 ^ m - 7 < 2 ^ m := by omega
  have hlt3 : 2 ^ m - 3 < 2 ^ m := by omega
  rw [xor_block hlt7 hlt3]
  have hx62 : (6 : Nat) ^^^ 2 = 4 := by decide
  have hx73 : (2 ^ m - 7) ^^^ (2 ^ m - 3) = 4 := by
    have h7 : 2 ^ m - 7 = 1 + 8 * (2 ^ (m - 3) - 1) := by rw [hpowm]; omega
    have h3 : 2 ^ m - 3 = 5 + 8 * (2 ^ (m - 3) - 1) := by rw [hpowm]; omega
    rw [h7, h3]
    have hb := xor_block (a1 := 1) (a2 := 5) (b1 := 2 ^ (m - 3) - 1) (b2 := 2 ^ (m - 3) - 1)
                 (K := 3) (by omega) (by omega)
    have h23 : 2 ^ 3 = 8 := by decide
    have h15 : (1 : Nat) ^^^ 5 = 4 := by decide
    rw [h23, h15, Nat.xor_self, Nat.mul_zero, Nat.add_zero] at hb
    exact hb
  rw [hx62, hx73]
  have hpow2 : 2 ^ (m + 2) = 2 ^ m * 4 := by rw [Nat.pow_add]
  rw [hpow2, Nat.add_comm]

theorem mersenne_weight_two (m : Nat) (hm : 3 ≤ m) :
    defectWeight (2 ^ m - 1) 7 = 2 := by
  unfold defectWeight
  rw [mersenne_defect_seven m hm]
  have hlt : 4 < 2 ^ (m + 2) := by
    have : 2 ^ 5 ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have heq : 2 ^ (m + 2) + 4 = 4 + 2 ^ (m + 2) * 1 := by omega
  rw [heq, popcount_block hlt]
  have h4 : popcount 4 = 1 := by decide
  have h1 : popcount 1 = 1 := by decide
  rw [h4, h1]

/-- Uniform closed-form weight-3 witness for all Mersenne multipliers c = 2^m - 1 (m >= 4). -/
theorem mersenne_defect_w3 (m : Nat) (hm : 4 ≤ m) :
    defect (2 ^ m - 1) (11 * 2 ^ (m - 3) + 1) =
      2 ^ (2 * m) + 2 ^ (2 * m - 1) + 2 ^ (m - 2) := by
  unfold defect
  have hpos3 : 1 ≤ 2 ^ (m - 3) := Nat.two_pow_pos (m - 3)
  have h1lt : 1 < 2 ^ (m - 3) := by
    have : 2 ^ 1 ≤ 2 ^ (m - 3) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hpowm : 2 ^ m = 8 * 2 ^ (m - 3) := by
    have heq : m = (m - 3) + 3 := by omega
    conv => lhs; rw [heq, Nat.pow_add]
    omega
  have hpowm2 : 2 ^ (m - 2) = 2 * 2 ^ (m - 3) := by
    have heq : m - 2 = (m - 3) + 1 := by omega
    conv => lhs; rw [heq, Nat.pow_succ]
    omega
  have hpow2m3 : 2 ^ (2 * m - 3) = 2 ^ m * 2 ^ (m - 3) := by
    have heq : 2 * m - 3 = m + (m - 3) := by omega
    conv => lhs; rw [heq, Nat.pow_add]
  have hpow2m : 2 ^ (2 * m) = 8 * 2 ^ (2 * m - 3) := by
    have heq : 2 * m = (2 * m - 3) + 3 := by omega
    conv => lhs; rw [heq, Nat.pow_add]
    omega
  have hpow2m1 : 2 ^ (2 * m - 1) = 4 * 2 ^ (2 * m - 3) := by
    have heq : 2 * m - 1 = (2 * m - 3) + 2 := by omega
    conv => lhs; rw [heq, Nat.pow_add]
    omega
  have hclm_shift : clmul (2 ^ m - 1) (11 * 2 ^ (m - 3) + 1) =
      (2 ^ m - 1) ^^^ (2 ^ (m - 3) * clmul (2 ^ m - 1) 11) := by
    have h := clmul_add_shift (2 ^ m - 1) 1 11 (m - 3) h1lt
    rw [Nat.add_comm, Nat.mul_comm (2 ^ (m - 3)) 11] at h
    rw [h, clmul_one]
  have hclm11 : clmul (2 ^ m - 1) 11 = (2 ^ m - 7) + 2 ^ m * 6 := by
    rw [clmul_eleven, mersenne_xor_double m (by omega)]
    have heq8 : 8 * (2 ^ m - 1) = (2 ^ m - 8) + 2 ^ m * 7 := by omega
    have h1eq : 1 + 2 ^ m = 1 + 2 ^ m * 1 := by omega
    have ha1 : 1 < 2 ^ m := by omega
    have ha2 : 2 ^ m - 8 < 2 ^ m := by omega
    rw [h1eq, heq8, xor_block ha1 ha2]
    have hx17 : (1 : Nat) ^^^ 7 = 6 := by decide
    have hx18 : 1 ^^^ (2 ^ m - 8) = 2 ^ m - 7 := by
      have h8 : 2 ^ m - 8 = 0 + 8 * (2 ^ (m - 3) - 1) := by rw [hpowm]; omega
      rw [h8]
      have hb := xor_block (a1 := 1) (a2 := 0) (b1 := 0) (b2 := 2 ^ (m - 3) - 1)
                   (K := 3) (by omega) (by omega)
      have h23 : 2 ^ 3 = 8 := by decide
      simp only [Nat.mul_zero, Nat.add_zero, Nat.xor_zero, Nat.zero_xor, h23] at hb
      rw [hb, hpowm]; omega
    rw [hx17, hx18]
  have hclm_exact : clmul (2 ^ m - 1) (11 * 2 ^ (m - 3) + 1) =
      (2 ^ (m - 3) - 1) + 2 ^ (m - 3) * ((2 ^ m - 2) + 2 ^ m * 6) := by
    rw [hclm_shift, hclm11]
    have hsplit : 2 ^ m - 1 = (2 ^ (m - 3) - 1) + 2 ^ (m - 3) * 7 := by rw [hpowm]; omega
    have h0add : 2 ^ (m - 3) * (2 ^ m - 7 + 2 ^ m * 6) =
        0 + 2 ^ (m - 3) * (2 ^ m - 7 + 2 ^ m * 6) := by omega
    rw [hsplit, h0add]
    rw [xor_block (a1 := 2 ^ (m - 3) - 1) (a2 := 0) (by omega) (by omega), Nat.xor_zero]
    have h7lt : 7 < 2 ^ m := by omega
    have h7lt2 : 2 ^ m - 7 < 2 ^ m := by omega
    have hblk := xor_block (a1 := 7) (a2 := 2 ^ m - 7) (b1 := 0) (b2 := 6) h7lt h7lt2
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_xor] at hblk
    rw [hblk]
    have hx7 : 7 ^^^ (2 ^ m - 7) = 2 ^ m - 2 := by
      have h7d : 2 ^ m - 7 = 1 + 8 * (2 ^ (m - 3) - 1) := by rw [hpowm]; omega
      rw [h7d]
      have hb := xor_block (a1 := 7) (a2 := 1) (b1 := 0) (b2 := 2 ^ (m - 3) - 1)
                   (K := 3) (by omega) (by omega)
      have h23 : 2 ^ 3 = 8 := by decide
      have h71 : (7 : Nat) ^^^ 1 = 6 := by decide
      simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_xor, h23, h71] at hb
      rw [hb, hpowm]; omega
    rw [hx7]
  have hmul_exact : (2 ^ m - 1) * (11 * 2 ^ (m - 3) + 1) =
      (2 ^ (m - 3) - 1) + 2 ^ (m - 3) * ((2 ^ m - 4) + 2 ^ m * 10) := by
    have h1 : (2 ^ m - 1) * (11 * 2 ^ (m - 3) + 1) + (11 * 2 ^ (m - 3) + 1) =
        2 ^ m * (11 * 2 ^ (m - 3) + 1) := by
      have hpos : 1 ≤ 2 ^ m := Nat.two_pow_pos m
      calc (2 ^ m - 1) * (11 * 2 ^ (m - 3) + 1) + (11 * 2 ^ (m - 3) + 1)
          = (2 ^ m - 1 + 1) * (11 * 2 ^ (m - 3) + 1) := by rw [Nat.add_mul, Nat.one_mul]
        _ = 2 ^ m * (11 * 2 ^ (m - 3) + 1) := by rw [Nat.sub_add_cancel hpos]
    have h2 : 2 ^ m * (11 * 2 ^ (m - 3) + 1) =
        2 ^ (m - 3) * (11 * 2 ^ m) + 8 * 2 ^ (m - 3) := by
      rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm (2 ^ m) 11,
          Nat.mul_assoc, Nat.mul_comm (2 ^ m) (2 ^ (m - 3)), ← Nat.mul_assoc,
          Nat.mul_comm 11 (2 ^ (m - 3)), Nat.mul_assoc, hpowm]
    have h3 : (2 ^ (m - 3) - 1) + 2 ^ (m - 3) * ((2 ^ m - 4) + 2 ^ m * 10) +
        (11 * 2 ^ (m - 3) + 1) = 2 ^ (m - 3) * (11 * 2 ^ m) + 8 * 2 ^ (m - 3) := by
      have hle4 : 4 ≤ 2 ^ m := by omega
      have h4 : (2 ^ m - 4) + 2 ^ m * 10 + 4 = 11 * 2 ^ m := by omega
      have h5 : 2 ^ (m - 3) * ((2 ^ m - 4) + 2 ^ m * 10) + 4 * 2 ^ (m - 3) =
          2 ^ (m - 3) * (11 * 2 ^ m) := by
        rw [Nat.mul_comm 4 (2 ^ (m - 3)), ← Nat.mul_add, h4]
      omega
    omega
  rw [hmul_exact, hclm_exact]
  rw [xor_block (a1 := 2 ^ (m - 3) - 1) (a2 := 2 ^ (m - 3) - 1) (by omega) (by omega),
      Nat.xor_self, Nat.zero_add]
  have hlt4 : 2 ^ m - 4 < 2 ^ m := by omega
  have hlt2 : 2 ^ m - 2 < 2 ^ m := by omega
  rw [xor_block hlt4 hlt2]
  have hx106 : (10 : Nat) ^^^ 6 = 12 := by decide
  have hx42 : (2 ^ m - 4) ^^^ (2 ^ m - 2) = 2 := by
    have h4d : 2 ^ m - 4 = 4 + 8 * (2 ^ (m - 3) - 1) := by rw [hpowm]; omega
    have h2d : 2 ^ m - 2 = 6 + 8 * (2 ^ (m - 3) - 1) := by rw [hpowm]; omega
    rw [h4d, h2d]
    have hb := xor_block (a1 := 4) (a2 := 6) (b1 := 2 ^ (m - 3) - 1) (b2 := 2 ^ (m - 3) - 1)
                 (K := 3) (by omega) (by omega)
    have h23 : 2 ^ 3 = 8 := by decide
    have h46 : (4 : Nat) ^^^ 6 = 2 := by decide
    rw [h23, h46, Nat.xor_self, Nat.mul_zero, Nat.add_zero] at hb
    exact hb
  rw [hx106, hx42, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (m - 3)) (2 ^ m),
      ← hpow2m3, hpow2m, hpow2m1, hpowm2]
  omega

theorem mersenne_weight_three (m : Nat) (hm : 4 ≤ m) :
    defectWeight (2 ^ m - 1) (11 * 2 ^ (m - 3) + 1) = 3 := by
  unfold defectWeight
  rw [mersenne_defect_w3 m hm]
  have h1 : 2 ^ (m - 2) < 2 ^ (2 * m - 1) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have h2 : 2 ^ (2 * m) + 2 ^ (2 * m - 1) + 2 ^ (m - 2) =
      2 ^ (m - 2) + 2 ^ (2 * m - 1) * 3 := by
    have heq : 2 ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
      have : 2 * m = (2 * m - 1) + 1 := by omega
      conv => lhs; rw [this, Nat.pow_succ]
      omega
    omega
  rw [h2, popcount_block h1, popcount_pow_two]
  have h3 : popcount 3 = 2 := by decide
  rw [h3]

/-- Infinite Theorem 2 (Complete Spectrum Classification):
    For EVERY m >= 2, the carry-defect weight spectrum of 2^m - 1 is EXACTLY Nat \ {1}. -/
theorem mersenne_spectrum_classify (m : Nat) (hm : 2 ≤ m) :
    ∀ w : Nat, (∃ x : Nat, defectWeight (2 ^ m - 1) x = w) ↔ w ≠ 1 := by
  intro w
  constructor
  · rintro ⟨x, rfl⟩
    exact mersenne_no_weight_one m hm x
  · intro hw1
    by_cases hw0 : w = 0
    · subst hw0; exact ⟨0, defectWeight_zero_right (2 ^ m - 1)⟩
    · have hw2 : 2 ≤ w := by omega
      have hblock : ∀ r, r < 2 → ∃ x, defectWeight (2 ^ m - 1) x = 2 + r := by
        intro r hr
        have hcase : r = 0 ∨ r = 1 := by omega
        rcases hcase with rfl | rfl
        · by_cases hm2 : m = 2
          · subst hm2; exact ⟨3, by decide⟩
          · exact ⟨7, mersenne_weight_two m (by omega)⟩
        · by_cases hm2 : m = 2
          · subst hm2; exact ⟨7, by decide⟩
          · by_cases hm3 : m = 3
            · subst hm3; exact ⟨3, by decide⟩
            · exact ⟨11 * 2 ^ (m - 3) + 1, mersenne_weight_three m (by omega)⟩
      exact semigroup_all_ge (2 ^ m - 1) 2 (by omega) hblock w hw2


/-! ## Section 7: Concrete Certificate Compilations (c = 23, c = 175),
    Stealth Falsification (c = 211), Negative Mutation Tests, Sharpness & Non-Vacuity -/

-- Auto-synthesized exact backward-potential certificate for c = 23 (38 reachable states, depth = 6, B[0] = 2)

/-- Pure-kernel verification of the 38-state backward-potential certificate for c = 23. -/
theorem cert23_valid : checkTree 23 6 certTree23 certTree23 = true := by decide

/-- Pure-kernel verification of the 302-state backward-potential certificate for c = 175. -/
theorem cert175_valid : checkTree 175 9 certTree175 certTree175 = true := by decide

/-- Kernel-checked hostile mutation test: bumping root bVal of c = 23 from 2 to 3 is REJECTED. -/
theorem cert23_mutation_rejected :
    let bad := BinTree.bumpRootBVal 6 certTree23 1
    checkTree 23 6 bad bad = false := by decide

/-- Kernel-checked hostile mutation test: bumping root bVal of c = 175 from 3 to 4 is REJECTED. -/
theorem cert175_mutation_rejected :
    let bad := BinTree.bumpRootBVal 9 certTree175 1
    checkTree 175 9 bad bad = false := by decide

/-- Infinite Theorem 3a (Reuse Instance — non-Mersenne c = 23 = 0b10111):
    Every nonzero carry-defect of 23 has weight >= 2, and W(23) = Nat \ {1}. -/
theorem defectWeight_23_ge_two : ∀ x : Nat, defect 23 x ≠ 0 → 2 ≤ defectWeight 23 x := by
  have hRoot : BinTree.lookup 6 certTree23 0 = some ⟨0, 0, 0, 1, 0, 2⟩ := rfl
  exact PotentialCert.sound 23 6 0 certTree23 ⟨0, 0, 0, 1, 0, 2⟩ cert23_valid hRoot rfl rfl

theorem spectrum_23 : ∀ w : Nat, (∃ x : Nat, defectWeight 23 x = w) ↔ w ≠ 1 := by
  have hRoot : BinTree.lookup 6 certTree23 0 = some ⟨0, 0, 0, 1, 0, 2⟩ := rfl
  have hblock : ∀ r, r < 2 → ∃ x, defectWeight 23 x = 2 + r := by
    intro r hr
    have hc : r = 0 ∨ r = 1 := by omega
    rcases hc with rfl | rfl
    · exact ⟨9, by decide⟩
    · exact ⟨5, by decide⟩
  have hspec := spectrum_classify_of_cert 23 6 0 certTree23 ⟨0, 0, 0, 1, 0, 2⟩
                  cert23_valid hRoot rfl rfl (by decide) hblock
  intro w
  rw [hspec]
  dsimp only
  omega

/-- Infinite Theorem 3b (Headline Discovery — c = 175 = 0b10101111, minimal mu(c) = 3):
    For ALL x in Nat, (175 * x) ^^^ clmul(175, x) NEVER has Hamming weight 1 or 2! -/
theorem defectWeight_175_ge_three : ∀ x : Nat, defect 175 x ≠ 0 → 3 ≤ defectWeight 175 x := by
  have hRoot : BinTree.lookup 9 certTree175 0 = some ⟨0, 0, 0, 1, 0, 3⟩ := rfl
  exact PotentialCert.sound 175 9 0 certTree175 ⟨0, 0, 0, 1, 0, 3⟩ cert175_valid hRoot rfl rfl

/-- Exact Infinite Spectrum Classification of c = 175:
    W(175) = {0} U {w in Nat | w >= 3} = Nat \ {1, 2}. -/
theorem spectrum_175 :
    ∀ w : Nat, (∃ x : Nat, defectWeight 175 x = w) ↔ (w = 0 ∨ 3 ≤ w) := by
  have hRoot : BinTree.lookup 9 certTree175 0 = some ⟨0, 0, 0, 1, 0, 3⟩ := rfl
  have hblock : ∀ r, r < 3 → ∃ x, defectWeight 175 x = 3 + r := by
    intro r hr
    have hc : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · exact ⟨17, by decide⟩
    · exact ⟨11, by decide⟩
    · exact ⟨5, by decide⟩
  exact spectrum_classify_of_cert 175 9 0 certTree175 ⟨0, 0, 0, 1, 0, 3⟩
          cert175_valid hRoot rfl rfl (by decide) hblock

/-- Stealth Weight-1 Falsification Witness at c = 211 = 0b11010011:
    (a) Every 2-bit input x = 1 + 2^d (1 <= d < 8) has carry-defect weight >= 2. -/
theorem two_bit_211_ge_two :
    ∀ d : Nat, 1 ≤ d → d < 8 → 2 ≤ defectWeight 211 (1 + 2 ^ d) := by
  intro d hd1 hd8
  have hc : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- (b) Yet the 15-bit even-carry-pipeline witness x = 17125 = 0b100001011100101
    achieves EXACT carry-defect word 2^17 (Hamming weight 1)! -/
theorem stealth_211_weight_one :
    defect 211 17125 = 2 ^ 17 ∧ defectWeight 211 17125 = 1 := by
  constructor <;> decide

/-- (c) Hence c = 211 has FULL carry-defect spectrum W(211) = Nat despite having no 2-bit weight-1 witness. -/
theorem spectrum_211 : ∀ w : Nat, ∃ x : Nat, defectWeight 211 x = w := by
  intro w
  by_cases hw : w = 0
  · subst hw; exact ⟨0, defectWeight_zero_right 211⟩
  · exact semigroup_all_ge 211 1 (by omega) (fun r hr => by
      have hr0 : r = 0 := by omega
      subst hr0
      exact ⟨17125, stealth_211_weight_one.2⟩) w (by omega)

/-! ### Sharpness Counterexamples & Non-Vacuity Witnesses -/

/-- Sharpness 1: At c = 1 (violating c >= 5 in Theorem 1 and m >= 2 in Theorem 2),
    the spectrum collapses to {0}. -/
theorem sharpness_c_eq_one : ∀ x : Nat, defectWeight 1 x = 0 := defectWeight_one_left

/-- Sharpness 2: Flipping Mersenne 2^m - 1 to Fermat-like 2^m + 1 (m >= 2)
    restores weight 1 and full spectrum Nat. -/
theorem sharpness_mersenne_plus_one (m : Nat) (hm : 2 ≤ m) :
    ∀ w : Nat, ∃ x : Nat, defectWeight (2 ^ m + 1) x = w := by
  have h4 : 4 ≤ 2 ^ m := by
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    omega
  have hmod : (2 ^ m + 1) % 4 = 1 := by
    have heq : 2 ^ m = 4 * 2 ^ (m - 2) := by
      have : m = (m - 2) + 2 := by omega
      conv => lhs; rw [this, Nat.pow_add]
      omega
    omega
  exact spectrum_one_mod_four (2 ^ m + 1) (by omega) hmod

/-- Sharpness 3: Removing one leading '10' pair from 175 = 0b10101111 gives 47 = 0b101111,
    which breaks mu >= 3 by achieving weight 2 at x = 39 = 0b100111. -/
theorem sharpness_47_weight_two : defectWeight 47 39 = 2 := by decide

/-- Non-Vacuity Witnesses confirming every quantified hypothesis is constructively inhabited. -/
theorem nonvacuity_potentialCert :
    Nonempty { p : Nat × Nat × BinTree StateEntry // checkTree p.1 p.2.1 p.2.2 p.2.2 = true } :=
  ⟨⟨(175, 9, certTree175), cert175_valid⟩⟩

theorem nonvacuity_one_mod_four :
    Nonempty { c : Nat // 5 ≤ c ∧ c % 4 = 1 } :=
  ⟨⟨5, by omega, by omega⟩⟩

theorem nonvacuity_mersenne_nonzero_defect :
    Nonempty { p : Nat × Nat // 2 ≤ p.1 ∧ defect (2 ^ p.1 - 1) p.2 ≠ 0 ∧ defectWeight (2 ^ p.1 - 1) p.2 = 2 } :=
  ⟨⟨(3, 7), by omega, by decide, by decide⟩⟩

theorem nonvacuity_175_nonzero_defect :
    Nonempty { x : Nat // defect 175 x ≠ 0 ∧ defectWeight 175 x = 3 } :=
  ⟨⟨17, by decide, by decide⟩⟩

end CarryDefectEngine
