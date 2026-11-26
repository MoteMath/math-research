/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitwiseCarryAlgebra.Defs

/-!
# Bitwise Carry 2-Cocycles, Gray-Carry Transitions, Borrow Duality, and Exact Square Sums
-/

namespace BitwiseCarryAlgebra

/-! ### Part 1: Basic Bitwise Helpers, 2-Cocycle, Gray Linearity, and Borrow Duality -/

theorem xor_mod_two (a b : Nat) : (a ^^^ b) % 2 = (a % 2 + b % 2) % 2 := by
  have h := Nat.testBit_xor a b 0
  simp only [Nat.testBit_zero] at h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hab : (a ^^^ b) % 2 = 0 ∨ (a ^^^ b) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;>
    simp_all

theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor, ← Nat.testBit_div_two,
    ← Nat.testBit_div_two]

theorem carryWord_comm (x y : Nat) : carryWord x y = carryWord y x := by
  unfold carryWord
  rw [Nat.add_comm, Nat.xor_assoc, Nat.xor_comm x y, ← Nat.xor_assoc]

theorem carryWord_cocycle (x y z : Nat) :
    carryWord x y ^^^ carryWord (x + y) z ^^^ carryWord y z ^^^ carryWord x (y + z) = 0 := by
  unfold carryWord
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.zero_testBit, Nat.add_assoc]
  cases (x + (y + z)).testBit i <;>
    cases (x + y).testBit i <;>
    cases (y + z).testBit i <;>
    cases x.testBit i <;>
    cases y.testBit i <;>
    cases z.testBit i <;>
    rfl

theorem gray_xor (a b : Nat) : gray (a ^^^ b) = gray a ^^^ gray b := by
  unfold gray
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_shiftRight]
  cases a.testBit i <;> cases b.testBit i <;>
    cases a.testBit (1 + i) <;> cases b.testBit (1 + i) <;> rfl

theorem gray_add_xor_eq_gray_carryWord (x y : Nat) :
    gray (x + y) ^^^ gray x ^^^ gray y = gray (carryWord x y) := by
  unfold carryWord
  rw [gray_xor, gray_xor]

theorem borrowWord_eq_carryWord (x y : Nat) :
    borrowWord x y = carryWord (min x y) (max x y - min x y) := by
  unfold borrowWord carryWord
  have hsum : min x y + (max x y - min x y) = max x y := by omega
  rw [hsum]
  by_cases h : x ≤ y
  · have hmin : min x y = x := Nat.min_eq_left h
    have hmax : max x y = y := Nat.max_eq_right h
    rw [hmin, hmax]
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_xor]
    cases (y - x).testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  · have hmin : min x y = y := Nat.min_eq_right (by omega)
    have hmax : max x y = x := Nat.max_eq_left (by omega)
    rw [hmin, hmax]
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_xor]
    cases (x - y).testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl

/-! ### Part 2: Popcount, Carry-Popcount 2-Cocycle, and Gray-to-Blocks Identity -/

theorem popcnt_zero : popcnt 0 = 0 := by rw [popcnt]; rfl

theorem popcnt_step (n : Nat) : popcnt n = n % 2 + popcnt (n / 2) := by
  by_cases h : n = 0
  · subst h; simp [popcnt_zero]
  · rw [popcnt]; simp [h]

theorem popcnt_one : popcnt 1 = 1 := by
  rw [popcnt_step]; simp [popcnt_zero]

theorem popcnt_two_mul_add (q b : Nat) (hb : b ≤ 1) :
    popcnt (2 * q + b) = b + popcnt q := by
  rw [popcnt_step]
  have h1 : (2 * q + b) % 2 = b := by omega
  have h2 : (2 * q + b) / 2 = q := by omega
  rw [h1, h2]

theorem blocks_zero : blocks 0 = 0 := by rw [blocks]; rfl

theorem blocks_step (n : Nat) :
    blocks n = blocks (n / 2) + if n % 2 = 1 ∧ (n / 2) % 2 = 0 then 1 else 0 := by
  by_cases h : n = 0
  · subst h; simp [blocks_zero]
  · rw [blocks]; simp [h]

theorem blocks_one : blocks 1 = 1 := by
  rw [blocks_step]; simp [blocks_zero]

/-- Auxiliary carry word with incoming carry `c ∈ {0, 1}`. -/
private def cwC (c x y : Nat) : Nat := (x + y + c) ^^^ x ^^^ y

private theorem cwC_mod_two (c x y : Nat) (hc : c ≤ 1) : cwC c x y % 2 = c := by
  unfold cwC
  rw [xor_mod_two, xor_mod_two]
  omega

private theorem cwC_div_two (c a b q r : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    cwC c (2 * q + a) (2 * r + b) / 2 = cwC ((a + b + c) / 2) q r := by
  unfold cwC
  rw [xor_div_two, xor_div_two]
  have h1 : (2 * q + a + (2 * r + b) + c) / 2 = q + r + (a + b + c) / 2 := by omega
  have h2 : (2 * q + a) / 2 = q := by omega
  have h3 : (2 * r + b) / 2 = r := by omega
  rw [h1, h2, h3]

theorem popcnt_carryWord_with_carry :
    ∀ n x y c, x + y ≤ n → c ≤ 1 →
      popcnt (cwC c x y) + popcnt (x + y + c) = popcnt x + popcnt y + 2 * c
  | 0, x, y, c, hxy, hc => by
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst hx; subst hy
    have hcases : c = 0 ∨ c = 1 := by omega
    rcases hcases with rfl | rfl
    · simp [cwC, popcnt_zero]
    · simp [cwC, popcnt_zero, popcnt_one]
  | n + 1, x, y, c, hxy, hc => by
    have hx : x = 2 * (x / 2) + x % 2 := by omega
    have hy : y = 2 * (y / 2) + y % 2 := by omega
    let c' := (x % 2 + y % 2 + c) / 2
    have hc' : c' ≤ 1 := by omega
    have hdiv : cwC c x y / 2 = cwC c' (x / 2) (y / 2) := by
      have heq : cwC c x y = cwC c (2 * (x / 2) + x % 2) (2 * (y / 2) + y % 2) := by
        rw [← hx, ← hy]
      rw [heq]
      exact cwC_div_two c (x % 2) (y % 2) (x / 2) (y / 2) (by omega) (by omega)
    have hmod : cwC c x y % 2 = c := cwC_mod_two c x y hc
    have hsum : x + y + c = 2 * (x / 2 + y / 2 + c') + (x % 2 + y % 2 + c) % 2 := by omega
    have ih := popcnt_carryWord_with_carry n (x / 2) (y / 2) c' (by omega) hc'
    rw [popcnt_step (cwC c x y), hmod, hdiv]
    rw [hsum, popcnt_two_mul_add (x / 2 + y / 2 + c') ((x % 2 + y % 2 + c) % 2) (by omega)]
    rw [popcnt_step x, popcnt_step y]
    omega

theorem popcnt_carryWord_add_sum (x y : Nat) :
    popcnt (carryWord x y) + popcnt (x + y) = popcnt x + popcnt y := by
  have h := popcnt_carryWord_with_carry (x + y) x y 0 (Nat.le_refl _) (by omega)
  simpa [cwC, carryWord] using h

theorem carryPop_cocycle (x y z : Nat) :
    popcnt (carryWord x y) + popcnt (carryWord (x + y) z) =
    popcnt (carryWord y z) + popcnt (carryWord x (y + z)) := by
  have h1 := popcnt_carryWord_add_sum x y
  have h2 := popcnt_carryWord_add_sum (x + y) z
  have h3 := popcnt_carryWord_add_sum y z
  have h4 := popcnt_carryWord_add_sum x (y + z)
  rw [Nat.add_assoc] at h2
  omega

theorem popcnt_gray_aux : ∀ n : Nat, popcnt (gray n) + n % 2 = 2 * blocks n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h0 : n = 0
    · subst h0; simp [gray, popcnt_zero, blocks_zero]
    · have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      have ihm := ih (n / 2) hlt
      have hgm : gray n % 2 = (n % 2 + (n / 2) % 2) % 2 := by
        unfold gray
        rw [xor_mod_two]
        have hs : n >>> 1 = n / 2 := Nat.shiftRight_eq_div_pow n 1
        rw [hs]
      have hgd : gray n / 2 = gray (n / 2) := by
        unfold gray
        rw [xor_div_two]
        have hs1 : n >>> 1 = n / 2 := Nat.shiftRight_eq_div_pow n 1
        have hs2 : (n / 2) >>> 1 = (n / 2) / 2 := Nat.shiftRight_eq_div_pow (n / 2) 1
        rw [hs1, hs2]
      rw [popcnt_step (gray n), hgm, hgd, blocks_step n]
      split <;> omega

theorem carryWord_even (x y : Nat) : carryWord x y % 2 = 0 := by
  simpa [cwC, carryWord] using cwC_mod_two 0 x y (by omega)

theorem popcnt_gray_carryWord (x y : Nat) :
    popcnt (gray (x + y) ^^^ gray x ^^^ gray y) = 2 * carryBlocks x y := by
  rw [gray_add_xor_eq_gray_carryWord]
  have h := popcnt_gray_aux (carryWord x y)
  have hev := carryWord_even x y
  unfold carryBlocks
  omega

/-! ### Part 3: Exact Closed-Form Square Sums over `[0, 2^k) × [0, 2^k)` -/

theorem sumRange_two_mul (n : Nat) (f : Nat → Nat) :
    sumRange (2 * n) f = sumRange n (fun q => f (2 * q) + f (2 * q + 1)) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    have h : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [h, sumRange, sumRange, ih, sumRange]
    omega

theorem sumRange_add_fn (n : Nat) (f g : Nat → Nat) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp only [sumRange, ih]; omega

theorem sumRange_const (n c : Nat) : sumRange n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, ih, Nat.succ_mul]

private theorem sumSquare_succ (m : Nat) (f : Nat → Nat → Nat) :
    sumSquare (m + 1) f =
      sumSquare m (fun q r =>
        f (2 * q) (2 * r) + f (2 * q) (2 * r + 1) +
        f (2 * q + 1) (2 * r) + f (2 * q + 1) (2 * r + 1)) := by
  unfold sumSquare
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
  rw [hpow, sumRange_two_mul]
  congr 1; funext q
  rw [sumRange_two_mul, sumRange_two_mul, ← sumRange_add_fn]
  congr 1; funext r; dsimp only; omega

private theorem sumSquare_add_fn (m : Nat) (f g : Nat → Nat → Nat) :
    sumSquare m (fun q r => f q r + g q r) = sumSquare m f + sumSquare m g := by
  unfold sumSquare
  have h : (fun q => sumRange (2 ^ m) (fun r => f q r + g q r)) =
      (fun q => sumRange (2 ^ m) (fun r => f q r) + sumRange (2 ^ m) (fun r => g q r)) := by
    funext q; exact sumRange_add_fn (2 ^ m) (f q) (g q)
  rw [h, sumRange_add_fn]

private theorem sumSquare_const (m c : Nat) : sumSquare m (fun _ _ => c) = 4 ^ m * c := by
  unfold sumSquare
  have h : (fun (_ : Nat) => sumRange (2 ^ m) (fun _ => c)) = (fun (_ : Nat) => 2 ^ m * c) := by
    funext _; exact sumRange_const (2 ^ m) c
  rw [h, sumRange_const, ← Nat.mul_assoc, ← Nat.mul_pow]

theorem sumSquare_carryPop (k : Nat) :
    2 * sumSquare k (fun i j => popcnt (carryWord i j)) + 4 ^ k = k * 4 ^ k + 2 ^ k := by
  have hpair : ∀ m,
      2 * sumSquare m (fun i j => popcnt (cwC 0 i j)) + 4 ^ m = m * 4 ^ m + 2 ^ m ∧
      2 * sumSquare m (fun i j => popcnt (cwC 1 i j)) + 2 ^ m = (m + 3) * 4 ^ m := by
    intro m
    induction m with
    | zero =>
      constructor <;> simp [sumSquare, sumRange, cwC, popcnt_zero, popcnt_one]
    | succ m ih =>
      obtain ⟨ih0, ih1⟩ := ih
      have hstep_cell : ∀ c a b q r, c ≤ 1 → a ≤ 1 → b ≤ 1 →
          popcnt (cwC c (2 * q + a) (2 * r + b)) =
            c + popcnt (cwC ((a + b + c) / 2) q r) := by
        intro c a b q r hc ha hb
        rw [popcnt_step, cwC_mod_two c _ _ hc, cwC_div_two c a b q r ha hb]
      have h0eq : sumSquare (m + 1) (fun i j => popcnt (cwC 0 i j)) =
          3 * sumSquare m (fun q r => popcnt (cwC 0 q r)) +
          sumSquare m (fun q r => popcnt (cwC 1 q r)) := by
        rw [sumSquare_succ]
        have hf : (fun q r =>
              popcnt (cwC 0 (2 * q) (2 * r)) + popcnt (cwC 0 (2 * q) (2 * r + 1)) +
              popcnt (cwC 0 (2 * q + 1) (2 * r)) + popcnt (cwC 0 (2 * q + 1) (2 * r + 1))) =
            (fun q r =>
              ((popcnt (cwC 0 q r) + popcnt (cwC 0 q r)) + popcnt (cwC 0 q r)) +
              popcnt (cwC 1 q r)) := by
          funext q r
          have e00 := hstep_cell 0 0 0 q r (by omega) (by omega) (by omega)
          have e01 := hstep_cell 0 0 1 q r (by omega) (by omega) (by omega)
          have e10 := hstep_cell 0 1 0 q r (by omega) (by omega) (by omega)
          have e11 := hstep_cell 0 1 1 q r (by omega) (by omega) (by omega)
          simp only [Nat.add_zero] at e00 e01 e10 e11
          have d0 : (0 : Nat) / 2 = 0 := rfl
          have d1 : (1 : Nat) / 2 = 0 := rfl
          have d2 : (1 + 1 : Nat) / 2 = 1 := rfl
          rw [d0] at e00; rw [d1] at e01 e10; rw [d2] at e11
          omega
        rw [hf, sumSquare_add_fn, sumSquare_add_fn, sumSquare_add_fn]; omega
      have h1eq : sumSquare (m + 1) (fun i j => popcnt (cwC 1 i j)) =
          4 ^ m * 4 +
          sumSquare m (fun q r => popcnt (cwC 0 q r)) +
          3 * sumSquare m (fun q r => popcnt (cwC 1 q r)) := by
        rw [sumSquare_succ]
        have hf : (fun q r =>
              popcnt (cwC 1 (2 * q) (2 * r)) + popcnt (cwC 1 (2 * q) (2 * r + 1)) +
              popcnt (cwC 1 (2 * q + 1) (2 * r)) + popcnt (cwC 1 (2 * q + 1) (2 * r + 1))) =
            (fun q r =>
              (4 + popcnt (cwC 0 q r)) +
              ((popcnt (cwC 1 q r) + popcnt (cwC 1 q r)) + popcnt (cwC 1 q r))) := by
          funext q r
          have e00 := hstep_cell 1 0 0 q r (by omega) (by omega) (by omega)
          have e01 := hstep_cell 1 0 1 q r (by omega) (by omega) (by omega)
          have e10 := hstep_cell 1 1 0 q r (by omega) (by omega) (by omega)
          have e11 := hstep_cell 1 1 1 q r (by omega) (by omega) (by omega)
          simp only [Nat.add_zero] at e00 e01 e10 e11
          have d1 : (0 + 1 : Nat) / 2 = 0 := rfl
          have d2 : (1 + 1 : Nat) / 2 = 1 := rfl
          have d2' : (0 + 1 + 1 : Nat) / 2 = 1 := rfl
          have d3 : (1 + 1 + 1 : Nat) / 2 = 1 := rfl
          rw [d1] at e00; rw [d2'] at e01; rw [d2] at e10; rw [d3] at e11
          omega
        rw [hf, sumSquare_add_fn, sumSquare_add_fn, sumSquare_const, sumSquare_add_fn, sumSquare_add_fn]
        omega
      have h4s : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [Nat.pow_succ]; omega
      have h2s : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
      rw [h0eq, h1eq, h4s, h2s]
      have hm0 : (m + 3) * 4 ^ m = m * 4 ^ m + 3 * 4 ^ m := by rw [Nat.add_mul]
      have hm1 : (m + 1) * (4 * 4 ^ m) = 4 * (m * 4 ^ m) + 4 * 4 ^ m := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
      have hm2 : (m + 1 + 3) * (4 * 4 ^ m) = 4 * ((m + 3) * 4 ^ m) + 4 * 4 ^ m := by
        have : m + 1 + 3 = (m + 3) + 1 := by omega
        rw [this, Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
      rw [hm1, hm2]
      constructor <;> omega
  have h := (hpair k).1
  simpa [cwC, carryWord] using h

theorem sumSquare_carryBlocks (k : Nat) :
    8 * sumSquare k carryBlocks + 2 * 2 ^ k = (k + 2) * 4 ^ k := by
  have hpair : ∀ m,
      8 * sumSquare m (fun i j => blocks (cwC 0 i j)) + 2 * 2 ^ m = (m + 2) * 4 ^ m ∧
      8 * sumSquare m (fun i j => blocks (cwC 1 i j)) = (m + 6) * 4 ^ m + 2 * 2 ^ m := by
    intro m
    induction m with
    | zero =>
      constructor <;> simp [sumSquare, sumRange, cwC, blocks_zero, blocks_one]
    | succ m ih =>
      obtain ⟨ih0, ih1⟩ := ih
      have h0eq : sumSquare (m + 1) (fun i j => blocks (cwC 0 i j)) =
          3 * sumSquare m (fun q r => blocks (cwC 0 q r)) +
          sumSquare m (fun q r => blocks (cwC 1 q r)) := by
        rw [sumSquare_succ]
        have hf : (fun q r =>
              blocks (cwC 0 (2 * q) (2 * r)) + blocks (cwC 0 (2 * q) (2 * r + 1)) +
              blocks (cwC 0 (2 * q + 1) (2 * r)) + blocks (cwC 0 (2 * q + 1) (2 * r + 1))) =
            (fun q r =>
              ((blocks (cwC 0 q r) + blocks (cwC 0 q r)) + blocks (cwC 0 q r)) +
              blocks (cwC 1 q r)) := by
          funext q r
          have d00 := cwC_div_two 0 0 0 q r (by omega) (by omega)
          have d01 := cwC_div_two 0 0 1 q r (by omega) (by omega)
          have d10 := cwC_div_two 0 1 0 q r (by omega) (by omega)
          have d11 := cwC_div_two 0 1 1 q r (by omega) (by omega)
          simp only [Nat.add_zero] at d00 d01 d10 d11
          have e0 : (0 : Nat) / 2 = 0 := rfl
          have e1 : (1 : Nat) / 2 = 0 := rfl
          have e2 : (1 + 1 : Nat) / 2 = 1 := rfl
          rw [e0] at d00; rw [e1] at d01 d10; rw [e2] at d11
          rw [blocks_step (cwC 0 (2 * q) (2 * r)), cwC_mod_two 0 (2 * q) (2 * r) (by omega), d00]
          rw [blocks_step (cwC 0 (2 * q) (2 * r + 1)), cwC_mod_two 0 (2 * q) (2 * r + 1) (by omega), d01]
          rw [blocks_step (cwC 0 (2 * q + 1) (2 * r)), cwC_mod_two 0 (2 * q + 1) (2 * r) (by omega), d10]
          rw [blocks_step (cwC 0 (2 * q + 1) (2 * r + 1)), cwC_mod_two 0 (2 * q + 1) (2 * r + 1) (by omega), d11]
          simp only [Nat.zero_ne_one, false_and, ↓reduceIte, Nat.add_zero]
        rw [hf, sumSquare_add_fn, sumSquare_add_fn, sumSquare_add_fn]; omega
      have h1eq : sumSquare (m + 1) (fun i j => blocks (cwC 1 i j)) =
          4 ^ m * 1 +
          sumSquare m (fun q r => blocks (cwC 0 q r)) +
          3 * sumSquare m (fun q r => blocks (cwC 1 q r)) := by
        rw [sumSquare_succ]
        have hf : (fun q r =>
              blocks (cwC 1 (2 * q) (2 * r)) + blocks (cwC 1 (2 * q) (2 * r + 1)) +
              blocks (cwC 1 (2 * q + 1) (2 * r)) + blocks (cwC 1 (2 * q + 1) (2 * r + 1))) =
            (fun q r =>
              (1 + blocks (cwC 0 q r)) +
              ((blocks (cwC 1 q r) + blocks (cwC 1 q r)) + blocks (cwC 1 q r))) := by
          funext q r
          have d00 := cwC_div_two 1 0 0 q r (by omega) (by omega)
          have d01 := cwC_div_two 1 0 1 q r (by omega) (by omega)
          have d10 := cwC_div_two 1 1 0 q r (by omega) (by omega)
          have d11 := cwC_div_two 1 1 1 q r (by omega) (by omega)
          simp only [Nat.add_zero] at d00 d01 d10 d11
          have e1 : (0 + 1 : Nat) / 2 = 0 := rfl
          have e2 : (1 + 1 : Nat) / 2 = 1 := rfl
          have e2' : (0 + 1 + 1 : Nat) / 2 = 1 := rfl
          have e3 : (1 + 1 + 1 : Nat) / 2 = 1 := rfl
          rw [e1] at d00; rw [e2'] at d01; rw [e2] at d10; rw [e3] at d11
          have hp0 := cwC_mod_two 0 q r (by omega)
          have hp1 := cwC_mod_two 1 q r (by omega)
          rw [blocks_step (cwC 1 (2 * q) (2 * r)), cwC_mod_two 1 (2 * q) (2 * r) (by omega), d00]
          rw [blocks_step (cwC 1 (2 * q) (2 * r + 1)), cwC_mod_two 1 (2 * q) (2 * r + 1) (by omega), d01]
          rw [blocks_step (cwC 1 (2 * q + 1) (2 * r)), cwC_mod_two 1 (2 * q + 1) (2 * r) (by omega), d10]
          rw [blocks_step (cwC 1 (2 * q + 1) (2 * r + 1)), cwC_mod_two 1 (2 * q + 1) (2 * r + 1) (by omega), d11]
          simp only [hp0, hp1, and_self, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_zero]
          omega
        rw [hf, sumSquare_add_fn, sumSquare_add_fn, sumSquare_const, sumSquare_add_fn, sumSquare_add_fn]
        omega
      have h4s : 4 ^ (m + 1) = 4 * 4 ^ m := by rw [Nat.pow_succ]; omega
      have h2s : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
      rw [h0eq, h1eq, h4s, h2s]
      have hm0 : (m + 6) * 4 ^ m = (m + 2) * 4 ^ m + 4 * 4 ^ m := by
        have : m + 6 = (m + 2) + 4 := by omega
        rw [this, Nat.add_mul]
      have hm1 : (m + 1 + 2) * (4 * 4 ^ m) = 4 * ((m + 2) * 4 ^ m) + 4 * 4 ^ m := by
        have : m + 1 + 2 = (m + 2) + 1 := by omega
        rw [this, Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
      have hm2 : (m + 1 + 6) * (4 * 4 ^ m) = 4 * ((m + 6) * 4 ^ m) + 4 * 4 ^ m := by
        have : m + 1 + 6 = (m + 6) + 1 := by omega
        rw [this, Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
      rw [hm1, hm2]
      constructor <;> omega
  exact (hpair k).1

private theorem blocks_pos_of_ne_zero (u : Nat) (hu : u ≠ 0) : 1 ≤ blocks u := by
  induction u using Nat.strongRecOn with
  | ind u ihu =>
    rw [blocks_step u]
    by_cases hd : u / 2 = 0
    · have hm1 : u % 2 = 1 := by omega
      have hm2 : (u / 2) % 2 = 0 := by omega
      simp [hm1, hm2]
    · have hlt : u / 2 < u := Nat.div_lt_self (by omega) (by omega)
      have := ihu (u / 2) hlt hd
      omega

theorem count_zero_and_one_carryBlock (k : Nat) :
    sumSquare k (fun i j => if carryBlocks i j = 0 then 1 else 0) = 3 ^ k ∧
    2 * sumSquare (k + 2) (fun i j => if carryBlocks i j = 1 then 1 else 0) =
      (k + 2) * (k + 7) * 3 ^ k := by
  let ind (v c i j : Nat) := if blocks (cwC c i j) = v then 1 else 0
  have htriple : ∀ m,
      sumSquare m (ind 0 0) = 3 ^ m ∧
      3 * sumSquare m (ind 1 1) = (m + 3) * 3 ^ m ∧
      18 * sumSquare m (ind 1 0) = m * (m + 5) * 3 ^ m := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> simp [ind, sumSquare, sumRange, cwC, blocks_zero, blocks_one]
    | succ m ih =>
      obtain ⟨ihZ0, ihC1, ihC0⟩ := ih
      have hZ0_eq : sumSquare (m + 1) (ind 0 0) = 3 * sumSquare m (ind 0 0) := by
        rw [sumSquare_succ]
        have hf : (fun q r =>
              ind 0 0 (2 * q) (2 * r) + ind 0 0 (2 * q) (2 * r + 1) +
              ind 0 0 (2 * q + 1) (2 * r) + ind 0 0 (2 * q + 1) (2 * r + 1)) =
            (fun q r => (ind 0 0 q r + ind 0 0 q r) + ind 0 0 q r) := by
          funext q r
          have d00 := cwC_div_two 0 0 0 q r (by omega) (by omega)
          have d01 := cwC_div_two 0 0 1 q r (by omega) (by omega)
          have d10 := cwC_div_two 0 1 0 q r (by omega) (by omega)
          have d11 := cwC_div_two 0 1 1 q r (by omega) (by omega)
          simp only [Nat.add_zero] at d00 d01 d10 d11
          have e0 : (0 : Nat) / 2 = 0 := rfl
          have e1 : (1 : Nat) / 2 = 0 := rfl
          have e2 : (1 + 1 : Nat) / 2 = 1 := rfl
          rw [e0] at d00; rw [e1] at d01 d10; rw [e2] at d11
          have hne0 : blocks (cwC 1 q r) ≠ 0 := by
            have hp : cwC 1 q r % 2 = 1 := cwC_mod_two 1 q r (by omega)
            have := blocks_pos_of_ne_zero (cwC 1 q r) (by omega)
            omega
          dsimp only [ind]
          rw [blocks_step (cwC 0 (2 * q) (2 * r)), cwC_mod_two 0 (2 * q) (2 * r) (by omega), d00]
          rw [blocks_step (cwC 0 (2 * q) (2 * r + 1)), cwC_mod_two 0 (2 * q) (2 * r + 1) (by omega), d01]
          rw [blocks_step (cwC 0 (2 * q + 1) (2 * r)), cwC_mod_two 0 (2 * q + 1) (2 * r) (by omega), d10]
          rw [blocks_step (cwC 0 (2 * q + 1) (2 * r + 1)), cwC_mod_two 0 (2 * q + 1) (2 * r + 1) (by omega), d11]
          simp only [Nat.zero_ne_one, false_and, ↓reduceIte, Nat.add_zero, hne0]
        rw [hf, sumSquare_add_fn, sumSquare_add_fn]; omega
      have hC1_eq : sumSquare (m + 1) (ind 1 1) =
          sumSquare m (ind 0 0) + 3 * sumSquare m (ind 1 1) := by
        rw [sumSquare_succ]
        have hf : (fun q r =>
              ind 1 1 (2 * q) (2 * r) + ind 1 1 (2 * q) (2 * r + 1) +
              ind 1 1 (2 * q + 1) (2 * r) + ind 1 1 (2 * q + 1) (2 * r + 1)) =
            (fun q r => ind 0 0 q r + ((ind 1 1 q r + ind 1 1 q r) + ind 1 1 q r)) := by
          funext q r
          have d00 := cwC_div_two 1 0 0 q r (by omega) (by omega)
          have d01 := cwC_div_two 1 0 1 q r (by omega) (by omega)
          have d10 := cwC_div_two 1 1 0 q r (by omega) (by omega)
          have d11 := cwC_div_two 1 1 1 q r (by omega) (by omega)
          simp only [Nat.add_zero] at d00 d01 d10 d11
          have e1 : (0 + 1 : Nat) / 2 = 0 := rfl
          have e2 : (1 + 1 : Nat) / 2 = 1 := rfl
          have e2' : (0 + 1 + 1 : Nat) / 2 = 1 := rfl
          have e3 : (1 + 1 + 1 : Nat) / 2 = 1 := rfl
          rw [e1] at d00; rw [e2'] at d01; rw [e2] at d10; rw [e3] at d11
          have hp0 := cwC_mod_two 0 q r (by omega)
          have hp1 := cwC_mod_two 1 q r (by omega)
          dsimp only [ind]
          rw [blocks_step (cwC 1 (2 * q) (2 * r)), cwC_mod_two 1 (2 * q) (2 * r) (by omega), d00]
          rw [blocks_step (cwC 1 (2 * q) (2 * r + 1)), cwC_mod_two 1 (2 * q) (2 * r + 1) (by omega), d01]
          rw [blocks_step (cwC 1 (2 * q + 1) (2 * r)), cwC_mod_two 1 (2 * q + 1) (2 * r) (by omega), d10]
          rw [blocks_step (cwC 1 (2 * q + 1) (2 * r + 1)), cwC_mod_two 1 (2 * q + 1) (2 * r + 1) (by omega), d11]
          simp only [hp0, hp1, and_self, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_zero]
          have hiff : (blocks (cwC 0 q r) + 1 = 1) ↔ (blocks (cwC 0 q r) = 0) := by omega
          simp only [hiff]; omega
        rw [hf, sumSquare_add_fn, sumSquare_add_fn, sumSquare_add_fn]; omega
      have hC0_eq : sumSquare (m + 1) (ind 1 0) =
          3 * sumSquare m (ind 1 0) + sumSquare m (ind 1 1) := by
        rw [sumSquare_succ]
        have hf : (fun q r =>
              ind 1 0 (2 * q) (2 * r) + ind 1 0 (2 * q) (2 * r + 1) +
              ind 1 0 (2 * q + 1) (2 * r) + ind 1 0 (2 * q + 1) (2 * r + 1)) =
            (fun q r => ((ind 1 0 q r + ind 1 0 q r) + ind 1 0 q r) + ind 1 1 q r) := by
          funext q r
          have d00 := cwC_div_two 0 0 0 q r (by omega) (by omega)
          have d01 := cwC_div_two 0 0 1 q r (by omega) (by omega)
          have d10 := cwC_div_two 0 1 0 q r (by omega) (by omega)
          have d11 := cwC_div_two 0 1 1 q r (by omega) (by omega)
          simp only [Nat.add_zero] at d00 d01 d10 d11
          have e0 : (0 : Nat) / 2 = 0 := rfl
          have e1 : (1 : Nat) / 2 = 0 := rfl
          have e2 : (1 + 1 : Nat) / 2 = 1 := rfl
          rw [e0] at d00; rw [e1] at d01 d10; rw [e2] at d11
          dsimp only [ind]
          rw [blocks_step (cwC 0 (2 * q) (2 * r)), cwC_mod_two 0 (2 * q) (2 * r) (by omega), d00]
          rw [blocks_step (cwC 0 (2 * q) (2 * r + 1)), cwC_mod_two 0 (2 * q) (2 * r + 1) (by omega), d01]
          rw [blocks_step (cwC 0 (2 * q + 1) (2 * r)), cwC_mod_two 0 (2 * q + 1) (2 * r) (by omega), d10]
          rw [blocks_step (cwC 0 (2 * q + 1) (2 * r + 1)), cwC_mod_two 0 (2 * q + 1) (2 * r + 1) (by omega), d11]
          simp only [Nat.zero_ne_one, false_and, ↓reduceIte, Nat.add_zero]
        rw [hf, sumSquare_add_fn, sumSquare_add_fn, sumSquare_add_fn]; omega
      have h3s : 3 ^ (m + 1) = 3 * 3 ^ m := by rw [Nat.pow_succ]; omega
      rw [hZ0_eq, hC1_eq, hC0_eq, h3s]
      refine ⟨by omega, ?_, ?_⟩
      · have h1 : (m + 1 + 3) * (3 * 3 ^ m) = 3 * ((m + 3) * 3 ^ m) + 3 * 3 ^ m := by
          have : m + 1 + 3 = (m + 3) + 1 := by omega
          rw [this, Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
        omega
      · have hpoly : (m + 1) * (m + 1 + 5) = m * (m + 5) + 2 * (m + 3) := by
          have : m + 1 + 5 = (m + 5) + 1 := by omega
          rw [this, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
          omega
        have h2 : (m + 1) * (m + 1 + 5) * (3 * 3 ^ m) =
            3 * (m * (m + 5) * 3 ^ m) + 6 * ((m + 3) * 3 ^ m) := by
          rw [hpoly, Nat.add_mul]
          have ha : m * (m + 5) * (3 * 3 ^ m) = 3 * (m * (m + 5) * 3 ^ m) := by
            rw [Nat.mul_left_comm]
          have hb : 2 * (m + 3) * (3 * 3 ^ m) = 6 * ((m + 3) * 3 ^ m) := by
            rw [Nat.mul_assoc, Nat.mul_left_comm (m + 3) 3, ← Nat.mul_assoc]
          omega
        omega
  refine ⟨?_, ?_⟩
  · exact (htriple k).1
  · have h := (htriple (k + 2)).2.2
    have h3 : 3 ^ (k + 2) = 9 * 3 ^ k := by
      rw [Nat.pow_succ, Nat.pow_succ]; omega
    rw [h3] at h
    have hsim : (k + 2) * (k + 2 + 5) * (9 * 3 ^ k) = 9 * ((k + 2) * (k + 7) * 3 ^ k) := by
      have : k + 2 + 5 = k + 7 := by omega
      rw [this, Nat.mul_left_comm]
    have hfinal : 2 * sumSquare (k + 2) (ind 1 0) = (k + 2) * (k + 7) * 3 ^ k := by omega
    exact hfinal

end BitwiseCarryAlgebra
