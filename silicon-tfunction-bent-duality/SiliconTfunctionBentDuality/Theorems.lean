import SiliconTfunctionBentDuality.Defs

namespace SiliconBent
/-- Helper: `(2 * n).testBit (j + 1) = n.testBit j`. -/
theorem testBit_two_mul_succ (n j : Nat) : (2 * n).testBit (j + 1) = n.testBit j := by
  rw [Nat.testBit_succ]; congr 1; omega

/-- Helper: `(2 * n + 1).testBit (j + 1) = n.testBit j`. -/
theorem testBit_two_mul_add_one_succ (n j : Nat) : (2 * n + 1).testBit (j + 1) = n.testBit j := by
  rw [Nat.testBit_succ]; congr 1; omega

/-- Helper: if `x < 2 ^ i`, then `x.testBit i = false`. -/
theorem testBit_false_of_lt_pow2 (x i : Nat) (h : x < 2 ^ i) : x.testBit i = false := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]
  rfl

private theorem bitParityAux_eq_of_le (fuel n : Nat) (h : n ≤ fuel) :
    bitParityAux fuel n = bitParity n := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn; rfl
  | succ fuel ih =>
    cases n with
    | zero => rfl
    | succ m =>
      unfold bitParity
      simp only [bitParityAux, Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
      have hdiv_le_fuel : (m + 1) / 2 ≤ fuel := by omega
      have hdiv_le_m : (m + 1) / 2 ≤ m := by omega
      rw [ih ((m + 1) / 2) hdiv_le_fuel]
      -- also relate `bitParityAux m ((m+1)/2)` via a quick lemma:
      have haux : ∀ f1 f2 x, x ≤ f1 → x ≤ f2 → bitParityAux f1 x = bitParityAux f2 x := by
        intro f1
        induction f1 with
        | zero =>
          intro f2 x hx1 _
          have hx0 : x = 0 := by omega
          subst hx0
          cases f2 <;> rfl
        | succ f1 ih1 =>
          intro f2 x hx1 hx2
          cases f2 with
          | zero =>
            have hx0 : x = 0 := by omega
            subst hx0; rfl
          | succ f2 =>
            simp only [bitParityAux]
            by_cases hx0 : x = 0
            · subst hx0; rfl
            · simp only [hx0, beq_iff_eq, ↓reduceIte]
              rw [ih1 f2 (x / 2) (by omega) (by omega)]
      have hself : bitParityAux m ((m + 1) / 2) = bitParity ((m + 1) / 2) :=
        haux m ((m + 1) / 2) ((m + 1) / 2) hdiv_le_m (Nat.le_refl _)
      rw [hself]

theorem bitParity_zero : bitParity 0 = false := rfl

theorem bitParity_eq (n : Nat) (h : n ≠ 0) :
    bitParity n = xor (n % 2 == 1) (bitParity (n / 2)) := by
  cases n with
  | zero => exact absurd rfl h
  | succ m =>
    unfold bitParity
    simp only [bitParityAux, Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
    rw [bitParityAux_eq_of_le m ((m + 1) / 2) (by omega)]
    rfl

theorem bitParity_two_mul (n : Nat) : bitParity (2 * n) = bitParity n := by
  by_cases h : n = 0
  · subst h; rfl
  · rw [bitParity_eq (2 * n) (by omega)]
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n) / 2 = n := by omega
    simp [h1, h2]

theorem bitParity_two_mul_add_one (n : Nat) : bitParity (2 * n + 1) = !(bitParity n) := by
  rw [bitParity_eq (2 * n + 1) (by omega)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  simp [h1, h2]

theorem bitParity_step (n : Nat) :
    bitParity n = xor (n % 2 == 1) (bitParity (n / 2)) := by
  by_cases h : n = 0
  · subst h; simp [bitParity_zero]
  · exact bitParity_eq n h

theorem bitParity_xor : ∀ a b : Nat, bitParity (a ^^^ b) = xor (bitParity a) (bitParity b) := by
  intro a
  refine Nat.strongRecOn (motive := fun a => ∀ b, bitParity (a ^^^ b) = xor (bitParity a) (bitParity b)) a ?_
  intro a ih b
  by_cases ha : a = 0
  · subst ha; simp [bitParity_zero]
  · rw [bitParity_step (a ^^^ b), bitParity_step a, bitParity_step b]
    have hdiv : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp [Nat.testBit_div_two, Nat.testBit_xor]
    have hmod : ((a ^^^ b) % 2 == 1) = xor (a % 2 == 1) (b % 2 == 1) := by
      have htb := Nat.testBit_xor a b 0
      simp [Nat.testBit_zero] at htb
      cases h1 : (a % 2 == 1) <;> cases h2 : (b % 2 == 1) <;> simp_all
    rw [hdiv, hmod, ih (a / 2) (by omega) (b / 2)]
    cases (a % 2 == 1) <;> cases (b % 2 == 1) <;> cases bitParity (a / 2) <;> cases bitParity (b / 2) <;> rfl

theorem innerParity_comm (x y : Nat) : innerParity x y = innerParity y x := by
  simp [innerParity, Nat.and_comm]

theorem innerParity_zero_left (y : Nat) : innerParity 0 y = false := by
  simp [innerParity, bitParity_zero]

theorem innerParity_zero_right (x : Nat) : innerParity x 0 = false := by
  simp [innerParity, bitParity_zero]

theorem innerParity_xor_left (a b y : Nat) :
    innerParity (a ^^^ b) y = xor (innerParity a y) (innerParity b y) := by
  unfold innerParity
  have h : (a ^^^ b) &&& y = (a &&& y) ^^^ (b &&& y) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Nat.testBit_xor, Bool.and_xor_distrib_right]
  rw [h, bitParity_xor]

theorem innerParity_xor_right (x a b : Nat) :
    innerParity x (a ^^^ b) = xor (innerParity x a) (innerParity x b) := by
  rw [innerParity_comm, innerParity_xor_left, innerParity_comm a x, innerParity_comm b x]

theorem innerParity_two_mul (x w : Nat) :
    innerParity (2 * x) w = innerParity x (w / 2) := by
  unfold innerParity
  have h : (2 * x) &&& w = 2 * (x &&& (w / 2)) := by
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ j => rw [Nat.testBit_and, testBit_two_mul_succ, testBit_two_mul_succ, Nat.testBit_and, Nat.testBit_div_two]
  rw [h, bitParity_two_mul]

theorem innerParity_two_mul_add_one (x w : Nat) :
    innerParity (2 * x + 1) w = xor (w % 2 == 1) (innerParity x (w / 2)) := by
  unfold innerParity
  have h : (2 * x + 1) &&& w = 2 * (x &&& (w / 2)) + (w % 2) := by
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero =>
      simp [Nat.testBit_zero]
    | succ j =>
      have h1 : (2 * (x &&& (w / 2)) + w % 2).testBit (j + 1) = (x &&& (w / 2)).testBit j := by
        rw [Nat.testBit_succ]; congr 1; omega
      rw [Nat.testBit_and, testBit_two_mul_add_one_succ, h1, Nat.testBit_and, Nat.testBit_div_two]
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one w with hw | hw
  · simp [hw, bitParity_two_mul]
  · simp [hw, bitParity_two_mul_add_one]

theorem innerParity_mod_pow2 (k x y : Nat) (hx : x < 2 ^ k) :
    innerParity x (y % 2 ^ k) = innerParity x y := by
  unfold innerParity
  congr 1
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hi : i < k
  · simp [hi]
  · have hle : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    have htb : x.testBit i = false := testBit_false_of_lt_pow2 x i (Nat.lt_of_lt_of_le hx hle)
    simp [hi, htb]

theorem innerParity_low_high_zero (r x y : Nat) (hx : x < 2 ^ r) (hy : y % 2 ^ r = 0) :
    innerParity x y = false := by
  rw [← innerParity_mod_pow2 r x y hx, hy, innerParity_zero_right]

theorem boolSign_false : boolSign false = 1 := rfl
theorem boolSign_true : boolSign true = -1 := rfl

theorem boolSign_xor (a b : Bool) : boolSign (xor a b) = boolSign a * boolSign b := by
  cases a <;> cases b <;> rfl

theorem boolSign_not (b : Bool) : boolSign (!b) = -(boolSign b) := by
  cases b <;> rfl

theorem boolSign_sq (b : Bool) : boolSign b * boolSign b = 1 := by
  cases b <;> rfl

theorem sumRange_congr (n : Nat) (f g : Nat → Int) (h : ∀ i < n, f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp only [sumRange, ih]; omega

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp only [sumRange, ih]; omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp only [sumRange, ih, Int.mul_add]

theorem sumRange_mul_right (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => f i * c) = sumRange n f * c := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp only [sumRange, ih, Int.add_mul]

theorem sumRange_zero (n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumRange, ih]

theorem sumRange_const (n : Nat) (c : Int) : sumRange n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih, Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]

theorem sumRange_two_mul (n : Nat) (f : Nat → Int) :
    sumRange (2 * n) f = sumRange n (fun i => f (2 * i)) + sumRange n (fun i => f (2 * i + 1)) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    have h : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h]
    simp only [sumRange]
    rw [ih]
    omega

theorem sumRange_append (a b : Nat) (f : Nat → Int) :
    sumRange (a + b) f = sumRange a f + sumRange b (fun i => f (a + i)) := by
  induction b with
  | zero => simp [sumRange]
  | succ b ih =>
    rw [← Nat.add_assoc]
    simp only [sumRange, ih]
    omega

theorem sumRange_mul (m n : Nat) (f : Nat → Int) :
    sumRange (m * n) f = sumRange n (fun y => sumRange m (fun x => f (x + m * y))) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [Nat.mul_succ, sumRange_append, ih]
    simp only [sumRange]
    congr 1
    apply sumRange_congr
    intro x _
    congr 1; omega

theorem sumRange_swap (m n : Nat) (f : Nat → Nat → Int) :
    sumRange m (fun x => sumRange n (fun y => f x y)) =
    sumRange n (fun y => sumRange m (fun x => f x y)) := by
  induction m with
  | zero => simp [sumRange, sumRange_zero]
  | succ m ih =>
    simp only [sumRange, ih, ← sumRange_add]

theorem sumRange_single (n a : Nat) (ha : a < n) (v : Int) :
    sumRange n (fun i => if i = a then v else 0) = v := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumRange]
    by_cases h : n = a
    · subst h
      have h0 : sumRange n (fun i => if i = n then v else 0) = 0 := by
        rw [sumRange_congr n _ (fun _ => 0) (fun i hi => by simp [Nat.ne_of_lt hi]), sumRange_zero]
      simp [h0]
    · have ha' : a < n := by omega
      simp [h, ih ha']

theorem walsh_congr (n : Nat) (f g : Nat → Int) (h : ∀ x < 2 ^ n, f x = g x) (w : Nat) :
    walsh n f w = walsh n g w := by
  induction n generalizing f g w with
  | zero => exact h 0 (by omega)
  | succ n ih =>
    simp only [walsh]
    rw [ih (fun x => f (2 * x)) (fun x => g (2 * x)) (fun x hx => h (2 * x) (by rw [Nat.pow_succ]; omega)) (w / 2)]
    rw [ih (fun x => f (2 * x + 1)) (fun x => g (2 * x + 1)) (fun x hx => h (2 * x + 1) (by rw [Nat.pow_succ]; omega)) (w / 2)]

theorem walsh_eq_sumRange (n : Nat) (f : Nat → Int) (w : Nat) :
    walsh n f w = sumRange (2 ^ n) (fun x => boolSign (innerParity x w) * f x) := by
  induction n generalizing f w with
  | zero =>
    simp [walsh, sumRange, innerParity_zero_left, boolSign]
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    rw [walsh, hp, sumRange_two_mul, ih, ih]
    congr 1
    · apply sumRange_congr; intro x _
      rw [innerParity_two_mul]
    · rw [← sumRange_mul_left]
      apply sumRange_congr; intro x _
      rw [innerParity_two_mul_add_one, boolSign_xor]
      have hs : boolSign (w % 2 == 1) = (if w % 2 == 0 then (1 : Int) else -1) := by
        rcases Nat.mod_two_eq_zero_or_one w with hw | hw <;> simp [hw, boolSign]
      rw [hs, Int.mul_assoc]

theorem walsh_add (n : Nat) (f g : Nat → Int) (w : Nat) :
    walsh n (fun x => f x + g x) w = walsh n f w + walsh n g w := by
  rw [walsh_eq_sumRange, walsh_eq_sumRange, walsh_eq_sumRange, ← sumRange_add]
  apply sumRange_congr; intro t _; rw [Int.mul_add]

theorem walsh_sub (n : Nat) (f g : Nat → Int) (w : Nat) :
    walsh n (fun x => f x - g x) w = walsh n f w - walsh n g w := by
  rw [walsh_eq_sumRange, walsh_eq_sumRange, walsh_eq_sumRange, ← sumRange_sub]
  apply sumRange_congr; intro t _; rw [Int.mul_sub]

theorem walsh_mul_left (n : Nat) (c : Int) (f : Nat → Int) (w : Nat) :
    walsh n (fun x => c * f x) w = c * walsh n f w := by
  rw [walsh_eq_sumRange, walsh_eq_sumRange, ← sumRange_mul_left]
  apply sumRange_congr; intro t _
  rw [← Int.mul_assoc, Int.mul_comm (boolSign _) c, Int.mul_assoc]

/-- Hadamard Involution Theorem: `W_n (W_n f) x = 2^n * f x` for all `x < 2^n`. -/
theorem walsh_walsh (n : Nat) (f : Nat → Int) (x : Nat) (hx : x < 2 ^ n) :
    walsh n (walsh n f) x = (2 ^ n : Int) * f x := by
  induction n generalizing f x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0
    simp [walsh]
  | succ n ih =>
    let f0 := fun t => f (2 * t)
    let f1 := fun t => f (2 * t + 1)
    have heven : ∀ w, walsh (n + 1) f (2 * w) = walsh n f0 w + walsh n f1 w := by
      intro w
      have hd : (2 * w) / 2 = w := by omega
      have hm : (2 * w) % 2 = 0 := by omega
      simp [walsh, f0, f1, hd, hm]
    have hodd : ∀ w, walsh (n + 1) f (2 * w + 1) = walsh n f0 w - walsh n f1 w := by
      intro w
      have hd : (2 * w + 1) / 2 = w := by omega
      have hm : (2 * w + 1) % 2 = 1 := by omega
      simp only [walsh, f0, f1, hd, hm, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
      omega
    conv => lhs; unfold walsh
    rw [walsh_congr n (fun w => walsh (n + 1) f (2 * w)) (fun w => walsh n f0 w + walsh n f1 w) (fun w _ => heven w)]
    rw [walsh_congr n (fun w => walsh (n + 1) f (2 * w + 1)) (fun w => walsh n f0 w - walsh n f1 w) (fun w _ => hodd w)]
    rw [walsh_add, walsh_sub]
    have hx' : x / 2 < 2 ^ n := by rw [Nat.pow_succ] at hx; omega
    rw [ih f0 (x / 2) hx', ih f1 (x / 2) hx']
    have hpow : (2 ^ (n + 1) : Int) = 2 * (2 ^ n : Int) := by
      rw [Int.pow_succ]; omega
    rw [hpow]
    rcases Nat.mod_two_eq_zero_or_one x with hxm | hxm
    · have hxeq : 2 * (x / 2) = x := by omega
      simp only [hxm, beq_self_eq_true, ↓reduceIte, Int.one_mul, f0, hxeq]
      rw [Int.mul_assoc]; omega
    · have hxeq : 2 * (x / 2) + 1 = x := by omega
      simp only [hxm, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, f1, hxeq]
      rw [Int.mul_assoc]; omega

private theorem xor_two_mul_even (x a : Nat) : (2 * x) ^^^ (2 * a) = 2 * (x ^^^ a) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j => rw [Nat.testBit_xor, testBit_two_mul_succ, testBit_two_mul_succ, testBit_two_mul_succ, Nat.testBit_xor]

private theorem xor_two_mul_add_one_even (x a : Nat) : (2 * x + 1) ^^^ (2 * a) = 2 * (x ^^^ a) + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_xor, testBit_two_mul_add_one_succ, testBit_two_mul_succ, testBit_two_mul_add_one_succ, Nat.testBit_xor]

private theorem xor_two_mul_odd (x a : Nat) : (2 * x) ^^^ (2 * a + 1) = 2 * (x ^^^ a) + 1 := by
  rw [Nat.xor_comm, xor_two_mul_add_one_even, Nat.xor_comm]

private theorem xor_two_mul_add_one_odd (x a : Nat) : (2 * x + 1) ^^^ (2 * a + 1) = 2 * (x ^^^ a) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_xor, testBit_two_mul_add_one_succ, testBit_two_mul_add_one_succ, testBit_two_mul_succ, Nat.testBit_xor]

/-- Exact Silicon Wiener-Khinchin Theorem: `W_n (xcorr n f g) w = W_n f w * W_n g w`. -/
theorem walsh_xcorr (n : Nat) (f g : Nat → Int) (w : Nat) :
    walsh n (xcorr n f g) w = walsh n f w * walsh n g w := by
  induction n generalizing f g w with
  | zero =>
    simp [walsh, xcorr, sumRange]
  | succ n ih =>
    let f0 := fun x => f (2 * x)
    let f1 := fun x => f (2 * x + 1)
    let g0 := fun x => g (2 * x)
    let g1 := fun x => g (2 * x + 1)
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    have heven : ∀ a, xcorr (n + 1) f g (2 * a) = xcorr n f0 g0 a + xcorr n f1 g1 a := by
      intro a
      unfold xcorr
      rw [hp, sumRange_two_mul]
      congr 1
      · apply sumRange_congr; intro x _; rw [xor_two_mul_even]
      · apply sumRange_congr; intro x _; rw [xor_two_mul_add_one_even]
    have hodd : ∀ a, xcorr (n + 1) f g (2 * a + 1) = xcorr n f0 g1 a + xcorr n f1 g0 a := by
      intro a
      unfold xcorr
      rw [hp, sumRange_two_mul]
      congr 1
      · apply sumRange_congr; intro x _; rw [xor_two_mul_odd]
      · apply sumRange_congr; intro x _; rw [xor_two_mul_add_one_odd]
    conv => lhs; unfold walsh
    rw [walsh_congr n (fun a => xcorr (n + 1) f g (2 * a)) (fun a => xcorr n f0 g0 a + xcorr n f1 g1 a) (fun a _ => heven a)]
    rw [walsh_congr n (fun a => xcorr (n + 1) f g (2 * a + 1)) (fun a => xcorr n f0 g1 a + xcorr n f1 g0 a) (fun a _ => hodd a)]
    rw [walsh_add, walsh_add, ih f0 g0, ih f1 g1, ih f0 g1, ih f1 g0]
    conv => rhs; unfold walsh
    rcases Nat.mod_two_eq_zero_or_one w with hwm | hwm
    · simp only [hwm, beq_self_eq_true, ↓reduceIte, Int.one_mul]
      have hring : ∀ A B C D : Int, A * C + B * D + (A * D + B * C) = (A + B) * (C + D) := by
        intro A B C D; rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
      exact hring _ _ _ _
    · simp only [hwm, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
      have hring : ∀ A B C D : Int, A * C + B * D + (-1) * (A * D + B * C) = (A + (-1) * B) * (C + (-1) * D) := by
        intro A B C D
        rw [Int.add_mul, Int.mul_add, Int.mul_add]
        simp only [Int.neg_mul, Int.mul_neg, Int.one_mul]
        rw [Int.mul_add, Int.mul_neg]
        omega
      exact hring _ _ _ _

private theorem int_two_pow_ne_zero (n : Nat) : ((2 : Int) ^ n) ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Int.pow_succ]
    intro h
    rcases Int.mul_eq_zero.mp h with h1 | h2
    · exact ih h1
    · omega

private theorem int_two_pow_double (k : Nat) : ((2 : Int) ^ (2 * k)) = ((2 : Int) ^ k) * ((2 : Int) ^ k) := by
  have h : 2 * k = k + k := by omega
  rw [h, Int.pow_add]

theorem IsBentWithDual.flatWalsh {k : Nat} {f d : Nat → Int} (h : IsBentWithDual k f d) :
    FlatWalsh k f := by
  intro w hw
  rw [h.2.2 w hw]
  rcases h.2.1 w hw with hd | hd
  · left; rw [hd, Int.mul_one]
  · right; rw [hd]; omega

/-- Dual Bentness & Involution Theorem: if `f` is bent with dual `d`, then `d` is bent with dual `f`. -/
theorem IsBentWithDual.dual_isBent {k : Nat} {f d : Nat → Int} (h : IsBentWithDual k f d) :
    IsBentWithDual k d f := by
  refine ⟨h.2.1, h.1, ?_⟩
  intro x hx
  have h1 := walsh_walsh (2 * k) f x hx
  have h2 : walsh (2 * k) (walsh (2 * k) f) x = walsh (2 * k) (fun w => (2 ^ k : Int) * d w) x :=
    walsh_congr (2 * k) _ _ (fun w hw => h.2.2 w hw) x
  rw [h2, walsh_mul_left, int_two_pow_double, Int.mul_assoc] at h1
  exact Int.eq_of_mul_eq_mul_left (int_two_pow_ne_zero k) h1

theorem walsh_const (n : Nat) (c : Int) (x : Nat) (hx : x < 2 ^ n) :
    walsh n (fun _ => c) x = if x = 0 then (2 ^ n : Int) * c else 0 := by
  have h := walsh_walsh n (fun t => if t = 0 then c else 0) x hx
  have h1 : ∀ w, walsh n (fun t => if t = 0 then c else 0) w = c := by
    intro w
    rw [walsh_eq_sumRange]
    have hcongr : sumRange (2 ^ n) (fun t => boolSign (innerParity t w) * (if t = 0 then c else 0)) =
                  sumRange (2 ^ n) (fun t => if t = 0 then c else 0) := by
      apply sumRange_congr; intro t _
      by_cases ht : t = 0
      · subst ht; simp [innerParity_zero_left, boolSign]
      · simp [ht]
    rw [hcongr, sumRange_single (2 ^ n) 0 (Nat.two_pow_pos n) c]
  rw [walsh_congr n _ (fun _ => c) (fun w _ => h1 w) x] at h
  rw [h]
  split <;> simp

/-- Universal Equivalence: Flat Walsh spectrum `±2^k` ↔ Vanishing Autocorrelation. -/
theorem flatWalsh_iff_vanishingAutocorr (k : Nat) (f : Nat → Int) :
    FlatWalsh k f ↔ VanishingAutocorr (2 * k) f := by
  constructor
  · intro hflat
    have hsq : ∀ w < 2 ^ (2 * k), walsh (2 * k) (xcorr (2 * k) f f) w = (2 ^ (2 * k) : Int) := by
      intro w hw
      rw [walsh_xcorr]
      rcases hflat w hw with hf | hf <;> rw [hf]
      · exact (int_two_pow_double k).symm
      · simp [Int.neg_mul, Int.mul_neg, Int.neg_neg, (int_two_pow_double k).symm]
    have hval : ∀ a < 2 ^ (2 * k), xcorr (2 * k) f f a = if a = 0 then (2 ^ (2 * k) : Int) else 0 := by
      intro a ha
      have h1 := walsh_walsh (2 * k) (xcorr (2 * k) f f) a ha
      rw [walsh_congr (2 * k) _ (fun _ => (2 ^ (2 * k) : Int)) hsq a] at h1
      rw [walsh_const (2 * k) (2 ^ (2 * k) : Int) a ha] at h1
      have hpos := int_two_pow_ne_zero (2 * k)
      by_cases ha0 : a = 0
      · simp only [ha0, ↓reduceIte] at h1 ⊢
        exact Int.eq_of_mul_eq_mul_left hpos h1.symm
      · simp only [ha0, ↓reduceIte] at h1 ⊢
        have : (2 ^ (2 * k) : Int) * xcorr (2 * k) f f a = (2 ^ (2 * k) : Int) * 0 := by simp [h1.symm]
        exact Int.eq_of_mul_eq_mul_left hpos this
    refine ⟨?_, ?_⟩
    · have := hval 0 (Nat.two_pow_pos (2 * k)); simpa using this
    · intro a ha0 ha
      have := hval a ha
      simp [Nat.ne_of_gt ha0] at this
      exact this
  · intro ⟨h0, hnz⟩ w hw
    have hw_xc : walsh (2 * k) (xcorr (2 * k) f f) w = (2 ^ (2 * k) : Int) := by
      rw [walsh_eq_sumRange]
      have hcongr : sumRange (2 ^ (2 * k)) (fun a => boolSign (innerParity a w) * xcorr (2 * k) f f a) =
                    sumRange (2 ^ (2 * k)) (fun a => if a = 0 then (2 ^ (2 * k) : Int) else 0) := by
        apply sumRange_congr; intro a ha
        by_cases ha0 : a = 0
        · subst ha0; simp [innerParity_zero_left, boolSign, h0]
        · simp [ha0, hnz a (Nat.pos_of_ne_zero ha0) ha]
      rw [hcongr, sumRange_single (2 ^ (2 * k)) 0 (Nat.two_pow_pos (2 * k)) (2 ^ (2 * k) : Int)]
    rw [walsh_xcorr, int_two_pow_double] at hw_xc
    have hdiff : (walsh (2 * k) f w - (2 ^ k : Int)) * (walsh (2 * k) f w + (2 ^ k : Int)) = 0 := by
      rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm (2 ^ k : Int) (walsh (2 * k) f w)]
      omega
    rcases Int.mul_eq_zero.mp hdiff with h1 | h2
    · left; omega
    · right; omega

theorem IsBentWithDual.vanishingAutocorr {k : Nat} {f d : Nat → Int} (h : IsBentWithDual k f d) :
    VanishingAutocorr (2 * k) f :=
  (flatWalsh_iff_vanishingAutocorr k f).mp h.flatWalsh

/-! ## Section 2: Causal Silicon T-Function Combinator Algebra & Constructive Hensel Inverter -/

/-- Two naturals agree mod `2^(k+1)` iff they agree mod `2^k` and agree at bit `k`. -/
theorem mod_two_pow_succ_eq_iff (a b k : Nat) :
    a % 2 ^ (k + 1) = b % 2 ^ (k + 1) ↔
    (a % 2 ^ k = b % 2 ^ k ∧ a.testBit k = b.testBit k) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 : a % 2 ^ (k + 1) % 2 ^ k = b % 2 ^ (k + 1) % 2 ^ k := by rw [h]
      have hdvd : 2 ^ k ∣ 2 ^ (k + 1) := ⟨2, by rw [Nat.pow_succ]⟩
      rwa [Nat.mod_mod_of_dvd a hdvd, Nat.mod_mod_of_dvd b hdvd] at h1
    · have ht := congrArg (fun n => n.testBit k) h
      simp only [Nat.testBit_mod_two_pow, Nat.lt_succ_self, decide_true, Bool.true_and] at ht
      exact ht
  · intro ⟨hmod, hbit⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases hi : i < k + 1
    · simp only [hi, decide_true, Bool.true_and]
      by_cases hik : i < k
      · have ht := congrArg (fun n => n.testBit i) hmod
        simpa [Nat.testBit_mod_two_pow, hik] using ht
      · have heq : i = k := by omega
        subst heq; exact hbit
    · simp [hi]

theorem mod_two_pow_eq_iff_testBit (a b k : Nat) :
    a % 2 ^ k = b % 2 ^ k ↔ ∀ i < k, a.testBit i = b.testBit i := by
  constructor
  · intro h i hi
    have ht := congrArg (fun n => n.testBit i) h
    simpa [Nat.testBit_mod_two_pow, hi] using ht
  · intro h
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases hi : i < k
    · simp [hi, h i hi]
    · simp [hi]

theorem testBit_add_two_pow_same (x k : Nat) (hx : x < 2 ^ k) :
    (x + 2 ^ k).testBit k = true := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hdiv : (x + 2 ^ k) / 2 ^ k = 1 := by
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    have : (x + 2 ^ k) = 2 ^ k * 1 + x := by omega
    rw [this, Nat.mul_add_div hp, Nat.div_eq_of_lt hx]
  rw [hdiv]; rfl

theorem testBit_add_two_pow_same_any (x k : Nat) :
    (x + 2 ^ k).testBit k = !(x.testBit k) := by
  rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdiv : (x + 2 ^ k) / 2 ^ k = x / 2 ^ k + 1 := Nat.add_div_right x hp
  rw [hdiv]
  have h1 : ∀ n : Nat, (1 &&& n != 0) = (n % 2 == 1) := by
    intro n
    rw [Nat.and_comm, Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
  rw [h1, h1]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h
  · have h' : (x / 2 ^ k + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (x / 2 ^ k + 1) % 2 = 0 := by omega
    simp [h, h']

theorem testBit_xor_two_pow_same (x k : Nat) :
    (x ^^^ 2 ^ k).testBit k = !(x.testBit k) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self]
  cases x.testBit k <;> rfl

/-- Reusable Causal Combinator Algebra: `+`, `*`, `^^^`, `&&&`, `|||`, `2 * ·`, composition. -/
theorem causal_id : Causal (fun x => x) := fun _ _ _ h => h

theorem causal_const (c : Nat) : Causal (fun _ => c) := fun _ _ _ _ => rfl

theorem causal_comp {f g : Nat → Nat} (hf : Causal f) (hg : Causal g) :
    Causal (fun x => f (g x)) :=
  fun k x y h => hf k (g x) (g y) (hg k x y h)

theorem causal_add {f g : Nat → Nat} (hf : Causal f) (hg : Causal g) :
    Causal (fun x => f x + g x) := by
  intro k x y h
  rw [Nat.add_mod, hf k x y h, hg k x y h, ← Nat.add_mod]

theorem causal_mul {f g : Nat → Nat} (hf : Causal f) (hg : Causal g) :
    Causal (fun x => f x * g x) := by
  intro k x y h
  rw [Nat.mul_mod, hf k x y h, hg k x y h, ← Nat.mul_mod]

theorem causal_xor {f g : Nat → Nat} (hf : Causal f) (hg : Causal g) :
    Causal (fun x => f x ^^^ g x) := by
  intro k x y h
  rw [mod_two_pow_eq_iff_testBit]
  intro i hi
  rw [Nat.testBit_xor, Nat.testBit_xor]
  rw [(mod_two_pow_eq_iff_testBit _ _ k).mp (hf k x y h) i hi]
  rw [(mod_two_pow_eq_iff_testBit _ _ k).mp (hg k x y h) i hi]

theorem causal_and {f g : Nat → Nat} (hf : Causal f) (hg : Causal g) :
    Causal (fun x => f x &&& g x) := by
  intro k x y h
  rw [mod_two_pow_eq_iff_testBit]
  intro i hi
  rw [Nat.testBit_and, Nat.testBit_and]
  rw [(mod_two_pow_eq_iff_testBit _ _ k).mp (hf k x y h) i hi]
  rw [(mod_two_pow_eq_iff_testBit _ _ k).mp (hg k x y h) i hi]

theorem causal_or {f g : Nat → Nat} (hf : Causal f) (hg : Causal g) :
    Causal (fun x => f x ||| g x) := by
  intro k x y h
  rw [mod_two_pow_eq_iff_testBit]
  intro i hi
  rw [Nat.testBit_or, Nat.testBit_or]
  rw [(mod_two_pow_eq_iff_testBit _ _ k).mp (hf k x y h) i hi]
  rw [(mod_two_pow_eq_iff_testBit _ _ k).mp (hg k x y h) i hi]

theorem causal_two_mul {f : Nat → Nat} (hf : Causal f) :
    Causal (fun x => 2 * f x) :=
  causal_mul (causal_const 2) hf

private theorem two_mul_causal_same_bit (φ : Nat → Nat) (hφ : Causal φ) (k x : Nat) :
    (2 * φ (x + 2 ^ k)).testBit k = (2 * φ x).testBit k := by
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [testBit_two_mul_succ, testBit_two_mul_succ]
    have hmod : (x + 2 ^ (j + 1)) % 2 ^ (j + 1) = x % 2 ^ (j + 1) := Nat.add_mod_right x _
    exact (mod_two_pow_eq_iff_testBit _ _ (j + 1)).mp (hφ (j + 1) _ _ hmod) j (by omega)

/-- Any causal `φ` yields a T-Bijection `y ↦ y ^^^ (2 * φ y)`. -/
theorem tBijection_xor_two_mul {φ : Nat → Nat} (hφ : Causal φ) :
    TBijection (fun y => y ^^^ (2 * φ y)) := by
  refine ⟨causal_xor causal_id (causal_two_mul hφ), ?_⟩
  intro k x hx
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_add_two_pow_same x k hx,
      testBit_false_of_lt_pow2 x k hx, two_mul_causal_same_bit φ hφ k x]
  cases (2 * φ x).testBit k <;> rfl

/-- Any causal `φ` yields a carried T-Bijection `y ↦ y + 2 * φ y`. -/
theorem tBijection_add_two_mul {φ : Nat → Nat} (hφ : Causal φ) :
    TBijection (fun y => y + 2 * φ y) := by
  refine ⟨causal_add causal_id (causal_two_mul hφ), ?_⟩
  intro k x _
  have hmod2 : (2 * φ (x + 2 ^ k)) % 2 ^ (k + 1) = (2 * φ x) % 2 ^ (k + 1) := by
    have hmod_in : (x + 2 ^ k) % 2 ^ k = x % 2 ^ k := Nat.add_mod_right x _
    have hφeq := hφ k (x + 2 ^ k) x hmod_in
    rw [mod_two_pow_eq_iff_testBit]
    intro i hi
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ j =>
      rw [testBit_two_mul_succ, testBit_two_mul_succ]
      exact (mod_two_pow_eq_iff_testBit _ _ k).mp hφeq j (by omega)
  have hsum : ((x + 2 ^ k) + 2 * φ (x + 2 ^ k)) % 2 ^ (k + 1) =
              ((x + 2 * φ x) + 2 ^ k) % 2 ^ (k + 1) := by
    rw [Nat.add_mod, hmod2, ← Nat.add_mod]
    congr 1; omega
  have ht := congrArg (fun n => n.testBit k) hsum
  simp only [Nat.testBit_mod_two_pow, Nat.lt_succ_self, decide_true, Bool.true_and] at ht
  rw [ht, testBit_add_two_pow_same_any]

/-- Any odd affine map `y ↦ (2 * m + 1) * y + c` is a T-Bijection. -/
theorem tBijection_odd_mul_add (m c : Nat) :
    TBijection (fun y => (2 * m + 1) * y + c) := by
  have heq : (fun y => (2 * m + 1) * y + c) = (fun y => ((y + 2 * (m * y)) + c)) := by
    funext y
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.add_comm (2 * (m * y)) y]
  rw [heq]
  refine ⟨causal_add (causal_add causal_id (causal_two_mul (causal_mul (causal_const m) causal_id))) (causal_const c), ?_⟩
  intro k x _
  dsimp only
  have hstep : (x + 2 ^ k) + 2 * (m * (x + 2 ^ k)) + c =
               ((x + 2 * (m * x) + c) + 2 ^ k) + 2 ^ (k + 1) * m := by
    rw [Nat.mul_add, Nat.mul_add, Nat.pow_succ]
    have hmul : 2 * (m * 2 ^ k) = 2 ^ k * 2 * m := by ac_rfl
    rw [hmul]; omega
  rw [hstep]
  have hmod : (((x + 2 * (m * x) + c) + 2 ^ k) + 2 ^ (k + 1) * m) % 2 ^ (k + 1) =
              ((x + 2 * (m * x) + c) + 2 ^ k) % 2 ^ (k + 1) := by
    rw [Nat.add_mul_mod_self_left]
  have ht := congrArg (fun n => n.testBit k) hmod
  simp only [Nat.testBit_mod_two_pow, Nat.lt_succ_self, decide_true, Bool.true_and] at ht
  rw [ht, testBit_add_two_pow_same_any]

theorem tInv_lt (π : Nat → Nat) (k y : Nat) : tInv π k y < 2 ^ k := by
  induction k with
  | zero => simp [tInv]
  | succ k ih =>
    simp only [tInv]
    rw [Nat.pow_succ]
    split <;> omega

theorem tInv_right_inv {π : Nat → Nat} (h : TBijection π) (k y : Nat) :
    π (tInv π k y) % 2 ^ k = y % 2 ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [mod_two_pow_succ_eq_iff]
    simp only [tInv]
    have hr : tInv π k y < 2 ^ k := tInv_lt π k y
    cases hb : xor (y.testBit k) ((π (tInv π k y)).testBit k)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      refine ⟨ih, ?_⟩
      cases hy : y.testBit k <;> cases hp : (π (tInv π k y)).testBit k <;> simp_all
    · simp only [↓reduceIte]
      refine ⟨?_, ?_⟩
      · have hmod_in : (tInv π k y + 2 ^ k) % 2 ^ k = (tInv π k y) % 2 ^ k := Nat.add_mod_right _ _
        rw [h.causal k (tInv π k y + 2 ^ k) (tInv π k y) hmod_in, ih]
      · rw [h.bitFlip k (tInv π k y) hr]
        cases hy : y.testBit k <;> cases hp : (π (tInv π k y)).testBit k <;> simp_all

theorem tInv_mod (π : Nat → Nat) (k y : Nat) : tInv π k (y % 2 ^ k) = tInv π k y := by
  have hgen : ∀ j ≤ k, tInv π j (y % 2 ^ k) = tInv π j y := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [tInv]
      rw [ih (by omega)]
      have htb : (y % 2 ^ k).testBit j = y.testBit j := by
        rw [Nat.testBit_mod_two_pow]
        have : j < k := by omega
        simp [this]
      rw [htb]
  exact hgen k (Nat.le_refl k)

theorem tInv_left_inv {π : Nat → Nat} (h : TBijection π) (k x : Nat) :
    tInv π k (π x) = x % 2 ^ k := by
  induction k with
  | zero => simp [tInv, Nat.mod_one]
  | succ k ih =>
    simp only [tInv, ih]
    have hlt : x % 2 ^ k < 2 ^ k := Nat.mod_lt x (Nat.two_pow_pos k)
    have hmod_x : x % 2 ^ (k + 1) = x % 2 ^ k + (if x.testBit k then 2 ^ k else 0) := by
      have hrhs_lt : x % 2 ^ k + (if x.testBit k then 2 ^ k else 0) < 2 ^ (k + 1) := by
        rw [Nat.pow_succ]; split <;> omega
      rw [← Nat.mod_eq_of_lt hrhs_lt, mod_two_pow_succ_eq_iff]
      cases hxk : x.testBit k
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        refine ⟨?_, ?_⟩
        · rw [Nat.mod_mod]
        · rw [testBit_false_of_lt_pow2 _ _ hlt]
      · simp only [↓reduceIte]
        refine ⟨?_, ?_⟩
        · rw [Nat.add_mod_right, Nat.mod_mod]
        · rw [testBit_add_two_pow_same _ _ hlt]
    have hpi_mod : π x % 2 ^ (k + 1) = π (x % 2 ^ (k + 1)) % 2 ^ (k + 1) :=
      h.causal (k + 1) x (x % 2 ^ (k + 1)) (Nat.mod_mod _ _).symm
    have hpi_bit : (π x).testBit k = (π (x % 2 ^ (k + 1))).testBit k := by
      have ht := congrArg (fun n => n.testBit k) hpi_mod
      simpa [Nat.testBit_mod_two_pow] using ht
    rw [hpi_bit, hmod_x]
    cases hxk : x.testBit k
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.xor_self]
    · simp only [↓reduceIte, h.bitFlip k (x % 2 ^ k) hlt]
      cases (π (x % 2 ^ k)).testBit k <;> simp

theorem tInv_left_inv_mod {π : Nat → Nat} (h : TBijection π) (k x : Nat) :
    tInv π k (π x % 2 ^ k) = x % 2 ^ k := by
  rw [tInv_mod, tInv_left_inv h]

theorem tInv_prefix (π : Nat → Nat) (k r y : Nat) (hr : r ≤ k) :
    tInv π k y % 2 ^ r = tInv π r y := by
  induction k with
  | zero =>
    have hr0 : r = 0 := by omega
    subst hr0; simp [tInv]
  | succ k ih =>
    by_cases heq : r = k + 1
    · subst heq; exact Nat.mod_eq_of_lt (tInv_lt π (k + 1) y)
    · have hrk : r ≤ k := by omega
      simp only [tInv]
      have hdvd : 2 ^ r ∣ 2 ^ k := Nat.pow_dvd_pow 2 hrk
      split
      · rcases hdvd with ⟨q, hq⟩
        rw [hq, Nat.add_mul_mod_self_left, ih hrk]
      · simp [ih hrk]

theorem tInv_causal (π : Nat → Nat) (k r a b : Nat) (hr : r ≤ k) (hab : a % 2 ^ r = b % 2 ^ r) :
    tInv π k a % 2 ^ r = tInv π k b % 2 ^ r := by
  rw [tInv_prefix π k r a hr, tInv_prefix π k r b hr, ← tInv_mod π r a, ← tInv_mod π r b, hab]

/-! ### Bit-Packing Helpers for `(x, y) ↔ x + 2^k * y` -/

theorem bitParity_add_pow2_mul (k u v : Nat) (hu : u < 2 ^ k) :
    bitParity (u + 2 ^ k * v) = xor (bitParity u) (bitParity v) := by
  induction k generalizing u with
  | zero =>
    have hu0 : u = 0 := by omega
    subst hu0; simp [bitParity_zero]
  | succ k ih =>
    have hlt : u / 2 < 2 ^ k := by rw [Nat.pow_succ] at hu; omega
    have hp : 2 ^ (k + 1) * v = 2 * (2 ^ k * v) := by rw [Nat.pow_succ]; ac_rfl
    rcases Nat.mod_two_eq_zero_or_one u with hm | hm
    · have hu_eq : u = 2 * (u / 2) := by omega
      have h1 : u + 2 ^ (k + 1) * v = 2 * (u / 2 + 2 ^ k * v) := by rw [hp, Nat.mul_add]; omega
      rw [h1, bitParity_two_mul, ih (u / 2) hlt]
      conv => rhs; rw [hu_eq, bitParity_two_mul]
    · have hu_eq : u = 2 * (u / 2) + 1 := by omega
      have h1 : u + 2 ^ (k + 1) * v = 2 * (u / 2 + 2 ^ k * v) + 1 := by rw [hp, Nat.mul_add]; omega
      rw [h1, bitParity_two_mul_add_one, ih (u / 2) hlt]
      conv => rhs; rw [hu_eq, bitParity_two_mul_add_one]
      cases bitParity (u / 2) <;> cases bitParity v <;> rfl

theorem and_add_pow2_mul (k x y a b : Nat) (hx : x < 2 ^ k) (ha : a < 2 ^ k) :
    (x + 2 ^ k * y) &&& (a + 2 ^ k * b) = (x &&& a) + 2 ^ k * (y &&& b) := by
  apply Nat.eq_of_testBit_eq; intro i
  have hsplit : ∀ u v : Nat, u < 2 ^ k → (u + 2 ^ k * v).testBit i =
      if i < k then u.testBit i else v.testBit (i - k) := by
    intro u v hu
    by_cases hi : i < k
    · simp only [hi, ↓reduceIte]
      have hdvd : 2 ^ (i + 1) ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      rcases hdvd with ⟨q, hq⟩
      have hmod : (u + 2 ^ k * v) % 2 ^ (i + 1) = u % 2 ^ (i + 1) := by
        rw [hq, Nat.mul_assoc, Nat.add_mul_mod_self_left]
      have ht := congrArg (fun n => n.testBit i) hmod
      simpa [Nat.testBit_mod_two_pow] using ht
    · simp only [hi, ↓reduceIte]
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have hk : i = k + (i - k) := by omega
      have hp : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by conv => lhs; rw [hk, Nat.pow_add]
      rw [hp, ← Nat.div_div_eq_div_mul]
      have hdiv : (u + 2 ^ k * v) / 2 ^ k = v := by
        rw [Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt hu, Nat.add_zero]
      rw [hdiv]
  have hxa_lt : (x &&& a) < 2 ^ k := Nat.and_lt_two_pow x ha
  rw [Nat.testBit_and, hsplit x y hx, hsplit a b ha, hsplit (x &&& a) (y &&& b) hxa_lt]
  by_cases hi : i < k
  · simp [hi, Nat.testBit_and]
  · simp [hi, Nat.testBit_and]

theorem xor_add_pow2_mul (k x y a b : Nat) (hx : x < 2 ^ k) (ha : a < 2 ^ k) :
    (x + 2 ^ k * y) ^^^ (a + 2 ^ k * b) = (x ^^^ a) + 2 ^ k * (y ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  have hsplit : ∀ u v : Nat, u < 2 ^ k → (u + 2 ^ k * v).testBit i =
      if i < k then u.testBit i else v.testBit (i - k) := by
    intro u v hu
    by_cases hi : i < k
    · simp only [hi, ↓reduceIte]
      have hdvd : 2 ^ (i + 1) ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      rcases hdvd with ⟨q, hq⟩
      have hmod : (u + 2 ^ k * v) % 2 ^ (i + 1) = u % 2 ^ (i + 1) := by
        rw [hq, Nat.mul_assoc, Nat.add_mul_mod_self_left]
      have ht := congrArg (fun n => n.testBit i) hmod
      simpa [Nat.testBit_mod_two_pow] using ht
    · simp only [hi, ↓reduceIte]
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have hk : i = k + (i - k) := by omega
      have hp : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by conv => lhs; rw [hk, Nat.pow_add]
      rw [hp, ← Nat.div_div_eq_div_mul]
      have hdiv : (u + 2 ^ k * v) / 2 ^ k = v := by
        rw [Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt hu, Nat.add_zero]
      rw [hdiv]
  have hxa_lt : (x ^^^ a) < 2 ^ k := Nat.xor_lt_two_pow hx ha
  rw [Nat.testBit_xor, hsplit x y hx, hsplit a b ha, hsplit (x ^^^ a) (y ^^^ b) hxa_lt]
  by_cases hi : i < k
  · simp [hi, Nat.testBit_xor]
  · simp [hi, Nat.testBit_xor]

theorem innerParity_add_pow2_mul (k x y a b : Nat) (hx : x < 2 ^ k) (ha : a < 2 ^ k) :
    innerParity (x + 2 ^ k * y) (a + 2 ^ k * b) = xor (innerParity x a) (innerParity y b) := by
  unfold innerParity
  rw [and_add_pow2_mul k x y a b hx ha]
  exact bitParity_add_pow2_mul k (x &&& a) (y &&& b) (Nat.and_lt_two_pow x ha)

theorem sumRange_innerParity (k w : Nat) (hw : w < 2 ^ k) :
    sumRange (2 ^ k) (fun x => boolSign (innerParity x w)) = if w = 0 then (2 ^ k : Int) else 0 := by
  have h := walsh_const k 1 w hw
  rw [walsh_eq_sumRange] at h
  have hcongr : sumRange (2 ^ k) (fun x => boolSign (innerParity x w) * 1) =
                sumRange (2 ^ k) (fun x => boolSign (innerParity x w)) := by
    apply sumRange_congr; intro x _; exact Int.mul_one _
  rw [hcongr, Int.mul_one] at h
  exact h

/-- Parametric Maiorana-McFarland Bent Engine: ANY `TBijection π` and ANY `g` yields an exact
    bent function on `2*k` bits with flat Walsh spectrum `±2^k`, exact dual via `tInv π k`,
    and vanishing autocorrelation for all `k ≥ 0`. -/
theorem mm_isBent {π : Nat → Nat} (hπ : TBijection π) (g : Nat → Bool) (k : Nat) :
    IsBentWithDual k (mmSign k π g) (mmDualSign k π g) := by
  refine ⟨fun _ _ => by unfold mmSign boolSign; split <;> simp,
          fun _ _ => by unfold mmDualSign boolSign; split <;> simp, ?_⟩
  intro w _
  have h2k : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  rw [walsh_eq_sumRange, h2k, sumRange_mul]
  let a := w % 2 ^ k
  let b := w / 2 ^ k
  have ha : a < 2 ^ k := Nat.mod_lt w (Nat.two_pow_pos k)
  have hw_eq : w = a + 2 ^ k * b := by
    have := Nat.div_add_mod w (2 ^ k)
    change w = w % 2 ^ k + 2 ^ k * (w / 2 ^ k)
    omega
  have hinner : ∀ y < 2 ^ k,
      sumRange (2 ^ k) (fun x => boolSign (innerParity (x + 2 ^ k * y) w) * mmSign k π g (x + 2 ^ k * y)) =
      if y = tInv π k a then (2 ^ k : Int) * boolSign (xor (innerParity b (tInv π k a)) (g (tInv π k a))) else 0 := by
    intro y hy
    have hterm : ∀ x < 2 ^ k,
        boolSign (innerParity (x + 2 ^ k * y) w) * mmSign k π g (x + 2 ^ k * y) =
        boolSign (xor (innerParity b y) (g y)) * boolSign (innerParity x (a ^^^ (π y % 2 ^ k))) := by
      intro x hx
      have hdiv : (x + 2 ^ k * y) / 2 ^ k = y := by
        rw [Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt hx, Nat.add_zero]
      have hmod : (x + 2 ^ k * y) % 2 ^ k = x := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
      unfold mmSign mmBool
      rw [hdiv, hmod, hw_eq, innerParity_add_pow2_mul k x y a b hx ha,
          innerParity_xor_right, boolSign_xor, boolSign_xor, boolSign_xor, boolSign_xor,
          innerParity_comm y b]
      ac_rfl
    rw [sumRange_congr (2 ^ k) _ _ hterm, sumRange_mul_left]
    have hxor_lt : a ^^^ (π y % 2 ^ k) < 2 ^ k :=
      Nat.xor_lt_two_pow ha (Nat.mod_lt _ (Nat.two_pow_pos k))
    rw [sumRange_innerParity k _ hxor_lt]
    have hiff : (a ^^^ (π y % 2 ^ k) = 0) ↔ (y = tInv π k a) := by
      constructor
      · intro h0
        have heq : a = π y % 2 ^ k := by
          have := congrArg (fun t => t ^^^ (π y % 2 ^ k)) h0
          simpa [Nat.xor_assoc, Nat.xor_self] using this
        rw [heq, tInv_left_inv_mod hπ k y, Nat.mod_eq_of_lt hy]
      · intro hy_eq
        subst hy_eq
        rw [tInv_right_inv hπ k a, Nat.mod_eq_of_lt ha, Nat.xor_self]
    by_cases hcond : y = tInv π k a
    · have h0 : a ^^^ (π y % 2 ^ k) = 0 := hiff.mpr hcond
      rw [h0]
      simp only [hcond, ↓reduceIte, Int.mul_comm]
    · have h0 : a ^^^ (π y % 2 ^ k) ≠ 0 := fun hc => hcond (hiff.mp hc)
      simp only [h0, hcond, ↓reduceIte, Int.mul_zero]
  rw [sumRange_congr (2 ^ k) _ _ hinner]
  rw [sumRange_single (2 ^ k) (tInv π k a) (tInv_lt π k a) _]
  rfl

/-! ## Section 3: Recursive 4-Subblock Kronecker-Dual Bent Lifting Engine -/

theorem walsh_quadCombine (m : Nat) (f0 f1 f2 f3 : Nat → Int) (w : Nat) :
    walsh (m + 2) (quadCombine f0 f1 f2 f3) w =
    let s0 : Int := if w % 2 == 0 then 1 else -1
    let s1 : Int := if (w / 2) % 2 == 0 then 1 else -1
    walsh m f0 (w / 4) + s0 * walsh m f1 (w / 4) +
    s1 * walsh m f2 (w / 4) + s0 * s1 * walsh m f3 (w / 4) := by
  have hstep : walsh (m + 2) (quadCombine f0 f1 f2 f3) w =
      walsh (m + 1) (fun x => quadCombine f0 f1 f2 f3 (2 * x)) (w / 2) +
      (if w % 2 == 0 then (1 : Int) else -1) *
      walsh (m + 1) (fun x => quadCombine f0 f1 f2 f3 (2 * x + 1)) (w / 2) := rfl
  rw [hstep]
  conv => lhs; arg 1; unfold walsh
  conv => lhs; arg 2; arg 2; unfold walsh
  have hc0 : ∀ x, quadCombine f0 f1 f2 f3 (2 * (2 * x)) = f0 x := by
    intro x; unfold quadCombine
    have h1 : 2 * (2 * x) % 4 = 0 := by omega
    have h2 : 2 * (2 * x) / 4 = x := by omega
    simp [h1, h2]
  have hc2 : ∀ x, quadCombine f0 f1 f2 f3 (2 * (2 * x + 1)) = f2 x := by
    intro x; unfold quadCombine
    have h1 : 2 * (2 * x + 1) % 4 = 2 := by omega
    have h2 : 2 * (2 * x + 1) / 4 = x := by omega
    simp [h1, h2]
  have hc1 : ∀ x, quadCombine f0 f1 f2 f3 (2 * (2 * x) + 1) = f1 x := by
    intro x; unfold quadCombine
    have h1 : (2 * (2 * x) + 1) % 4 = 1 := by omega
    have h2 : (2 * (2 * x) + 1) / 4 = x := by omega
    simp [h1, h2]
  have hc3 : ∀ x, quadCombine f0 f1 f2 f3 (2 * (2 * x + 1) + 1) = f3 x := by
    intro x; unfold quadCombine
    have h1 : (2 * (2 * x + 1) + 1) % 4 = 3 := by omega
    have h2 : (2 * (2 * x + 1) + 1) / 4 = x := by omega
    simp [h1, h2]
  rw [walsh_congr m _ f0 (fun x _ => hc0 x)]
  rw [walsh_congr m _ f2 (fun x _ => hc2 x)]
  rw [walsh_congr m _ f1 (fun x _ => hc1 x)]
  rw [walsh_congr m _ f3 (fun x _ => hc3 x)]
  have hdiv : w / 2 / 2 = w / 4 := by omega
  rw [hdiv]
  dsimp only
  rw [Int.mul_add, ← Int.mul_assoc]
  omega

private theorem sign4_bent_iff (a b c d : Int)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1) :
    ((a + b + c + d = 2 ∨ a + b + c + d = -2) ∧
     (a - b + c - d = 2 ∨ a - b + c - d = -2) ∧
     (a + b - c - d = 2 ∨ a + b - c - d = -2) ∧
     (a - b - c + d = 2 ∨ a - b - c + d = -2)) ↔
    a * b * c * d = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> decide

/-- Forward 4-Quad Kronecker-Dual Lifting Theorem:
    if `f0, f1, f2, f3` are bent on `2*k` bits with dual product `-1`, then `quadCombine f0 f1 f2 f3`
    is bent on `2*(k+1)` bits with exact closed-form dual `quadDual d0 d1 d2 d3`. -/
theorem quadCombine_isBent {k : Nat} {f0 f1 f2 f3 d0 d1 d2 d3 : Nat → Int}
    (h0 : IsBentWithDual k f0 d0) (h1 : IsBentWithDual k f1 d1)
    (h2 : IsBentWithDual k f2 d2) (h3 : IsBentWithDual k f3 d3)
    (hprod : ∀ w < 2 ^ (2 * k), d0 w * d1 w * d2 w * d3 w = -1) :
    IsBentWithDual (k + 1) (quadCombine f0 f1 f2 f3) (quadDual d0 d1 d2 d3) := by
  have h2k : 2 * (k + 1) = 2 * k + 2 := by omega
  have hpow4 : 2 ^ (2 * (k + 1)) = 4 * 2 ^ (2 * k) := by
    rw [h2k, Nat.pow_add]; omega
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hz4 : z / 4 < 2 ^ (2 * k) := by omega
    unfold quadCombine
    split
    · exact h0.1 (z / 4) hz4
    · exact h1.1 (z / 4) hz4
    · exact h2.1 (z / 4) hz4
    · exact h3.1 (z / 4) hz4
  · intro w hw
    have hw4 : w / 4 < 2 ^ (2 * k) := by omega
    have hp := hprod (w / 4) hw4
    unfold quadDual
    rcases h0.2.1 (w / 4) hw4 with h0' | h0' <;>
    rcases h1.2.1 (w / 4) hw4 with h1' | h1' <;>
    rcases h2.2.1 (w / 4) hw4 with h2' | h2' <;>
    rcases h3.2.1 (w / 4) hw4 with h3' | h3' <;>
    simp only [h0', h1', h2', h3'] at hp ⊢ <;>
    (try exact absurd hp (by decide)) <;>
    (rcases Nat.mod_two_eq_zero_or_one w with hwm | hwm <;>
     rcases Nat.mod_two_eq_zero_or_one (w / 2) with hwm2 | hwm2 <;>
     simp [hwm, hwm2])
  · intro w hw
    have hw4 : w / 4 < 2 ^ (2 * k) := by omega
    rw [h2k, walsh_quadCombine (2 * k) f0 f1 f2 f3 w]
    rw [h0.2.2 (w / 4) hw4, h1.2.2 (w / 4) hw4, h2.2.2 (w / 4) hw4, h3.2.2 (w / 4) hw4]
    have hp := hprod (w / 4) hw4
    unfold quadDual
    have hpow : ((2 : Int) ^ (k + 1)) = ((2 : Int) ^ k) * 2 := by rw [Int.pow_succ]
    rw [hpow]
    dsimp only
    have hcomb : ∀ P A B C D s0 s1 : Int,
        P * A + s0 * (P * B) + s1 * (P * C) + s0 * s1 * (P * D) =
        P * (A + s0 * B + s1 * C + s0 * s1 * D) := by
      intro P A B C D s0 s1
      rw [Int.mul_add, Int.mul_add, Int.mul_add]
      have h1' : s0 * (P * B) = P * (s0 * B) := by ac_rfl
      have h2' : s1 * (P * C) = P * (s1 * C) := by ac_rfl
      have h3' : s0 * s1 * (P * D) = P * (s0 * s1 * D) := by ac_rfl
      rw [h1', h2', h3']
    rw [hcomb, Int.mul_assoc ((2 : Int) ^ k) 2]
    congr 1
    have hmul2 : ∀ a b c d s0 s1 : Int,
        (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → (c = 1 ∨ c = -1) → (d = 1 ∨ d = -1) →
        (s0 = 1 ∨ s0 = -1) → (s1 = 1 ∨ s1 = -1) → a * b * c * d = -1 →
        a + s0 * b + s1 * c + s0 * s1 * d = 2 * ((a + s0 * b + s1 * c + s0 * s1 * d) / 2) := by
      intro a b c d s0 s1 ha hb hc hd hs0 hs1 hp'
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
      (try exact absurd hp' (by decide)) <;>
      rcases hs0 with rfl | rfl <;> rcases hs1 with rfl | rfl <;> decide
    have hs0 : (if (w % 2 == 0) = true then (1 : Int) else -1) = 1 ∨
               (if (w % 2 == 0) = true then (1 : Int) else -1) = -1 := by split <;> simp
    have hs1 : (if (w / 2 % 2 == 0) = true then (1 : Int) else -1) = 1 ∨
               (if (w / 2 % 2 == 0) = true then (1 : Int) else -1) = -1 := by split <;> simp
    exact hmul2 _ _ _ _ _ _ (h0.2.1 (w / 4) hw4) (h1.2.1 (w / 4) hw4)
      (h2.2.1 (w / 4) hw4) (h3.2.1 (w / 4) hw4) hs0 hs1 hp

/-- Necessary & Sufficient Butterfly Dual-Product Law for 4-Quad Bent Lifting. -/
theorem quadCombine_flatWalsh_iff {k : Nat} {f0 f1 f2 f3 d0 d1 d2 d3 : Nat → Int}
    (h0 : IsBentWithDual k f0 d0) (h1 : IsBentWithDual k f1 d1)
    (h2 : IsBentWithDual k f2 d2) (h3 : IsBentWithDual k f3 d3) :
    FlatWalsh (k + 1) (quadCombine f0 f1 f2 f3) ↔
    ∀ w < 2 ^ (2 * k), d0 w * d1 w * d2 w * d3 w = -1 := by
  constructor
  · intro hflat w hw
    have h2k : 2 * (k + 1) = 2 * k + 2 := by omega
    have hpow4 : 2 ^ (2 * (k + 1)) = 4 * 2 ^ (2 * k) := by rw [h2k, Nat.pow_add]; omega
    have hpow : ((2 : Int) ^ (k + 1)) = ((2 : Int) ^ k) * 2 := by rw [Int.pow_succ]
    have hpos := int_two_pow_ne_zero k
    have heval : ∀ r < 4,
        let s0 : Int := if r % 2 == 0 then 1 else -1
        let s1 : Int := if (r / 2) % 2 == 0 then 1 else -1
        d0 w + s0 * d1 w + s1 * d2 w + s0 * s1 * d3 w = 2 ∨
        d0 w + s0 * d1 w + s1 * d2 w + s0 * s1 * d3 w = -2 := by
      intro r hr
      have hlt : 4 * w + r < 2 ^ (2 * (k + 1)) := by omega
      have hf := hflat (4 * w + r) hlt
      rw [h2k, walsh_quadCombine (2 * k) f0 f1 f2 f3 (4 * w + r)] at hf
      have hdiv4 : (4 * w + r) / 4 = w := by omega
      have hmod2 : (4 * w + r) % 2 = r % 2 := by omega
      have hdiv2mod2 : (4 * w + r) / 2 % 2 = r / 2 % 2 := by omega
      rw [hdiv4, hmod2, hdiv2mod2,
          h0.2.2 w hw, h1.2.2 w hw, h2.2.2 w hw, h3.2.2 w hw, hpow] at hf
      dsimp only at hf ⊢
      have hfact : ∀ P s0 s1 : Int,
          P * d0 w + s0 * (P * d1 w) + s1 * (P * d2 w) + s0 * s1 * (P * d3 w) =
          P * (d0 w + s0 * d1 w + s1 * d2 w + s0 * s1 * d3 w) := by
        intro P s0 s1
        rw [Int.mul_add, Int.mul_add, Int.mul_add]
        have h1' : s0 * (P * d1 w) = P * (s0 * d1 w) := by ac_rfl
        have h2' : s1 * (P * d2 w) = P * (s1 * d2 w) := by ac_rfl
        have h3' : s0 * s1 * (P * d3 w) = P * (s0 * s1 * d3 w) := by ac_rfl
        rw [h1', h2', h3']
      rw [hfact] at hf
      rcases hf with hf1 | hf2
      · left; exact Int.eq_of_mul_eq_mul_left hpos hf1
      · right
        have hf2' : ((2 : Int) ^ k) * (d0 w + (if (r % 2 == 0) = true then 1 else -1) * d1 w +
            (if (r / 2 % 2 == 0) = true then 1 else -1) * d2 w +
            (if (r % 2 == 0) = true then 1 else -1) * (if (r / 2 % 2 == 0) = true then 1 else -1) * d3 w) =
            ((2 : Int) ^ k) * (-2) := by
          rw [Int.mul_neg]; exact hf2
        exact Int.eq_of_mul_eq_mul_left hpos hf2'
    have h00 := heval 0 (by omega)
    have h01 := heval 1 (by omega)
    have h02 := heval 2 (by omega)
    have h03 := heval 3 (by omega)
    simp only [Nat.zero_mod, beq_self_eq_true, ↓reduceIte, Nat.zero_div, Int.one_mul,
               Nat.one_mod, Nat.reduceBEq, Bool.false_eq_true, Nat.reduceDiv,
               Nat.reduceMod, Int.neg_mul, Int.neg_neg] at h00 h01 h02 h03
    have hcond : (d0 w + d1 w + d2 w + d3 w = 2 ∨ d0 w + d1 w + d2 w + d3 w = -2) ∧
                 (d0 w - d1 w + d2 w - d3 w = 2 ∨ d0 w - d1 w + d2 w - d3 w = -2) ∧
                 (d0 w + d1 w - d2 w - d3 w = 2 ∨ d0 w + d1 w - d2 w - d3 w = -2) ∧
                 (d0 w - d1 w - d2 w + d3 w = 2 ∨ d0 w - d1 w - d2 w + d3 w = -2) := by
      refine ⟨h00, ?_, ?_, ?_⟩
      · rcases h01 with h | h
        · left; omega
        · right; omega
      · rcases h02 with h | h
        · left; omega
        · right; omega
      · rcases h03 with h | h
        · left; omega
        · right; omega
    exact (sign4_bent_iff (d0 w) (d1 w) (d2 w) (d3 w)
      (h0.2.1 w hw) (h1.2.1 w hw) (h2.2.1 w hw) (h3.2.1 w hw)).mp hcond
  · intro hprod
    exact (quadCombine_isBent h0 h1 h2 h3 hprod).flatWalsh

/-- Zero-Sum T-Function Quad Compiler:
    Given ANY two causal maps `φ1, φ2`, the 4 causal T-functions
    `ψ0(a)=a`, `ψ1(a)=a ^^^ 2φ1(a)`, `ψ2(a)=a ^^^ 2φ2(a)`, `ψ3(a)=a ^^^ 2(φ1(a) ^^^ φ2(a))`
    satisfy `ψ0 ^^^ ψ1 ^^^ ψ2 ^^^ ψ3 = 0`, so their dual-inverted MM functions lift via
    `quadCombine` to an infinite bent family on `2*(k+1)` bits with exact flat Walsh spectrum
    and vanishing autocorrelation for ALL `k ≥ 1`. -/
theorem zeroSum_tQuad_isBent {φ1 φ2 : Nat → Nat} (hφ1 : Causal φ1) (hφ2 : Causal φ2) (k : Nat) :
    let ψ0 := fun a => a
    let ψ1 := fun a => a ^^^ (2 * φ1 a)
    let ψ2 := fun a => a ^^^ (2 * φ2 a)
    let ψ3 := fun a => a ^^^ (2 * (φ1 a ^^^ φ2 a))
    let f0 := mmDualSign k ψ0 (fun _ => false)
    let f1 := mmDualSign k ψ1 (fun _ => false)
    let f2 := mmDualSign k ψ2 (fun _ => false)
    let f3 := mmDualSign k ψ3 (fun _ => true)
    let d0 := mmSign k ψ0 (fun _ => false)
    let d1 := mmSign k ψ1 (fun _ => false)
    let d2 := mmSign k ψ2 (fun _ => false)
    let d3 := mmSign k ψ3 (fun _ => true)
    IsBentWithDual (k + 1) (quadCombine f0 f1 f2 f3) (quadDual d0 d1 d2 d3) := by
  intro ψ0 ψ1 ψ2 ψ3 f0 f1 f2 f3 d0 d1 d2 d3
  have hψ0 : TBijection ψ0 := by
    have : ψ0 = fun y => (2 * 0 + 1) * y + 0 := by funext y; simp [ψ0]
    rw [this]; exact tBijection_odd_mul_add 0 0
  have hψ1 : TBijection ψ1 := tBijection_xor_two_mul hφ1
  have hψ2 : TBijection ψ2 := tBijection_xor_two_mul hφ2
  have hψ3 : TBijection ψ3 := tBijection_xor_two_mul (causal_xor hφ1 hφ2)
  have hb0 : IsBentWithDual k f0 d0 := (mm_isBent hψ0 (fun _ => false) k).dual_isBent
  have hb1 : IsBentWithDual k f1 d1 := (mm_isBent hψ1 (fun _ => false) k).dual_isBent
  have hb2 : IsBentWithDual k f2 d2 := (mm_isBent hψ2 (fun _ => false) k).dual_isBent
  have hb3 : IsBentWithDual k f3 d3 := (mm_isBent hψ3 (fun _ => true) k).dual_isBent
  apply quadCombine_isBent hb0 hb1 hb2 hb3
  intro w _
  unfold d0 d1 d2 d3 mmSign mmBool
  have hx : w % 2 ^ k < 2 ^ k := Nat.mod_lt w (Nat.two_pow_pos k)
  rw [innerParity_mod_pow2 k (w % 2 ^ k) (ψ0 (w / 2 ^ k)) hx,
      innerParity_mod_pow2 k (w % 2 ^ k) (ψ1 (w / 2 ^ k)) hx,
      innerParity_mod_pow2 k (w % 2 ^ k) (ψ2 (w / 2 ^ k)) hx,
      innerParity_mod_pow2 k (w % 2 ^ k) (ψ3 (w / 2 ^ k)) hx]
  have hzero : ψ0 (w / 2 ^ k) ^^^ ψ1 (w / 2 ^ k) ^^^ ψ2 (w / 2 ^ k) ^^^ ψ3 (w / 2 ^ k) = 0 := by
    simp only [ψ0, ψ1, ψ2, ψ3]
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ j =>
      simp only [Nat.testBit_xor, testBit_two_mul_succ, Nat.zero_testBit]
      cases (w / 2 ^ k).testBit (j + 1) <;> cases (φ1 (w / 2 ^ k)).testBit j <;>
      cases (φ2 (w / 2 ^ k)).testBit j <;> rfl
  have hpar : xor (xor (innerParity (w % 2 ^ k) (ψ0 (w / 2 ^ k))) (innerParity (w % 2 ^ k) (ψ1 (w / 2 ^ k))))
                  (xor (innerParity (w % 2 ^ k) (ψ2 (w / 2 ^ k))) (innerParity (w % 2 ^ k) (ψ3 (w / 2 ^ k)))) = false := by
    rw [← innerParity_xor_right, ← innerParity_xor_right, ← innerParity_xor_right,
        ← Nat.xor_assoc, hzero, innerParity_zero_right]
  simp only [Bool.xor_false, Bool.xor_true, boolSign_not]
  rw [← boolSign_xor, Int.mul_assoc, Int.mul_neg, ← boolSign_xor, Int.mul_neg, ← boolSign_xor]
  rw [hpar]
  rfl

/-! ## Section 4A: Silicon Causal-Mask Carlet-T Bent Engine (∀ k ≥ 1, ∀ 0 ≤ r ≤ k) -/

theorem sumRange_filter_lt (m n : Nat) (hmn : m ≤ n) (f : Nat → Int) :
    sumRange n (fun x => if x < m then f x else 0) = sumRange m f := by
  have hsplit : n = m + (n - m) := by omega
  rw [hsplit, sumRange_append]
  have hleft : sumRange m (fun x => if x < m then f x else 0) = sumRange m f := by
    apply sumRange_congr; intro x hx; simp [hx]
  have hright : sumRange (n - m) (fun i => if m + i < m then f (m + i) else 0) = 0 := by
    rw [sumRange_congr (n - m) _ (fun _ => 0) (fun i _ => by simp [show ¬(m + i < m) by omega]), sumRange_zero]
  rw [hleft, hright, Int.add_zero]

/-- Silicon Causal-Mask Carlet-T Bent Theorem:
    For EVERY `TBijection π`, EVERY `k`, and EVERY `r ≤ k`, `carletTSign k r π` is bent
    with exact flat Walsh spectrum `±2^k`, exact dual `carletTDualSign k r π`, and
    vanishing autocorrelation (unconditional on `π 0`). -/
theorem carletT_isBent {π : Nat → Nat} (hπ : TBijection π) (k r : Nat) (hr : r ≤ k) :
    IsBentWithDual k (carletTSign k r π) (carletTDualSign k r π) := by
  refine ⟨fun _ _ => by unfold carletTSign boolSign; split <;> simp,
          fun _ _ => by unfold carletTDualSign boolSign; dsimp only; split <;> simp, ?_⟩
  intro w hw
  let a := w % 2 ^ k
  let b := w / 2 ^ k
  have ha : a < 2 ^ k := Nat.mod_lt w (Nat.two_pow_pos k)
  have hb : b < 2 ^ k := by
    have h2k : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
    have hw' : w < 2 ^ k * 2 ^ k := h2k ▸ hw
    exact Nat.div_lt_of_lt_mul hw'
  have hw_eq : w = a + 2 ^ k * b := by
    have := Nat.div_add_mod w (2 ^ k)
    change w = w % 2 ^ k + 2 ^ k * (w / 2 ^ k)
    omega
  let δ : Nat → Int := fun z =>
    if z % 2 ^ k < 2 ^ r ∧ (z / 2 ^ k) % 2 ^ r = 0
    then boolSign (innerParity (z % 2 ^ k) (π 0 % 2 ^ r))
    else 0
  have hdecomp : ∀ z < 2 ^ (2 * k),
      carletTSign k r π z = mmSign k π (fun _ => false) z - 2 * δ z := by
    intro z _
    unfold carletTSign carletTBool mmSign mmBool
    dsimp only [δ]
    by_cases hc : z % 2 ^ k < 2 ^ r ∧ (z / 2 ^ k) % 2 ^ r = 0
    · have hpir : π (z / 2 ^ k) % 2 ^ r = π 0 % 2 ^ r := by
        apply hπ.causal r (z / 2 ^ k) 0
        simpa using hc.2
      have hxr : z % 2 ^ k < 2 ^ r := hc.1
      have hxk : z % 2 ^ k < 2 ^ k := Nat.mod_lt z (Nat.two_pow_pos k)
      have hip : innerParity (z % 2 ^ k) (π (z / 2 ^ k) % 2 ^ k) =
                 innerParity (z % 2 ^ k) (π 0 % 2 ^ r) := by
        rw [innerParity_mod_pow2 k _ _ hxk, ← innerParity_mod_pow2 r _ _ hxr, hpir]
      simp only [hc, and_self, decide_true, Bool.xor_true, Bool.xor_false, ↓reduceIte, boolSign_not, hip]
      omega
    · simp only [hc, decide_false, Bool.xor_false, ↓reduceIte]
      omega
  rw [walsh_congr (2 * k) (carletTSign k r π) (fun z => mmSign k π (fun _ => false) z - 2 * δ z) hdecomp w]
  rw [walsh_sub, walsh_mul_left]
  have hmm := (mm_isBent hπ (fun _ => false) k).2.2 w hw
  rw [hmm]
  have hwalsh_δ : walsh (2 * k) δ w =
      if a % 2 ^ r = π 0 % 2 ^ r ∧ b < 2 ^ r then (2 ^ k : Int) else 0 := by
    have h2k : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
    rw [walsh_eq_sumRange, h2k, sumRange_mul]
    have hsplit_inner : ∀ y < 2 ^ k,
        sumRange (2 ^ k) (fun x => boolSign (innerParity (x + 2 ^ k * y) w) * δ (x + 2 ^ k * y)) =
        (if y % 2 ^ r = 0 then boolSign (innerParity y b) else 0) *
        (if a % 2 ^ r = π 0 % 2 ^ r then (2 ^ r : Int) else 0) := by
      intro y _
      have hterm : ∀ x < 2 ^ k,
          boolSign (innerParity (x + 2 ^ k * y) w) * δ (x + 2 ^ k * y) =
          (if y % 2 ^ r = 0 then boolSign (innerParity y b) else 0) *
          (if x < 2 ^ r then boolSign (innerParity x ((a % 2 ^ r) ^^^ (π 0 % 2 ^ r))) else 0) := by
        intro x hx
        have hdiv : (x + 2 ^ k * y) / 2 ^ k = y := by
          rw [Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt hx, Nat.add_zero]
        have hmod : (x + 2 ^ k * y) % 2 ^ k = x := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
        dsimp only [δ]
        rw [hdiv, hmod, hw_eq, innerParity_add_pow2_mul k x y a b hx ha, boolSign_xor]
        by_cases hy0 : y % 2 ^ r = 0
        · by_cases hxr : x < 2 ^ r
          · simp only [hy0, hxr, and_self, ↓reduceIte]
            rw [innerParity_xor_right, boolSign_xor, innerParity_mod_pow2 r x a hxr]
            ac_rfl
          · simp [hy0, hxr]
        · simp [hy0]
      rw [sumRange_congr (2 ^ k) _ _ hterm, sumRange_mul_left]
      congr 1
      rw [sumRange_filter_lt (2 ^ r) (2 ^ k) (Nat.pow_le_pow_right (by omega) hr)]
      have hxor_lt : (a % 2 ^ r) ^^^ (π 0 % 2 ^ r) < 2 ^ r :=
        Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos r)) (Nat.mod_lt _ (Nat.two_pow_pos r))
      rw [sumRange_innerParity r _ hxor_lt]
      have hiff : ((a % 2 ^ r) ^^^ (π 0 % 2 ^ r) = 0) ↔ (a % 2 ^ r = π 0 % 2 ^ r) := by
        constructor
        · intro h0
          have := congrArg (fun t => t ^^^ (π 0 % 2 ^ r)) h0
          simpa [Nat.xor_assoc, Nat.xor_self] using this
        · intro heq; rw [heq, Nat.xor_self]
      by_cases hcond : a % 2 ^ r = π 0 % 2 ^ r
      · have h0 := hiff.mpr hcond
        rw [h0]
        simp only [hcond, ↓reduceIte]
      · have h0 : (a % 2 ^ r) ^^^ (π 0 % 2 ^ r) ≠ 0 := fun hc => hcond (hiff.mp hc)
        simp only [h0, hcond, ↓reduceIte]
    rw [sumRange_congr (2 ^ k) _ _ hsplit_inner, sumRange_mul_right]
    have hysum : sumRange (2 ^ k) (fun y => if y % 2 ^ r = 0 then boolSign (innerParity y b) else 0) =
        if b < 2 ^ r then (2 ^ (k - r) : Int) else 0 := by
      have hk_split : 2 ^ k = 2 ^ r * 2 ^ (k - r) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [hk_split, sumRange_mul]
      have hinner_u : ∀ v < 2 ^ (k - r),
          sumRange (2 ^ r) (fun u => if (u + 2 ^ r * v) % 2 ^ r = 0 then boolSign (innerParity (u + 2 ^ r * v) b) else 0) =
          boolSign (innerParity v (b / 2 ^ r)) := by
        intro v _
        have hcu : ∀ u < 2 ^ r,
            (if (u + 2 ^ r * v) % 2 ^ r = 0 then boolSign (innerParity (u + 2 ^ r * v) b) else 0) =
            (if u = 0 then boolSign (innerParity v (b / 2 ^ r)) else 0) := by
          intro u hu
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
          by_cases hu0 : u = 0
          · subst hu0
            simp only [↓reduceIte, Nat.zero_add]
            have hb_eq : b = b % 2 ^ r + 2 ^ r * (b / 2 ^ r) := by
              have := Nat.div_add_mod b (2 ^ r); omega
            have h0lt : 0 < 2 ^ r := Nat.two_pow_pos r
            have hbm : b % 2 ^ r < 2 ^ r := Nat.mod_lt b h0lt
            have hip := innerParity_add_pow2_mul r 0 v (b % 2 ^ r) (b / 2 ^ r) h0lt hbm
            rw [Nat.zero_add, ← hb_eq, innerParity_zero_left, Bool.false_xor] at hip
            rw [hip]
          · simp [hu0]
        rw [sumRange_congr (2 ^ r) _ _ hcu, sumRange_single (2 ^ r) 0 (Nat.two_pow_pos r)]
      rw [sumRange_congr (2 ^ (k - r)) _ _ hinner_u]
      have hbd_lt : b / 2 ^ r < 2 ^ (k - r) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos r), ← Nat.pow_add]
        have : (k - r) + r = k := by omega
        rw [this]; exact hb
      rw [sumRange_innerParity (k - r) (b / 2 ^ r) hbd_lt]
      have hiff : (b / 2 ^ r = 0) ↔ (b < 2 ^ r) := Nat.div_eq_zero_iff_lt (Nat.two_pow_pos r)
      by_cases hblt : b < 2 ^ r
      · have h0 := hiff.mpr hblt; simp only [h0, hblt, ↓reduceIte]
      · have h0 : b / 2 ^ r ≠ 0 := fun hc => hblt (hiff.mp hc); simp only [h0, hblt, ↓reduceIte]
    rw [hysum]
    have hpow_mul : ((2 : Int) ^ (k - r)) * ((2 : Int) ^ r) = ((2 : Int) ^ k) := by
      rw [← Int.pow_add]; congr 1; omega
    by_cases ha_eq : a % 2 ^ r = π 0 % 2 ^ r
    · by_cases hb_lt : b < 2 ^ r
      · simp only [ha_eq, hb_lt, and_self, ↓reduceIte, hpow_mul]
      · simp only [ha_eq, hb_lt, and_false, ↓reduceIte, Int.zero_mul]
    · simp only [ha_eq, false_and, ↓reduceIte, Int.mul_zero]
  rw [hwalsh_δ]
  unfold mmDualSign carletTDualSign
  dsimp only
  simp only [Bool.xor_false]
  by_cases hc : w % 2 ^ k % 2 ^ r = π 0 % 2 ^ r ∧ w / 2 ^ k < 2 ^ r
  · have hca : a % 2 ^ r = π 0 % 2 ^ r ∧ b < 2 ^ r := hc
    simp only [hca, hc, and_self, decide_true, Bool.xor_true, ↓reduceIte, boolSign_not]
    have htinv_mod : tInv π k (w % 2 ^ k) % 2 ^ r = 0 := by
      have h1 := tInv_causal π k r (w % 2 ^ k) (π 0) hr hc.1
      rw [h1, tInv_left_inv hπ k 0]
      simp
    have hip0 : innerParity (w / 2 ^ k) (tInv π k (w % 2 ^ k)) = false :=
      innerParity_low_high_zero r (w / 2 ^ k) (tInv π k (w % 2 ^ k)) hc.2 htinv_mod
    rw [hip0, boolSign_false]
    omega
  · have hca : ¬ (a % 2 ^ r = π 0 % 2 ^ r ∧ b < 2 ^ r) := hc
    simp only [hca, hc, decide_false, Bool.xor_false, ↓reduceIte]
    omega

/-! ## Section 4B: Finite 4-Bit Hyperplane Certificate → Infinite Non-M# Lifting Engine -/

theorem LinSubspace.toX_zero {k : Nat} (V : LinSubspace k) : V.toX 0 = 0 := by
  have h := V.toX_xor 0 0 (Nat.two_pow_pos k) (Nat.two_pow_pos k)
  simpa [Nat.xor_self] using h

theorem LinSubspace.toY_zero {k : Nat} (V : LinSubspace k) : V.toY 0 = 0 := by
  have h := V.toY_xor 0 0 (Nat.two_pow_pos k) (Nat.two_pow_pos k)
  simpa [Nat.xor_self] using h

theorem sumRange_le (n : Nat) (f g : Nat → Int) (h : ∀ i < n, f i ≤ g i) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ n ih =>
    simp only [sumRange]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    omega

theorem sumRange_nonneg (n : Nat) (f : Nat → Int) (h : ∀ i < n, 0 ≤ f i) :
    0 ≤ sumRange n f := by
  have := sumRange_le n (fun _ => 0) f h
  simpa [sumRange_zero] using this

theorem sumRange_eq_of_le (n : Nat) (f g : Nat → Int)
    (hle : ∀ i < n, f i ≤ g i) (heq : sumRange n f = sumRange n g) :
    ∀ i < n, f i = g i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [sumRange] at heq
    have h1 : sumRange n f ≤ sumRange n g := sumRange_le n f g (fun i hi => hle i (by omega))
    have h2 : f n ≤ g n := hle n (by omega)
    have hsum_eq : sumRange n f = sumRange n g := by omega
    have hlast_eq : f n = g n := by omega
    intro i hi
    by_cases hin : i = n
    · subst hin; exact hlast_eq
    · exact ih (fun j hj => hle j (by omega)) hsum_eq i (by omega)

theorem exists_ge_of_sumRange_ge (n : Nat) (f : Nat → Int) (c : Int)
    (hn : 0 < n) (hsum : (n : Int) * c ≤ sumRange n f) :
    ∃ i < n, c ≤ f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumRange, Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul] at hsum
    by_cases hlast : c ≤ f n
    · exact ⟨n, by omega, hlast⟩
    · have hn' : 0 < n := by
        cases n with
        | zero => simp [sumRange] at hsum; omega
        | succ m => omega
      have hsum' : (n : Int) * c ≤ sumRange n f := by omega
      rcases ih hn' hsum' with ⟨i, hi, hci⟩
      exact ⟨i, by omega, hci⟩

theorem sumRange_xor_perm (k s0 : Nat) (hs0 : s0 < 2 ^ k) (f : Nat → Int) :
    sumRange (2 ^ k) (fun s => f (s ^^^ s0)) = sumRange (2 ^ k) f := by
  induction k generalizing s0 f with
  | zero =>
    have hs : s0 = 0 := by omega
    subst hs; simp [sumRange]
  | succ k ih =>
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hs0' : s0 / 2 < 2 ^ k := by rw [Nat.pow_succ] at hs0; omega
    rw [hp, sumRange_two_mul, sumRange_two_mul]
    rcases Nat.mod_two_eq_zero_or_one s0 with hm | hm
    · have hs_eq : s0 = 2 * (s0 / 2) := by omega
      have he : ∀ i, f ((2 * i) ^^^ s0) = f (2 * (i ^^^ (s0 / 2))) := by
        intro i; conv => lhs; rw [hs_eq, xor_two_mul_even]
      have ho : ∀ i, f ((2 * i + 1) ^^^ s0) = f (2 * (i ^^^ (s0 / 2)) + 1) := by
        intro i; conv => lhs; rw [hs_eq, xor_two_mul_add_one_even]
      rw [sumRange_congr (2 ^ k) _ _ (fun i _ => he i),
          sumRange_congr (2 ^ k) _ _ (fun i _ => ho i),
          ih (s0 / 2) hs0' (fun i => f (2 * i)),
          ih (s0 / 2) hs0' (fun i => f (2 * i + 1))]
    · have hs_eq : s0 = 2 * (s0 / 2) + 1 := by omega
      have he : ∀ i, f ((2 * i) ^^^ s0) = f (2 * (i ^^^ (s0 / 2)) + 1) := by
        intro i; conv => lhs; rw [hs_eq, xor_two_mul_odd]
      have ho : ∀ i, f ((2 * i + 1) ^^^ s0) = f (2 * (i ^^^ (s0 / 2))) := by
        intro i; conv => lhs; rw [hs_eq, xor_two_mul_add_one_odd]
      rw [sumRange_congr (2 ^ k) _ _ (fun i _ => he i),
          sumRange_congr (2 ^ k) _ _ (fun i _ => ho i),
          ih (s0 / 2) hs0' (fun i => f (2 * i + 1)),
          ih (s0 / 2) hs0' (fun i => f (2 * i)),
          Int.add_comm]

theorem existsLtB_eq_true_iff (n : Nat) (p : Nat → Bool) :
    existsLtB n p = true ↔ ∃ i < n, p i = true := by
  induction n with
  | zero => simp [existsLtB]
  | succ n ih =>
    simp only [existsLtB, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, hp⟩ | hp)
      · exact ⟨i, by omega, hp⟩
      · exact ⟨n, by omega, hp⟩
    · rintro ⟨i, hi, hp⟩
      by_cases hin : i = n
      · right; subst hin; exact hp
      · left; exact ⟨i, by omega, hp⟩

theorem forallLtB_eq_true_iff (n : Nat) (p : Nat → Bool) :
    forallLtB n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [forallLtB]
  | succ n ih =>
    simp only [forallLtB, Bool.and_eq_true, ih]
    constructor
    · intro ⟨h1, h2⟩ i hi
      by_cases hin : i = n
      · subst hin; exact h2
      · exact h1 i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

/-- Pontryagin Duality on `F_2^4` proved directly via `walsh_walsh 4`:
    Every XOR-closed subgroup `p : Nat → Bool` of `[0, 16)` with at least 8 elements
    contains some hyperplane `H_lam = {v < 16 : <lam, v> = 0}` with `1 ≤ lam < 16`. -/
theorem subgroup4_contains_hyperplane (p : Nat → Bool)
    (hp0 : p 0 = true)
    (hpxor : ∀ x < 16, ∀ y < 16, p x = true → p y = true → p (x ^^^ y) = true)
    (hcnt : 8 ≤ sumRange 16 (fun y => if p y then (1 : Int) else 0)) :
    ∃ lam : Fin 16, lam.val ≠ 0 ∧ ∀ v < 16, innerParity lam.val v = false → p v = true := by
  let f : Nat → Int := fun y => if p y then 1 else 0
  let S : Int := sumRange 16 f
  have hS_ge : 8 ≤ S := hcnt
  have hS_le : S ≤ 16 := by
    have := sumRange_le 16 f (fun _ => 1) (fun i _ => by dsimp only [f]; split <;> omega)
    simpa [sumRange_const] using this
  by_cases hS16 : S = 16
  · -- All 16 elements are in `p`, so `lam = 1` works trivially!
    have hall : ∀ v < 16, p v = true := by
      have heq := sumRange_eq_of_le 16 f (fun _ => 1)
        (fun i _ => by dsimp only [f]; split <;> omega)
        (by simpa [sumRange_const] using hS16)
      intro v hv
      have hfv := heq v hv
      dsimp only [f] at hfv
      cases hpv : p v <;> simp_all
    exact ⟨⟨1, by omega⟩, by simp, fun v hv _ => hall v hv⟩
  · -- Compute `walsh 4 f lam` for each `lam < 16`
    let inPerp : Nat → Bool := fun lam => forallLtB 16 (fun y => !p y || !innerParity lam y)
    have hwalsh_f : ∀ lam < 16, walsh 4 f lam = (if inPerp lam then (1 : Int) else 0) * S := by
      intro lam _
      rw [walsh_eq_sumRange]
      have h16 : (2 : Nat) ^ 4 = 16 := rfl
      rw [h16]
      by_cases hp_in : inPerp lam = true
      · simp only [hp_in, ↓reduceIte, Int.one_mul]
        have hall := (forallLtB_eq_true_iff 16 _).mp hp_in
        apply sumRange_congr
        intro y hy
        dsimp only [f]
        cases hpy : p y
        · simp
        · have hy' := hall y hy
          simp only [hpy, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hy'
          rw [innerParity_comm y lam, hy', boolSign_false, Int.one_mul]
      · simp only [hp_in, Bool.false_eq_true, ↓reduceIte, Int.zero_mul]
        have hex : existsLtB 16 (fun y => p y && innerParity lam y) = true := by
          by_cases h : existsLtB 16 (fun y => p y && innerParity lam y) = true
          · exact h
          · exfalso
            apply hp_in
            rw [forallLtB_eq_true_iff]
            intro y hy
            cases hpy : p y
            · simp
            · cases hip : innerParity lam y
              · simp
              · exfalso; apply h
                rw [existsLtB_eq_true_iff]
                exact ⟨y, hy, by simp [hpy, hip]⟩
        rcases (existsLtB_eq_true_iff 16 _).mp hex with ⟨y0, hy0, hboth⟩
        simp only [Bool.and_eq_true] at hboth
        rcases hboth with ⟨hpy0, hip0⟩
        -- Re-index sum by `y ↦ y ^^^ y0` to show `sum = -sum`, hence `sum = 0`
        have hperm := sumRange_xor_perm 4 y0 hy0 (fun y => boolSign (innerParity y lam) * f y)
        have hneg : ∀ y < 16,
            boolSign (innerParity (y ^^^ y0) lam) * f (y ^^^ y0) =
            -(boolSign (innerParity y lam) * f y) := by
          intro y hy
          rw [innerParity_xor_left, boolSign_xor, innerParity_comm y0 lam, hip0, boolSign_true]
          have hfeq : f (y ^^^ y0) = f y := by
            dsimp only [f]
            cases hpy : p y
            · cases hpy' : p (y ^^^ y0)
              · rfl
              · exfalso
                have hlt : y ^^^ y0 < 16 := Nat.xor_lt_two_pow (n := 4) hy hy0
                have hback := hpxor (y ^^^ y0) hlt y0 hy0 hpy' hpy0
                rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at hback
                rw [hpy] at hback; cases hback
            · have hpy' := hpxor y hy y0 hy0 hpy hpy0
              simp [hpy']
          rw [hfeq, Int.mul_neg, Int.mul_one, Int.neg_mul]
        rw [h16] at hperm
        rw [sumRange_congr 16 _ _ hneg] at hperm
        have hneg_sum : sumRange 16 (fun y => -(boolSign (innerParity y lam) * f y)) =
                        -sumRange 16 (fun y => boolSign (innerParity y lam) * f y) := by
          have := sumRange_mul_left 16 (-1) (fun y => boolSign (innerParity y lam) * f y)
          have h1 : sumRange 16 (fun y => -(boolSign (innerParity y lam) * f y)) =
                    sumRange 16 (fun y => (-1 : Int) * (boolSign (innerParity y lam) * f y)) := by
            apply sumRange_congr; intro i _; omega
          rw [h1, this]; omega
        rw [hneg_sum] at hperm
        omega
    -- Apply Hadamard involution at x = 0: `P * S = 16`!
    have hinv := walsh_walsh 4 f 0 (by decide)
    rw [walsh_eq_sumRange] at hinv
    have h16 : (2 : Nat) ^ 4 = 16 := rfl
    rw [h16] at hinv
    have hsum_perp : sumRange 16 (fun lam => boolSign (innerParity lam 0) * walsh 4 f lam) =
                     sumRange 16 (fun lam => if inPerp lam then (1 : Int) else 0) * S := by
      rw [← sumRange_mul_right]
      apply sumRange_congr; intro lam hlam
      rw [innerParity_zero_right, boolSign_false, Int.one_mul, hwalsh_f lam hlam]
    rw [hsum_perp] at hinv
    have hf0 : f 0 = 1 := by simp [f, hp0]
    rw [hf0] at hinv
    let P : Int := sumRange 16 (fun lam => if inPerp lam then (1 : Int) else 0)
    have hPS : P * S = 16 := by
      change P * S = ((2 : Int) ^ 4) * 1 at hinv
      simpa using hinv
    -- Since `8 ≤ S < 16` and `P * S = 16`, we must have `S = 8` and `P = 2`!
    have hS8 : S = 8 := by
      have hP_pos : 0 < P := by
        by_cases h : P ≤ 0
        · have : P * S ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg h (by omega)
          omega
        · omega
      have hP_ge2 : 2 ≤ P := by
        by_cases h1 : P = 1
        · rw [h1, Int.one_mul] at hPS; exact absurd hPS hS16
        · omega
      have hmul : 2 * S ≤ P * S := Int.mul_le_mul_of_nonneg_right hP_ge2 (by omega)
      omega
    have hP2 : P = 2 := by rw [hS8] at hPS; omega
    -- Extract a nonzero `lam < 16` with `inPerp lam = true`
    have hperp0 : inPerp 0 = true := by
      rw [forallLtB_eq_true_iff]; intro y _; simp [innerParity_zero_left]
    have hex_lam : existsLtB 16 (fun lam => decide (lam ≠ 0) && inPerp lam) = true := by
      by_cases h : existsLtB 16 (fun lam => decide (lam ≠ 0) && inPerp lam) = true
      · exact h
      · exfalso
        have hP1 : P = 1 := by
          have hcongr : ∀ lam < 16,
              (if inPerp lam then (1 : Int) else 0) = (if lam = 0 then (1 : Int) else 0) := by
            intro lam hlam
            by_cases h0 : lam = 0
            · subst h0; simp [hperp0]
            · have hfalse : inPerp lam = false := by
                cases hp' : inPerp lam
                · rfl
                · exfalso; apply h
                  rw [existsLtB_eq_true_iff]
                  exact ⟨lam, hlam, by simp [h0, hp']⟩
              simp [h0, hfalse]
          change sumRange 16 (fun lam => if inPerp lam then (1 : Int) else 0) = 1
          rw [sumRange_congr 16 _ _ hcongr, sumRange_single 16 0 (by omega) 1]
        omega
    rcases (existsLtB_eq_true_iff 16 _).mp hex_lam with ⟨lam, hlam_lt, hlam_both⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlam_both
    rcases hlam_both with ⟨hlam_ne, hlam_perp⟩
    have hsub : ∀ v < 16, p v = true → innerParity lam v = false := by
      have hall := (forallLtB_eq_true_iff 16 _).mp hlam_perp
      intro v hv hpv
      have hv' := hall v hv
      simpa [hpv] using hv'
    -- Count `H_lam = {v < 16 : innerParity lam v = false}` using `sumRange_innerParity 4 lam`
    let g : Nat → Int := fun v => if innerParity lam v == false then 1 else 0
    have hH_cnt : sumRange 16 g = 8 := by
      have hbal := sumRange_innerParity 4 lam hlam_lt
      simp only [hlam_ne, ↓reduceIte] at hbal
      have hrel : sumRange 16 (fun v => boolSign (innerParity v lam)) = 2 * sumRange 16 g - 16 := by
        have h1 : 2 * sumRange 16 g - 16 = sumRange 16 (fun v => 2 * g v - 1) := by
          rw [sumRange_sub, sumRange_mul_left, sumRange_const]; rfl
        rw [h1]
        apply sumRange_congr; intro v _
        dsimp only [g]
        rw [innerParity_comm v lam]
        cases innerParity lam v <;> rfl
      have h16' : (2 : Nat) ^ 4 = 16 := rfl
      rw [h16', hrel] at hbal
      omega
    have hle : ∀ v < 16, f v ≤ g v := by
      intro v hv
      dsimp only [f, g]
      cases hpv : p v
      · cases innerParity lam v <;> simp
      · have := hsub v hv hpv; simp [this]
    have hfg_eq : ∀ v < 16, f v = g v :=
      sumRange_eq_of_le 16 f g hle (by rw [hH_cnt]; exact hS8)
    refine ⟨⟨lam, hlam_lt⟩, hlam_ne, ?_⟩
    intro v hv hip
    have heq := hfg_eq v hv
    dsimp only [f, g] at heq
    simp only [hip, beq_self_eq_true, ↓reduceIte] at heq
    cases hpv : p v <;> simp_all

private theorem exists_not_in_list (L : List Nat) :
    ∃ v < L.length + 2, v ≠ 0 ∧ v ∉ L := by
  let p : Nat → Bool := fun v => decide (v ≠ 0 ∧ v ∉ L)
  by_cases hex : existsLtB (L.length + 2) p = true
  · rcases (existsLtB_eq_true_iff (L.length + 2) p).mp hex with ⟨v, hv_lt, hpv⟩
    dsimp only [p] at hpv
    simp only [decide_eq_true_eq] at hpv
    exact ⟨v, hv_lt, hpv.1, hpv.2⟩
  · exfalso
    have hmem_all : ∀ v, 1 ≤ v → v < L.length + 2 → v ∈ L := by
      intro v hv1 hv2
      by_cases hm : v ∈ L
      · exact hm
      · exfalso; apply hex
        rw [existsLtB_eq_true_iff]
        refine ⟨v, hv2, ?_⟩
        dsimp only [p]
        simp [show v ≠ 0 by omega, hm]
    have hcount_le : ∀ (M : List Nat) (n : Nat),
        sumRange n (fun v => if v ∈ M then (1 : Int) else 0) ≤ (M.length : Int) := by
      intro M
      induction M with
      | nil =>
        intro n
        have : sumRange n (fun _ => (0 : Int)) = 0 := sumRange_zero n
        simp [this]
      | cons a tl ih =>
        intro n
        have hstep : ∀ v < n,
            (if v ∈ a :: tl then (1 : Int) else 0) ≤
            (if v = a then (1 : Int) else 0) + (if v ∈ tl then (1 : Int) else 0) := by
          intro v _
          by_cases hva : v = a
          · subst hva; by_cases htl : v ∈ tl <;> simp [htl]
          · by_cases htl : v ∈ tl <;> simp [hva, htl]
        have h1 := sumRange_le n _ _ hstep
        rw [sumRange_add] at h1
        have h2 := ih n
        have ha_le : sumRange n (fun v => if v = a then (1 : Int) else 0) ≤ 1 := by
          by_cases ha_lt : a < n
          · rw [sumRange_single n a ha_lt 1]; exact Int.le_refl 1
          · rw [sumRange_congr n _ (fun _ => 0) (fun v hv => by simp [show v ≠ a by omega]), sumRange_zero]
            omega
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
        omega
    have hlow : (L.length + 1 : Int) ≤ sumRange (L.length + 2) (fun v => if v ∈ L then (1 : Int) else 0) := by
      have hge : ∀ v < L.length + 2,
          (if v = 0 then (0 : Int) else 1) ≤ (if v ∈ L then (1 : Int) else 0) := by
        intro v hv
        by_cases hv0 : v = 0
        · subst hv0; split <;> omega
        · have hm := hmem_all v (by omega) hv
          simp [hv0, hm]
      have hle := sumRange_le (L.length + 2) _ _ hge
      have hsum_nz : sumRange (L.length + 2) (fun v => if v = 0 then (0 : Int) else 1) = (L.length + 1 : Int) := by
        have hsub : sumRange (L.length + 2) (fun v => if v = 0 then (0 : Int) else 1) =
                    sumRange (L.length + 2) (fun _ => (1 : Int)) -
                    sumRange (L.length + 2) (fun v => if v = 0 then (1 : Int) else 0) := by
          rw [← sumRange_sub]
          apply sumRange_congr; intro v _; by_cases hv : v = 0 <;> simp [hv]
        rw [hsub, sumRange_const, sumRange_single (L.length + 2) 0 (by omega) 1]
        omega
      omega
    have hhi := hcount_le L (L.length + 2)
    omega

private theorem xor_ne_of_ne {x y z : Nat} (h : y ≠ x ^^^ z) : x ^^^ y ≠ z := by
  intro heq
  apply h
  rw [← heq, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

private theorem bitParity_two_pow (i : Nat) : bitParity (2 ^ i) = true := by
  induction i with
  | zero =>
    change bitParity (2 * 0 + 1) = true
    rw [bitParity_two_mul_add_one, bitParity_zero]; rfl
  | succ i ih =>
    have h : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ]; omega
    rw [h, bitParity_two_mul, ih]

private theorem innerParity_two_pow (i n : Nat) : innerParity (2 ^ i) n = n.testBit i := by
  unfold innerParity
  have hand : 2 ^ i &&& n = if n.testBit i then 2 ^ i else 0 := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hji : i = j
    · subst hji; cases n.testBit i <;> simp [Nat.testBit_two_pow_self]
    · cases n.testBit i <;> simp [hji]
  rw [hand]
  cases n.testBit i
  · simp [bitParity_zero]
  · simp only [↓reduceIte, bitParity_two_pow]

private theorem exists_testBit_true_lt4 (m : Nat) (hm : m % 16 ≠ 0) :
    ∃ i < 4, m.testBit i = true := by
  by_cases h0 : m.testBit 0 = true
  · exact ⟨0, by omega, h0⟩
  · by_cases h1 : m.testBit 1 = true
    · exact ⟨1, by omega, h1⟩
    · by_cases h2 : m.testBit 2 = true
      · exact ⟨2, by omega, h2⟩
      · by_cases h3 : m.testBit 3 = true
        · exact ⟨3, by omega, h3⟩
        · exfalso; apply hm
          rw [show (0 : Nat) = 0 % 16 from rfl, show (16 : Nat) = 2 ^ 4 from rfl, mod_two_pow_eq_iff_testBit]
          intro i hi
          have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases this with rfl | rfl | rfl | rfl
          · cases h : m.testBit 0 <;> simp_all
          · cases h : m.testBit 1 <;> simp_all
          · cases h : m.testBit 2 <;> simp_all
          · cases h : m.testBit 3 <;> simp_all

/-- **FINITE-TO-INFINITE NON-M# LIFTING ENGINE:**
    Given ANY function `π : Nat → Nat` passing the 15-entry finite 4-bit hyperplane certificate
    `NonMMCert4 π`, the Silicon Carlet-T function `carletTBool k 0 π`
    (`f(x, y) = <x, π(y) mod 2^k> ⊕ [x = 0]`) has NO `k`-dimensional vanishing subspace
    (hence escapes the completed Maiorana-McFarland class `M#`) for EVERY `k ≥ 4`! -/
theorem carletT0_not_hasVanishingSubspace {π : Nat → Nat}
    (hcert : NonMMCert4 π) (k : Nat) (hk : 4 ≤ k) :
    ¬ HasVanishingSubspace k (carletTBool k 0 π) := by
  intro ⟨V, hvan⟩
  have h16_le : 16 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hk
    simpa using this
  have h2k_eq : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  have hcb : ∀ x y : Nat, x < 2 ^ k →
      carletTBool k 0 π (x + 2 ^ k * y) = xor (innerParity x (π y % 2 ^ k)) (decide (x = 0)) := by
    intro x y hx
    unfold carletTBool
    have hdiv : (x + 2 ^ k * y) / 2 ^ k = y := by
      rw [Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt hx, Nat.add_zero]
    have hmod : (x + 2 ^ k * y) % 2 ^ k = x := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    simp [hdiv, hmod, Nat.mod_one]
  -- STEP 1: `V.toX` takes at most 2 distinct values `{0, a0}`!
  have htoX_two : ∀ s < 2 ^ k, ∀ t < 2 ^ k, V.toX s = 0 ∨ V.toX t = 0 ∨ V.toX s = V.toX t := by
    intro s hs t ht
    by_cases ha0 : V.toX s = 0
    · left; exact ha0
    · by_cases hc0 : V.toX t = 0
      · right; left; exact hc0
      · by_cases hac : V.toX s = V.toX t
        · right; right; exact hac
        · exfalso
          let a := V.toX s; let b := V.toY s
          let c := V.toX t; let d := V.toY t
          have ha_ne0 : a ≠ 0 := ha0
          have hc_ne0 : c ≠ 0 := hc0
          have ha_lt : a < 2 ^ k := V.toX_lt s hs
          have hc_lt : c < 2 ^ k := V.toX_lt t ht
          have hac_ne : a ^^^ c ≠ 0 := by
            intro h0; apply hac
            have := congrArg (fun z => z ^^^ c) h0
            simpa [Nat.xor_assoc, Nat.xor_self] using this
          rcases exists_not_in_list [a, c, a ^^^ c] with ⟨u, hu5, hu0, hu_nmem⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu_nmem
          rcases hu_nmem with ⟨hua, huc, huac⟩
          rcases exists_not_in_list [a, c, a ^^^ c, u, u ^^^ a, u ^^^ c, u ^^^ (a ^^^ c)] with ⟨v, hv9, hv0, hv_nmem⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv_nmem
          rcases hv_nmem with ⟨hva, hvc, hvac, hvu, hvua, hvuc, hvuac⟩
          have hu_lt : u < 2 ^ k := by simp only [List.length_cons, List.length_nil] at hu5; omega
          have hv_lt : v < 2 ^ k := by simp only [List.length_cons, List.length_nil] at hv9; omega
          have hu16 : u < 16 := by simp only [List.length_cons, List.length_nil] at hu5; omega
          have hv16 : v < 16 := by simp only [List.length_cons, List.length_nil] at hv9; omega
          have huv_lt : u ^^^ v < 2 ^ k := Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 4) hu16 hv16) h16_le
          have huv0 : u ^^^ v ≠ 0 := by
            intro h0; apply hvu
            have := congrArg (fun z => z ^^^ v) h0
            have : u = v := by simpa [Nat.xor_assoc, Nat.xor_self] using this
            exact this.symm
          have huva : u ^^^ v ≠ a := xor_ne_of_ne hvua
          have huvc : u ^^^ v ≠ c := xor_ne_of_ne hvuc
          have huvac : u ^^^ v ≠ a ^^^ c := xor_ne_of_ne hvuac
          have hsd : ∀ x < 2 ^ k,
              secondDeriv (carletTBool k 0 π) (a + 2 ^ k * b) (c + 2 ^ k * d) x =
              xor (xor (innerParity x ((π 0 % 2 ^ k) ^^^ (π b % 2 ^ k) ^^^ (π d % 2 ^ k) ^^^ (π (b ^^^ d) % 2 ^ k)))
                       (xor (xor (innerParity a (π b % 2 ^ k)) (innerParity c (π d % 2 ^ k)))
                            (innerParity (a ^^^ c) (π (b ^^^ d) % 2 ^ k))))
                  (xor (xor (decide (x = 0)) (decide (x ^^^ a = 0)))
                       (xor (decide (x ^^^ c = 0)) (decide (x ^^^ a ^^^ c = 0)))) := by
            intro x hx
            unfold secondDeriv
            have hx0 : x = x + 2 ^ k * 0 := by omega
            have hxa_lt : x ^^^ a < 2 ^ k := Nat.xor_lt_two_pow hx ha_lt
            have hxc_lt : x ^^^ c < 2 ^ k := Nat.xor_lt_two_pow hx hc_lt
            have hxac_lt : x ^^^ a ^^^ c < 2 ^ k := Nat.xor_lt_two_pow hxa_lt hc_lt
            have h1 : x ^^^ (a + 2 ^ k * b) = (x ^^^ a) + 2 ^ k * b := by
              conv => lhs; rw [hx0]
              rw [xor_add_pow2_mul k x 0 a b hx ha_lt, Nat.zero_xor]
            have h2 : x ^^^ (c + 2 ^ k * d) = (x ^^^ c) + 2 ^ k * d := by
              conv => lhs; rw [hx0]
              rw [xor_add_pow2_mul k x 0 c d hx hc_lt, Nat.zero_xor]
            have h3 : x ^^^ (a + 2 ^ k * b) ^^^ (c + 2 ^ k * d) = (x ^^^ a ^^^ c) + 2 ^ k * (b ^^^ d) := by
              rw [h1, xor_add_pow2_mul k (x ^^^ a) b c d hxa_lt hc_lt]
            rw [h3, h2, h1]
            conv => lhs; arg 1; arg 1; rw [hx0]
            rw [hcb x 0 hx, hcb (x ^^^ a) b hxa_lt, hcb (x ^^^ c) d hxc_lt, hcb (x ^^^ a ^^^ c) (b ^^^ d) hxac_lt]
            rw [innerParity_xor_left x a, innerParity_xor_left x c,
                Nat.xor_assoc x a c, innerParity_xor_left x (a ^^^ c), ← Nat.xor_assoc x a c]
            rw [innerParity_xor_right, innerParity_xor_right, innerParity_xor_right]
            generalize innerParity x (π 0 % 2 ^ k) = p0
            generalize innerParity x (π b % 2 ^ k) = p1
            generalize innerParity x (π d % 2 ^ k) = p2
            generalize innerParity x (π (b ^^^ d) % 2 ^ k) = p3
            generalize innerParity a (π b % 2 ^ k) = q1
            generalize innerParity c (π d % 2 ^ k) = q2
            generalize innerParity (a ^^^ c) (π (b ^^^ d) % 2 ^ k) = q3
            generalize decide (x = 0) = r0
            generalize decide (x ^^^ a = 0) = r1
            generalize decide (x ^^^ c = 0) = r2
            generalize decide (x ^^^ a ^^^ c = 0) = r3
            cases p0 <;> cases p1 <;> cases p2 <;> cases p3 <;>
            cases q1 <;> cases q2 <;> cases q3 <;>
            cases r0 <;> cases r1 <;> cases r2 <;> cases r3 <;> rfl
          have hlt2k : ∀ x < 2 ^ k, x < 2 ^ (2 * k) := by
            intro x hx
            have hpos : 1 ≤ 2 ^ k := Nat.two_pow_pos k
            have hle : 2 ^ k ≤ 2 ^ k * 2 ^ k := Nat.le_mul_of_pos_right (2 ^ k) hpos
            omega
          have e0 := hvan s hs t ht 0 (hlt2k 0 (Nat.two_pow_pos k))
          have eu := hvan s hs t ht u (hlt2k u hu_lt)
          have ev := hvan s hs t ht v (hlt2k v hv_lt)
          have euv := hvan s hs t ht (u ^^^ v) (hlt2k (u ^^^ v) huv_lt)
          rw [hsd 0 (Nat.two_pow_pos k)] at e0
          rw [hsd u hu_lt] at eu
          rw [hsd v hv_lt] at ev
          rw [hsd (u ^^^ v) huv_lt] at euv
          have hne_xor : ∀ x y : Nat, x ≠ y → x ^^^ y ≠ 0 := by
            intro x y hxy h0; apply hxy
            have := congrArg (fun z => z ^^^ y) h0
            simpa [Nat.xor_assoc, Nat.xor_self] using this
          have hne_xor3 : ∀ x : Nat, x ≠ a ^^^ c → x ^^^ a ^^^ c ≠ 0 := by
            intro x hne; rw [Nat.xor_assoc]; exact hne_xor x (a ^^^ c) hne
          have hr0 : xor (xor (decide ((0 : Nat) = 0)) (decide (0 ^^^ a = 0)))
                         (xor (decide (0 ^^^ c = 0)) (decide (0 ^^^ a ^^^ c = 0))) = true := by
            simp [Nat.zero_xor, ha_ne0, hc_ne0, hac_ne]
          have hru : xor (xor (decide (u = 0)) (decide (u ^^^ a = 0)))
                         (xor (decide (u ^^^ c = 0)) (decide (u ^^^ a ^^^ c = 0))) = false := by
            simp [hu0, hne_xor u a hua, hne_xor u c huc, hne_xor3 u huac]
          have hrv : xor (xor (decide (v = 0)) (decide (v ^^^ a = 0)))
                         (xor (decide (v ^^^ c = 0)) (decide (v ^^^ a ^^^ c = 0))) = false := by
            simp [hv0, hne_xor v a hva, hne_xor v c hvc, hne_xor3 v hvac]
          have hruv : xor (xor (decide (u ^^^ v = 0)) (decide ((u ^^^ v) ^^^ a = 0)))
                          (xor (decide ((u ^^^ v) ^^^ c = 0)) (decide ((u ^^^ v) ^^^ a ^^^ c = 0))) = false := by
            simp [huv0, hne_xor (u ^^^ v) a huva, hne_xor (u ^^^ v) c huvc, hne_xor3 (u ^^^ v) huvac]
          rw [hr0, innerParity_zero_left, Bool.false_xor] at e0
          rw [hru, Bool.xor_false] at eu
          rw [hrv, Bool.xor_false] at ev
          rw [hruv, Bool.xor_false, innerParity_xor_left] at euv
          generalize innerParity u ((π 0 % 2 ^ k) ^^^ (π b % 2 ^ k) ^^^ (π d % 2 ^ k) ^^^ (π (b ^^^ d) % 2 ^ k)) = pu at eu euv
          generalize innerParity v ((π 0 % 2 ^ k) ^^^ (π b % 2 ^ k) ^^^ (π d % 2 ^ k) ^^^ (π (b ^^^ d) % 2 ^ k)) = pv at ev euv
          generalize xor (xor (innerParity a (π b % 2 ^ k)) (innerParity c (π d % 2 ^ k)))
                         (innerParity (a ^^^ c) (π (b ^^^ d) % 2 ^ k)) = C at e0 eu ev euv
          cases pu <;> cases pv <;> cases C <;> simp_all
  -- STEP 2: Kernel `ker = {s < 2^k : V.toX s = 0}` has size `≥ 2^(k-1)`
  have hker_ge : (2 ^ (k - 1) : Int) ≤ sumRange (2 ^ k) (fun s => if V.toX s = 0 then (1 : Int) else 0) := by
    by_cases hall0 : ∀ s < 2 ^ k, V.toX s = 0
    · have hfull : sumRange (2 ^ k) (fun s => if V.toX s = 0 then (1 : Int) else 0) = (2 ^ k : Int) := by
        rw [sumRange_congr (2 ^ k) _ (fun _ => 1) (fun s hs => by simp [hall0 s hs]), sumRange_const, Int.mul_one]
        exact Int.natCast_pow 2 k
      rw [hfull]
      have hle : 2 ^ (k - 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have hcast : ((2 ^ (k - 1) : Nat) : Int) ≤ ((2 ^ k : Nat) : Int) := Int.ofNat_le.mpr hle
      simpa [Int.natCast_pow] using hcast
    · have hex : existsLtB (2 ^ k) (fun s => decide (V.toX s ≠ 0)) = true := by
        by_cases h : existsLtB (2 ^ k) (fun s => decide (V.toX s ≠ 0)) = true
        · exact h
        · exfalso; apply hall0; intro s hs
          by_cases hs0 : V.toX s = 0
          · exact hs0
          · exfalso; apply h
            rw [existsLtB_eq_true_iff]
            exact ⟨s, hs, by simp [hs0]⟩
      rcases (existsLtB_eq_true_iff (2 ^ k) _).mp hex with ⟨s0, hs0, hne0⟩
      simp only [decide_eq_true_eq] at hne0
      have hpair : ∀ s < 2 ^ k,
          (if V.toX s = 0 then (1 : Int) else 0) + (if V.toX (s ^^^ s0) = 0 then (1 : Int) else 0) = 1 := by
        intro s hs
        rw [V.toX_xor s s0 hs hs0]
        rcases htoX_two s hs s0 hs0 with hs_zero | hs0_zero | heq
        · simp [hs_zero, Nat.zero_xor, hne0]
        · exact absurd hs0_zero hne0
        · simp [heq, hne0, Nat.xor_self]
      have hsum2 : sumRange (2 ^ k) (fun s => if V.toX s = 0 then (1 : Int) else 0) +
                   sumRange (2 ^ k) (fun s => if V.toX (s ^^^ s0) = 0 then (1 : Int) else 0) = (2 ^ k : Int) := by
        rw [← sumRange_add, sumRange_congr (2 ^ k) _ (fun _ => 1) hpair, sumRange_const, Int.mul_one]
        exact Int.natCast_pow 2 k
      rw [sumRange_xor_perm k s0 hs0 (fun s => if V.toX s = 0 then (1 : Int) else 0)] at hsum2
      have hpow : (2 ^ k : Int) = 2 * (2 ^ (k - 1) : Int) := by
        have : 2 ^ k = 2 * 2 ^ (k - 1) := by
          have hk1 : k = (k - 1) + 1 := by omega
          conv => lhs; rw [hk1, Nat.pow_succ]
          omega
        have hc : ((2 ^ k : Nat) : Int) = ((2 * 2 ^ (k - 1) : Nat) : Int) := by exact_mod_cast this
        simpa [Int.natCast_mul, Int.natCast_pow] using hc
      omega
  -- STEP 3: Pigeonhole on `q = V.toY s / 16 < 2^(k - 4)` gives a bucket of size `≥ 8`
  let bucket : Nat → Int := fun q =>
    sumRange (2 ^ k) (fun s => if V.toX s = 0 ∧ V.toY s / 16 = q then (1 : Int) else 0)
  have hsum_buckets : sumRange (2 ^ (k - 4)) bucket =
      sumRange (2 ^ k) (fun s => if V.toX s = 0 then (1 : Int) else 0) := by
    dsimp only [bucket]
    rw [sumRange_swap]
    apply sumRange_congr; intro s hs
    have hq_lt : V.toY s / 16 < 2 ^ (k - 4) := by
      have hy_lt : V.toY s < 2 ^ k := V.toY_lt s hs
      have hpow : 2 ^ k = 2 ^ (k - 4) * 16 := by
        have : (16 : Nat) = 2 ^ 4 := rfl
        rw [this, ← Nat.pow_add]; congr 1; omega
      rw [Nat.div_lt_iff_lt_mul (by omega), ← hpow]; exact hy_lt
    by_cases hx0 : V.toX s = 0
    · have hcongr : ∀ q < 2 ^ (k - 4),
          (if V.toX s = 0 ∧ V.toY s / 16 = q then (1 : Int) else 0) =
          (if q = V.toY s / 16 then (1 : Int) else 0) := by
        intro q _; by_cases hq : q = V.toY s / 16 <;> simp [hx0, hq, eq_comm]
      rw [sumRange_congr (2 ^ (k - 4)) _ _ hcongr, sumRange_single (2 ^ (k - 4)) (V.toY s / 16) hq_lt 1]
      simp [hx0]
    · rw [sumRange_congr (2 ^ (k - 4)) _ (fun _ => 0) (fun q _ => by simp [hx0]), sumRange_zero]
      simp [hx0]
  have h8mul : ((2 ^ (k - 4) : Nat) : Int) * 8 ≤ sumRange (2 ^ (k - 4)) bucket := by
    rw [hsum_buckets]
    have hpow : (2 ^ (k - 4) : Nat) * 8 = 2 ^ (k - 1) := by
      have : (8 : Nat) = 2 ^ 3 := rfl
      rw [this, ← Nat.pow_add]; congr 1; omega
    have hcast : ((2 ^ (k - 4) : Nat) : Int) * 8 = (2 ^ (k - 1) : Int) := by
      exact_mod_cast hpow
    rw [hcast]; exact hker_ge
  rcases exists_ge_of_sumRange_ge (2 ^ (k - 4)) bucket 8 (Nat.two_pow_pos (k - 4)) h8mul with ⟨q, hq_lt, hbq_ge⟩
  -- Pick one element `s0` in bucket `q`
  have hex_s0 : existsLtB (2 ^ k) (fun s => decide (V.toX s = 0 ∧ V.toY s / 16 = q)) = true := by
    by_cases h : existsLtB (2 ^ k) (fun s => decide (V.toX s = 0 ∧ V.toY s / 16 = q)) = true
    · exact h
    · exfalso
      have h0 : bucket q = 0 := by
        dsimp only [bucket]
        rw [sumRange_congr (2 ^ k) _ (fun _ => 0) (fun s hs => by
          by_cases hc : V.toX s = 0 ∧ V.toY s / 16 = q
          · exfalso; apply h; rw [existsLtB_eq_true_iff]; exact ⟨s, hs, by simp [hc]⟩
          · simp [hc]), sumRange_zero]
      omega
  rcases (existsLtB_eq_true_iff (2 ^ k) _).mp hex_s0 with ⟨s0, hs0, hs0_cond⟩
  simp only [decide_eq_true_eq] at hs0_cond
  rcases hs0_cond with ⟨hs0_x, hs0_q⟩
  -- STEP 4: Subgroup `K4 = {y < 16 : ∃ s < 2^k, V.toX s = 0 ∧ V.toY s = y}` has `≥ 8` elements!
  let inK4B : Nat → Bool := fun y => existsLtB (2 ^ k) (fun s => decide (V.toX s = 0 ∧ V.toY s = y))
  have hinK4_0 : inK4B 0 = true := by
    rw [existsLtB_eq_true_iff]
    exact ⟨0, Nat.two_pow_pos k, by simp [V.toX_zero, V.toY_zero]⟩
  have hinK4_xor : ∀ x < 16, ∀ y < 16, inK4B x = true → inK4B y = true → inK4B (x ^^^ y) = true := by
    intro x _ y _ hx hy
    rcases (existsLtB_eq_true_iff (2 ^ k) _).mp hx with ⟨sx, hsx, hcx⟩
    rcases (existsLtB_eq_true_iff (2 ^ k) _).mp hy with ⟨sy, hsy, hcy⟩
    simp only [decide_eq_true_eq] at hcx hcy
    rw [existsLtB_eq_true_iff]
    exact ⟨sx ^^^ sy, Nat.xor_lt_two_pow hsx hsy, by
      simp [V.toX_xor sx sy hsx hsy, V.toY_xor sx sy hsx hsy, hcx, hcy]⟩
  have hdiv16_xor : ∀ a b : Nat, (a ^^^ b) / 16 = (a / 16) ^^^ (b / 16) := by
    intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have htb : ∀ n : Nat, (n / 16).testBit i = n.testBit (i + 4) := by
      intro n
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
          Nat.div_div_eq_div_mul, show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add, Nat.add_comm 4 i]
    rw [htb (a ^^^ b), Nat.testBit_xor, Nat.testBit_xor, htb a, htb b]
  have hK4_cnt : 8 ≤ sumRange 16 (fun y => if inK4B y then (1 : Int) else 0) := by
    have hbq_eq : bucket q = sumRange 16 (fun y =>
        sumRange (2 ^ k) (fun s => if V.toX s = 0 ∧ V.toY s / 16 = q ∧ V.toY (s ^^^ s0) = y then (1 : Int) else 0)) := by
      rw [sumRange_swap]
      dsimp only [bucket]
      apply sumRange_congr; intro s hs
      by_cases hc : V.toX s = 0 ∧ V.toY s / 16 = q
      · have hlt16 : V.toY (s ^^^ s0) < 16 := by
          rw [V.toY_xor s s0 hs hs0]
          have hdiv0 : (V.toY s ^^^ V.toY s0) / 16 = 0 := by
            rw [hdiv16_xor, hc.2, hs0_q, Nat.xor_self]
          omega
        have hcongr : ∀ y < 16,
            (if V.toX s = 0 ∧ V.toY s / 16 = q ∧ V.toY (s ^^^ s0) = y then (1 : Int) else 0) =
            (if y = V.toY (s ^^^ s0) then (1 : Int) else 0) := by
          intro y _; by_cases hy : y = V.toY (s ^^^ s0) <;> simp [hc, hy, eq_comm]
        rw [sumRange_congr 16 _ _ hcongr, sumRange_single 16 (V.toY (s ^^^ s0)) hlt16 1]
        simp [hc]
      · rw [sumRange_congr 16 _ (fun _ => 0) (fun y _ => by
              have : ¬ (V.toX s = 0 ∧ V.toY s / 16 = q ∧ V.toY (s ^^^ s0) = y) := fun h => hc ⟨h.1, h.2.1⟩
              simp [this]), sumRange_zero]
        simp [hc]
    have hle_y : ∀ y < 16,
        sumRange (2 ^ k) (fun s => if V.toX s = 0 ∧ V.toY s / 16 = q ∧ V.toY (s ^^^ s0) = y then (1 : Int) else 0) ≤
        (if inK4B y then (1 : Int) else 0) := by
      intro y _
      by_cases hex : existsLtB (2 ^ k) (fun s => decide (V.toX s = 0 ∧ V.toY s / 16 = q ∧ V.toY (s ^^^ s0) = y)) = true
      · rcases (existsLtB_eq_true_iff (2 ^ k) _).mp hex with ⟨s1, hs1, hc1⟩
        simp only [decide_eq_true_eq] at hc1
        have hy_in : inK4B y = true := by
          rw [existsLtB_eq_true_iff]
          exact ⟨s1 ^^^ s0, Nat.xor_lt_two_pow hs1 hs0, by
            simp [V.toX_xor s1 s0 hs1 hs0, hc1.1, hs0_x, hc1.2.2]⟩
        have huniq : ∀ s < 2 ^ k,
            (if V.toX s = 0 ∧ V.toY s / 16 = q ∧ V.toY (s ^^^ s0) = y then (1 : Int) else 0) =
            (if s = s1 then (1 : Int) else 0) := by
          intro s hs
          by_cases hss1 : s = s1
          · subst hss1; simp [hc1]
          · have hnot : ¬ (V.toX s = 0 ∧ V.toY s / 16 = q ∧ V.toY (s ^^^ s0) = y) := by
              intro hcs; apply hss1
              have hxe : V.toX (s ^^^ s0) = V.toX (s1 ^^^ s0) := by
                rw [V.toX_xor s s0 hs hs0, V.toX_xor s1 s0 hs1 hs0, hcs.1, hc1.1]
              have hye : V.toY (s ^^^ s0) = V.toY (s1 ^^^ s0) := by rw [hcs.2.2, hc1.2.2]
              have heq := V.inj (s ^^^ s0) (s1 ^^^ s0) (Nat.xor_lt_two_pow hs hs0) (Nat.xor_lt_two_pow hs1 hs0) hxe hye
              have := congrArg (fun t => t ^^^ s0) heq
              simpa [Nat.xor_assoc, Nat.xor_self] using this
            simp [hss1, hnot]
        rw [sumRange_congr (2 ^ k) _ _ huniq, sumRange_single (2 ^ k) s1 hs1 1]
        simp [hy_in]
      · have h0 : sumRange (2 ^ k) (fun s => if V.toX s = 0 ∧ V.toY s / 16 = q ∧ V.toY (s ^^^ s0) = y then (1 : Int) else 0) = 0 := by
          rw [sumRange_congr (2 ^ k) _ (fun _ => 0) (fun s hs => by
            by_cases hc : V.toX s = 0 ∧ V.toY s / 16 = q ∧ V.toY (s ^^^ s0) = y
            · exfalso; apply hex; rw [existsLtB_eq_true_iff]; exact ⟨s, hs, by simp [hc]⟩
            · simp [hc]), sumRange_zero]
        rw [h0]; split <;> omega
    have hle_sum := sumRange_le 16 _ _ hle_y
    rw [← hbq_eq] at hle_sum
    omega
  -- STEP 5: Apply Pontryagin duality on `F_2^4` and fire the 15-hyperplane certificate `hcert`!
  rcases subgroup4_contains_hyperplane inK4B hinK4_0 hinK4_xor hK4_cnt with ⟨lam, hlam_ne, hlam_sub⟩
  have hval := hcert.valid lam hlam_ne
  dsimp only at hval
  rcases hval with ⟨hb16, hd16, hy16, hlam_b, hlam_d, hnonlin⟩
  let b := (hcert.witness lam).1
  let d := (hcert.witness lam).2.1
  let y := (hcert.witness lam).2.2
  have hb_in : inK4B b = true := hlam_sub b hb16 hlam_b
  have hd_in : inK4B d = true := hlam_sub d hd16 hlam_d
  rcases (existsLtB_eq_true_iff (2 ^ k) _).mp hb_in with ⟨sb, hsb, hcb_sb⟩
  rcases (existsLtB_eq_true_iff (2 ^ k) _).mp hd_in with ⟨sd, hsd, hcb_sd⟩
  simp only [decide_eq_true_eq] at hcb_sb hcb_sd
  -- Pick a bit `i < 4` where `(D_b D_d π(y)) mod 16` has bit `i = true`
  rcases exists_testBit_true_lt4 (π y ^^^ π (y ^^^ b) ^^^ π (y ^^^ d) ^^^ π (y ^^^ b ^^^ d)) hnonlin with ⟨i, hi4, hbit⟩
  -- Plug `x = 2^i < 16 ≤ 2^k` into `hvan sb _ sd _ (2^i + 2^k * y) _`!
  have hx_lt : 2 ^ i < 2 ^ k := Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) hi4) h16_le
  have hy_lt : y < 2 ^ k := Nat.lt_of_lt_of_le hy16 h16_le
  have hz_lt : 2 ^ i + 2 ^ k * y < 2 ^ (2 * k) := by
    rw [h2k_eq]
    have : 2 ^ k * y + 2 ^ k = 2 ^ k * (y + 1) := by rw [Nat.mul_succ]
    have hle : 2 ^ k * (y + 1) ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul_left (2 ^ k) hy_lt
    omega
  have hzero := hvan sb hsb sd hsd (2 ^ i + 2 ^ k * y) hz_lt
  rw [hcb_sb.1, hcb_sb.2, hcb_sd.1, hcb_sd.2] at hzero
  unfold secondDeriv at hzero
  have h1 : (2 ^ i + 2 ^ k * y) ^^^ (0 + 2 ^ k * b) = 2 ^ i + 2 ^ k * (y ^^^ b) := by
    rw [xor_add_pow2_mul k (2 ^ i) y 0 b hx_lt (Nat.two_pow_pos k), Nat.xor_zero]
  have h2 : (2 ^ i + 2 ^ k * y) ^^^ (0 + 2 ^ k * d) = 2 ^ i + 2 ^ k * (y ^^^ d) := by
    rw [xor_add_pow2_mul k (2 ^ i) y 0 d hx_lt (Nat.two_pow_pos k), Nat.xor_zero]
  have h3 : (2 ^ i + 2 ^ k * y) ^^^ (0 + 2 ^ k * b) ^^^ (0 + 2 ^ k * d) = 2 ^ i + 2 ^ k * (y ^^^ b ^^^ d) := by
    rw [h1, xor_add_pow2_mul k (2 ^ i) (y ^^^ b) 0 d hx_lt (Nat.two_pow_pos k), Nat.xor_zero]
  rw [h3, h2, h1, hcb (2 ^ i) y hx_lt, hcb (2 ^ i) (y ^^^ b) hx_lt,
      hcb (2 ^ i) (y ^^^ d) hx_lt, hcb (2 ^ i) (y ^^^ b ^^^ d) hx_lt] at hzero
  have hxne0 : 2 ^ i ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos i)
  simp only [hxne0, decide_false, Bool.xor_false] at hzero
  rw [innerParity_mod_pow2 k _ _ hx_lt, innerParity_mod_pow2 k _ _ hx_lt,
      innerParity_mod_pow2 k _ _ hx_lt, innerParity_mod_pow2 k _ _ hx_lt,
      ← innerParity_xor_right, ← innerParity_xor_right, ← innerParity_xor_right,
      ← Nat.xor_assoc, innerParity_two_pow] at hzero
  rw [hbit] at hzero
  cases hzero

/-! ## Section 5: Infinite Non-M# Bent Families, Carry-Dictionary Phase Transition,
    Sharpness Witnesses, Counterexamples, & Axiom Receipts -/

theorem tBijection_piMul3 : TBijection piMul3 := by
  have : piMul3 = fun y => (2 * 1 + 1) * y + 0 := by funext y; simp [piMul3]
  rw [this]; exact tBijection_odd_mul_add 1 0

theorem tBijection_piMul7 : TBijection piMul7 := by
  have : piMul7 = fun y => (2 * 3 + 1) * y + 0 := by funext y; simp [piMul7]
  rw [this]; exact tBijection_odd_mul_add 3 0

theorem tBijection_piKS : TBijection piKS :=
  tBijection_add_two_mul (causal_mul causal_id causal_id)

theorem tBijection_piARX : TBijection piARX :=
  tBijection_add_two_mul (causal_and causal_id (causal_two_mul causal_id))

theorem tBijection_piClmul3 : TBijection piClmul3 :=
  tBijection_xor_two_mul causal_id

/-- **Infinite Theorem 1 (`piMul3` — Carried Multiplication by 3):**
    For ALL `k ≥ 1`, `f_k(x, y) = <x, (3*y) mod 2^k> ⊕ [x = 0]` has exact flat Walsh spectrum `±2^k`,
    exact closed-form dual, and vanishing autocorrelation; and for ALL `k ≥ 4`, `f_k ∉ M#`! -/
theorem mul3_infinite_bent_and_nonMM (k : Nat) (hk : 4 ≤ k) :
    FlatWalsh k (carletTSign k 0 piMul3) ∧
    VanishingAutocorr (2 * k) (carletTSign k 0 piMul3) ∧
    ¬ HasVanishingSubspace k (carletTBool k 0 piMul3) :=
  ⟨(carletT_isBent tBijection_piMul3 k 0 (Nat.zero_le k)).flatWalsh,
   (carletT_isBent tBijection_piMul3 k 0 (Nat.zero_le k)).vanishingAutocorr,
   carletT0_not_hasVanishingSubspace certMul3 k hk⟩

/-- **Infinite Theorem 2 (`piKS` — Klimov-Shamir Quadratic Carry T-Function):**
    For ALL `k ≥ 4`, `f_k(x, y) = <x, (y + 2*y^2) mod 2^k> ⊕ [x = 0]` is bent with exact flat Walsh
    spectrum `±2^k`, vanishing autocorrelation, and strictly outside `M#`. -/
theorem ks_infinite_bent_and_nonMM (k : Nat) (hk : 4 ≤ k) :
    FlatWalsh k (carletTSign k 0 piKS) ∧
    VanishingAutocorr (2 * k) (carletTSign k 0 piKS) ∧
    ¬ HasVanishingSubspace k (carletTBool k 0 piKS) :=
  ⟨(carletT_isBent tBijection_piKS k 0 (Nat.zero_le k)).flatWalsh,
   (carletT_isBent tBijection_piKS k 0 (Nat.zero_le k)).vanishingAutocorr,
   carletT0_not_hasVanishingSubspace certKS k hk⟩

/-- **Infinite Theorem 3 (`piARX` — ARX Carry + Bitwise-AND T-Function):**
    For ALL `k ≥ 4`, `f_k(x, y) = <x, (y + 2*(y &&& 2*y)) mod 2^k> ⊕ [x = 0]` is bent with exact
    flat Walsh spectrum `±2^k`, vanishing autocorrelation, and strictly outside `M#`. -/
theorem arx_infinite_bent_and_nonMM (k : Nat) (hk : 4 ≤ k) :
    FlatWalsh k (carletTSign k 0 piARX) ∧
    VanishingAutocorr (2 * k) (carletTSign k 0 piARX) ∧
    ¬ HasVanishingSubspace k (carletTBool k 0 piARX) :=
  ⟨(carletT_isBent tBijection_piARX k 0 (Nat.zero_le k)).flatWalsh,
   (carletT_isBent tBijection_piARX k 0 (Nat.zero_le k)).vanishingAutocorr,
   carletT0_not_hasVanishingSubspace certARX k hk⟩

/-- **Infinite Theorem 4 (`piMul7` — Carried Multiplication by 7):**
    For ALL `k ≥ 4`, `f_k(x, y) = <x, (7*y) mod 2^k> ⊕ [x = 0]` is bent with exact flat Walsh
    spectrum `±2^k`, vanishing autocorrelation, and strictly outside `M#`. -/
theorem mul7_infinite_bent_and_nonMM (k : Nat) (hk : 4 ≤ k) :
    FlatWalsh k (carletTSign k 0 piMul7) ∧
    VanishingAutocorr (2 * k) (carletTSign k 0 piMul7) ∧
    ¬ HasVanishingSubspace k (carletTBool k 0 piMul7) :=
  ⟨(carletT_isBent tBijection_piMul7 k 0 (Nat.zero_le k)).flatWalsh,
   (carletT_isBent tBijection_piMul7 k 0 (Nat.zero_le k)).vanishingAutocorr,
   carletT0_not_hasVanishingSubspace certMul7 k hk⟩

/-! ### Carry-Dictionary Phase Transition & Sharpness Witnesses (Non-Vacuity Gate) -/

/-- **Carry-Dictionary Separation (Sharpness Theorem 1):**
    The carry-free twin `piClmul3 y = y ^^^ (2 * y)` yields a bent function for ALL `k ≥ 1`,
    AND stays INSIDE `M#` for ALL `k ≥ 1` via the explicit `k`-dim subspace `V = {(0, y)}`.
    Contrasted with `mul3_infinite_bent_and_nonMM`, the integer carry bit (`+` vs `^^^`) is the
    exact silicon switch that kicks the infinite family out of `M#`! -/
theorem clmul3_infinite_bent_and_inMM (k : Nat) :
    FlatWalsh k (carletTSign k 0 piClmul3) ∧
    VanishingAutocorr (2 * k) (carletTSign k 0 piClmul3) ∧
    HasVanishingSubspace k (carletTBool k 0 piClmul3) := by
  refine ⟨(carletT_isBent tBijection_piClmul3 k 0 (Nat.zero_le k)).flatWalsh,
          (carletT_isBent tBijection_piClmul3 k 0 (Nat.zero_le k)).vanishingAutocorr, ?_⟩
  refine ⟨{
    toX := fun _ => 0
    toY := fun s => s
    toX_lt := fun _ _ => Nat.two_pow_pos k
    toY_lt := fun _ hs => hs
    toX_xor := fun _ _ _ _ => rfl
    toY_xor := fun _ _ _ _ => rfl
    inj := fun _ _ _ _ _ hy => hy
  }, ?_⟩
  intro s hs t ht z _
  unfold secondDeriv carletTBool
  let x := z % 2 ^ k
  let y := z / 2 ^ k
  have hx : x < 2 ^ k := Nat.mod_lt z (Nat.two_pow_pos k)
  have hz_eq : z = x + 2 ^ k * y := by
    have := Nat.div_add_mod z (2 ^ k)
    change z = z % 2 ^ k + 2 ^ k * (z / 2 ^ k); omega
  have h1 : z ^^^ (0 + 2 ^ k * s) = x + 2 ^ k * (y ^^^ s) := by
    conv => lhs; rw [hz_eq]
    rw [xor_add_pow2_mul k x y 0 s hx (Nat.two_pow_pos k), Nat.xor_zero]
  have h2 : z ^^^ (0 + 2 ^ k * t) = x + 2 ^ k * (y ^^^ t) := by
    conv => lhs; rw [hz_eq]
    rw [xor_add_pow2_mul k x y 0 t hx (Nat.two_pow_pos k), Nat.xor_zero]
  have h3 : z ^^^ (0 + 2 ^ k * s) ^^^ (0 + 2 ^ k * t) = x + 2 ^ k * (y ^^^ s ^^^ t) := by
    rw [h1, xor_add_pow2_mul k x (y ^^^ s) 0 t hx (Nat.two_pow_pos k), Nat.xor_zero]
  have hdiv : ∀ v : Nat, (x + 2 ^ k * v) / 2 ^ k = v := fun v => by
    rw [Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt hx, Nat.add_zero]
  have hmod : ∀ v : Nat, (x + 2 ^ k * v) % 2 ^ k = x := fun v => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  rw [h3, h2, h1, hdiv, hdiv, hdiv, hmod, hmod, hmod]
  change xor (xor (xor (innerParity x (piClmul3 y % 2 ^ k)) (decide (x < 2 ^ 0 ∧ y % 2 ^ 0 = 0)))
                  (xor (innerParity x (piClmul3 (y ^^^ s) % 2 ^ k)) (decide (x < 2 ^ 0 ∧ (y ^^^ s) % 2 ^ 0 = 0))))
             (xor (xor (innerParity x (piClmul3 (y ^^^ t) % 2 ^ k)) (decide (x < 2 ^ 0 ∧ (y ^^^ t) % 2 ^ 0 = 0)))
                  (xor (innerParity x (piClmul3 (y ^^^ s ^^^ t) % 2 ^ k)) (decide (x < 2 ^ 0 ∧ (y ^^^ s ^^^ t) % 2 ^ 0 = 0)))) = false
  simp only [Nat.pow_zero, Nat.mod_one, and_true]
  rw [innerParity_mod_pow2 k x _ hx, innerParity_mod_pow2 k x _ hx,
      innerParity_mod_pow2 k x _ hx, innerParity_mod_pow2 k x _ hx]
  have hlin : piClmul3 y ^^^ piClmul3 (y ^^^ s) ^^^ piClmul3 (y ^^^ t) ^^^ piClmul3 (y ^^^ s ^^^ t) = 0 := by
    unfold piClmul3
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero =>
      simp only [Nat.testBit_xor, Nat.zero_testBit]
      have h2m : ∀ n : Nat, (2 * n).testBit 0 = false := fun n => by simp [Nat.testBit_zero]
      rw [h2m, h2m, h2m, h2m]
      cases y.testBit 0 <;> cases s.testBit 0 <;> cases t.testBit 0 <;> rfl
    | succ j =>
      simp only [Nat.testBit_xor, testBit_two_mul_succ, Nat.zero_testBit]
      cases y.testBit (j + 1) <;> cases s.testBit (j + 1) <;> cases t.testBit (j + 1) <;>
      cases y.testBit j <;> cases s.testBit j <;> cases t.testBit j <;> rfl
  have hpar : xor (xor (innerParity x (piClmul3 y)) (innerParity x (piClmul3 (y ^^^ s))))
                  (xor (innerParity x (piClmul3 (y ^^^ t))) (innerParity x (piClmul3 (y ^^^ s ^^^ t)))) = false := by
    rw [← innerParity_xor_right, ← innerParity_xor_right, ← innerParity_xor_right,
        ← Nat.xor_assoc, hlin, innerParity_zero_right]
  generalize decide (x < 1) = r
  have hr_cancel : ∀ p0 p1 p2 p3 : Bool,
      xor (xor (xor p0 r) (xor p1 r)) (xor (xor p2 r) (xor p3 r)) =
      xor (xor p0 p1) (xor p2 p3) := by
    intro p0 p1 p2 p3; cases p0 <;> cases p1 <;> cases p2 <;> cases p3 <;> cases r <;> rfl
  rw [hr_cancel, hpar]

/-- **Dimension-Threshold Sharpness Witness (`k = 3` vs `k ≥ 4`):**
    At `k = 3` (6 variables), `carletTBool 3 0 piMul3` DOES have an explicit 3-dimensional
    vanishing subspace `V = {(s &&& 1, s &&& 6) : s < 8}` (because the bit-3 carry of `3*y`
    overflows mod 8!). Hence `4 ≤ k` in `mul3_infinite_bent_and_nonMM` is **100% sharp**! -/
theorem mul3_k3_sharpness_inMM : HasVanishingSubspace 3 (carletTBool 3 0 piMul3) := by
  refine ⟨{
    toX := fun s => s &&& 1
    toY := fun s => s &&& 6
    toX_lt := fun s hs => by
      have : s < 8 := hs
      have h : s &&& 1 < 2 := Nat.and_lt_two_pow s (n := 1) (by omega)
      omega
    toY_lt := fun s hs => by
      have h : s &&& 6 < 8 := Nat.and_lt_two_pow s (n := 3) (by omega)
      exact h
    toX_xor := fun s t _ _ => by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and,
          Bool.and_xor_distrib_right]
    toY_xor := fun s t _ _ => by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and,
          Bool.and_xor_distrib_right]
    inj := fun s t hs ht hx hy => by
      apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 3
      · have h0 := congrArg (fun n => n.testBit 0) hx
        have h1 := congrArg (fun n => n.testBit 1) hy
        have h2 := congrArg (fun n => n.testBit 2) hy
        have hb1 : (6 : Nat).testBit 1 = true := rfl
        have hb2 : (6 : Nat).testBit 2 = true := rfl
        have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases this with rfl | rfl | rfl
        · simpa [Nat.testBit_and] using h0
        · simpa [Nat.testBit_and, hb1] using h1
        · simpa [Nat.testBit_and, hb2] using h2
      · have hle : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        rw [testBit_false_of_lt_pow2 s i (Nat.lt_of_lt_of_le hs hle),
            testBit_false_of_lt_pow2 t i (Nat.lt_of_lt_of_le ht hle)]
  }, ?_⟩
  have hdec : ∀ s : Fin 8, ∀ t : Fin 8, ∀ z : Fin 64,
      secondDeriv (carletTBool 3 0 piMul3) ((s.val &&& 1) + 8 * (s.val &&& 6))
        ((t.val &&& 1) + 8 * (t.val &&& 6)) z.val = false := by decide
  intro s hs t ht z hz
  exact hdec ⟨s, hs⟩ ⟨t, ht⟩ ⟨z, hz⟩

/-! ### Hypothesis-Breaking Sharpness Counterexamples (Kernel-Checked) -/

/-- Counterexample 1: Breaking `BitFlip` (`π(y) = 2*y`, even multiplier) destroys Walsh flatness
    and vanishing autocorrelation immediately at `k = 1` (`W = 4 ≠ ±2`, `Δ(1) = 4 ≠ 0`). -/
theorem counterexample_non_bijective_mul2 :
    ¬ FlatWalsh 1 (mmSign 1 (fun y => 2 * y) (fun _ => false)) ∧
    ¬ VanishingAutocorr 2 (mmSign 1 (fun y => 2 * y) (fun _ => false)) := by
  have hw0 : walsh 2 (mmSign 1 (fun y => 2 * y) (fun _ => false)) 0 = 4 := by decide
  have hxc1 : xcorr 2 (mmSign 1 (fun y => 2 * y) (fun _ => false))
                      (mmSign 1 (fun y => 2 * y) (fun _ => false)) 1 = 4 := by decide
  refine ⟨?_, ?_⟩
  · intro hflat
    have h0 := hflat 0 (by omega)
    rw [hw0] at h0; omega
  · intro ⟨_, hnz⟩
    have h1 := hnz 1 (by omega) (by omega)
    rw [hxc1] at h1; omega

/-- Counterexample 2: Breaking the 4-Quad dual-product law (`d0*d1*d2*d3 = +1` instead of `-1`)
    destroys Walsh flatness at `k = 1` (`W(0) = 4`, `W(1) = 0 ≠ ±2`). -/
theorem counterexample_quad_even_product :
    let f0 := fun _ : Nat => (1 : Int)
    ¬ FlatWalsh 1 (quadCombine f0 f0 f0 f0) := by
  intro f0 hflat
  have hw1 : walsh 2 (quadCombine f0 f0 f0 f0) 1 = 0 := by decide
  have h1 := hflat 1 (by omega)
  rw [hw1] at h1; omega

/-- Counterexample 3: Breaking `Causal` (`φ(y) = y / 2`, right-shift) causes
    `π(y) = y ^^^ (2 * (y / 2))` to collide mod 4 at `y = 0` and `y = 2` (not a bijection!). -/
theorem counterexample_non_causal_shift :
    let π := fun y => y ^^^ (2 * (y / 2))
    π 0 % 4 = π 2 % 4 ∧ (0 : Nat) ≠ 2 := by
  decide

theorem counterexample_non_causal_bitrev_carlet :
    ¬ FlatWalsh 2 (carletTSign 2 1 bitrev2) := by
  have hw0 : walsh 4 (carletTSign 2 1 bitrev2) 0 = 0 := by decide
  intro hflat
  have h0 := hflat 0 (by omega)
  rw [hw0] at h0; omega

/-! ### Non-Vacuity Witnesses (Every Universal Hypothesis Is Constructively Inhabited) -/

/-- Non-vacuity witness for Zero-Sum T-Quad Compiler (`φ1(y) = y*y`, `φ2(y) = y &&& (2*y)`). -/
theorem nonvacuity_zeroSum_tQuad (k : Nat) :
    let φ1 := fun y => y * y
    let φ2 := fun y => y &&& (2 * y)
    FlatWalsh (k + 1) (quadCombine
      (mmDualSign k (fun a => a) (fun _ => false))
      (mmDualSign k (fun a => a ^^^ (2 * φ1 a)) (fun _ => false))
      (mmDualSign k (fun a => a ^^^ (2 * φ2 a)) (fun _ => false))
      (mmDualSign k (fun a => a ^^^ (2 * (φ1 a ^^^ φ2 a))) (fun _ => true))) :=
  (zeroSum_tQuad_isBent (causal_mul causal_id causal_id)
    (causal_and causal_id (causal_two_mul causal_id)) k).flatWalsh

/-- Non-vacuity witness for Carlet-T with `π(0) ≠ 0` (`π(y) = 3*y + 1`, `r = 2 ≤ k`). -/
theorem nonvacuity_carletT_nonzero_pi0 (k : Nat) (hk : 2 ≤ k) :
    FlatWalsh k (carletTSign k 2 (fun y => 3 * y + 1)) ∧
    VanishingAutocorr (2 * k) (carletTSign k 2 (fun y => 3 * y + 1)) := by
  have hπ : TBijection (fun y => 3 * y + 1) := by
    have : (fun y => 3 * y + 1) = (fun y => (2 * 1 + 1) * y + 1) := rfl
    rw [this]; exact tBijection_odd_mul_add 1 1
  exact ⟨(carletT_isBent hπ k 2 hk).flatWalsh, (carletT_isBent hπ k 2 hk).vanishingAutocorr⟩

end SiliconBent
