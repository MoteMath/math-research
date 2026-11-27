import ZeckendorfBinaryCarryBridge.Defs

namespace CarryBridge
theorem testBit_zero_eq (n : Nat) : n.testBit 0 = (n % 2 == 1) := by
  simp [Nat.testBit, Nat.shiftRight_zero]

theorem testBit_succ_eq (n i : Nat) : n.testBit (i + 1) = (n / 2).testBit i := by
  rw [Nat.testBit_div_two]

theorem b2n_testBit_zero (n : Nat) : b2n (n.testBit 0) = n % 2 := by
  rw [testBit_zero_eq]
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [h, b2n]

theorem testBit_false_of_lt_two_pow {n k i : Nat} (hlt : n < 2 ^ k) (hi : k ≤ i) :
    n.testBit i = false := by
  have hlt' : n < 2 ^ i := Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hi)
  have hdiv : n >>> i = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hlt'
  simp [Nat.testBit, hdiv]

theorem exists_lt_two_pow (n : Nat) : ∃ N, n < 2 ^ N := by
  refine ⟨n, ?_⟩
  induction n with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

theorem sumNat_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i = g i) :
    sumNat n f = sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumNat]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sumNat_add (n : Nat) (f g : Nat → Nat) :
    sumNat n (fun i => f i + g i) = sumNat n f + sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumNat, ih]; omega

theorem sumNat_zero (n : Nat) : sumNat n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumNat, ih, Nat.add_zero]

theorem sumInt_congr {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) :
    sumInt n f = sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumInt]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sumInt_add (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i + g i) = sumInt n f + sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumInt, ih]; omega

theorem sumInt_sub (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i - g i) = sumInt n f - sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumInt, ih]; omega

theorem sumInt_zero (n : Nat) : sumInt n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumInt, ih, Int.add_zero]

theorem sumNat_succ_shift (n : Nat) (f : Nat → Nat) :
    sumNat (n + 1) f = f 0 + sumNat n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih =>
    simp only [sumNat] at ih ⊢
    omega

theorem sumNat_eq_of_zero_above {m n : Nat} (hmn : m ≤ n) (f : Nat → Nat)
    (hz : ∀ i, m ≤ i → i < n → f i = 0) : sumNat n f = sumNat m f := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this; rfl
  | succ k ih =>
    by_cases hmk : m = k + 1
    · subst hmk; rfl
    · have hle : m ≤ k := by omega
      simp only [sumNat, hz k hle (by omega), Nat.add_zero]
      exact ih hle (fun i h1 h2 => hz i h1 (by omega))

theorem sumInt_eq_of_zero_above {m n : Nat} (hmn : m ≤ n) (f : Nat → Int)
    (hz : ∀ i, m ≤ i → i < n → f i = 0) : sumInt n f = sumInt m f := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this; rfl
  | succ k ih =>
    by_cases hmk : m = k + 1
    · subst hmk; rfl
    · have hle : m ≤ k := by omega
      simp only [sumInt, hz k hle (by omega), Int.add_zero]
      exact ih hle (fun i h1 h2 => hz i h1 (by omega))

theorem popcount_zero : popcount 0 = 0 := by unfold popcount; simp

theorem popcount_eq (n : Nat) (hn : n ≠ 0) : popcount n = n % 2 + popcount (n / 2) := by
  conv => lhs; unfold popcount
  simp [hn]

theorem popcount_div_two_add (n : Nat) : popcount n = n % 2 + popcount (n / 2) := by
  by_cases h : n = 0
  · subst h; simp [popcount_zero]
  · exact popcount_eq n h

theorem popcount_one : popcount 1 = 1 := by
  rw [popcount_div_two_add]; simp [popcount_zero]

theorem popcount_mul_two (n : Nat) : popcount (2 * n) = popcount n := by
  rw [popcount_div_two_add]
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  rw [h1, h2, Nat.zero_add]

theorem popcount_shiftLeft (n k : Nat) : popcount (n <<< k) = popcount n := by
  rw [Nat.shiftLeft_eq]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (n * 2 ^ k) 2, popcount_mul_two, ih]

theorem popcount_eq_sumNat (n N : Nat) (hN : n < 2 ^ N) :
    popcount n = sumNat N (fun i => b2n (n.testBit i)) := by
  induction N generalizing n with
  | zero =>
    have : n = 0 := by simp at hN; omega
    subst this; simp [popcount_zero, sumNat]
  | succ k ih =>
    rw [sumNat_succ_shift, popcount_div_two_add, b2n_testBit_zero]
    have hdiv : n / 2 < 2 ^ k := by
      rw [Nat.pow_succ] at hN; omega
    rw [ih (n / 2) hdiv]
    congr 1
    apply sumNat_congr
    intro i _
    rw [testBit_succ_eq]

theorem popcount_add_low_high (m q r : Nat) (hm : m < 2 ^ r) :
    popcount (m + 2 ^ r * q) = popcount m + popcount q := by
  induction r generalizing m with
  | zero =>
    have : m = 0 := by simp at hm; omega
    subst this; simp [popcount_zero]
  | succ k ih =>
    rw [popcount_div_two_add (m + 2 ^ (k + 1) * q), popcount_div_two_add m]
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hmod : (m + 2 ^ (k + 1) * q) % 2 = m % 2 := by
      rw [hpow, Nat.mul_assoc]; omega
    have hdiv : (m + 2 ^ (k + 1) * q) / 2 = m / 2 + 2 ^ k * q := by
      rw [hpow, Nat.mul_assoc]; omega
    have hm' : m / 2 < 2 ^ k := by rw [hpow] at hm; omega
    rw [hmod, hdiv, ih (m / 2) hm']
    omega

theorem popcount_two_pow_sub_one (r : Nat) : popcount (2 ^ r - 1) = r := by
  induction r with
  | zero => simp [popcount_zero]
  | succ k ih =>
    have hpos : 2 ^ k ≥ 1 := Nat.one_le_two_pow
    have hpow : 2 ^ (k + 1) - 1 = 1 + 2 * (2 ^ k - 1) := by
      rw [Nat.pow_succ]; omega
    rw [hpow, popcount_div_two_add]
    have hmod : (1 + 2 * (2 ^ k - 1)) % 2 = 1 := by omega
    have hdiv : (1 + 2 * (2 ^ k - 1)) / 2 = 2 ^ k - 1 := by omega
    rw [hmod, hdiv, ih]
    omega

/-! ### 1.2 Fundamental Binary Addition & Kummer Carry-Count Theorem -/

theorem carryBitWith_succ_shift (a b : Nat) (c : Bool) (m : Nat) :
    carryBitWith (a / 2) (b / 2)
      ((a.testBit 0 && b.testBit 0) || (a.testBit 0 && c) || (b.testBit 0 && c)) m =
    carryBitWith a b c (m + 1) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp only [carryBitWith, ih, testBit_succ_eq]

theorem add_testBit_with_carry (a b : Nat) (c : Bool) (i : Nat) :
    (a + b + b2n c).testBit i = xor (xor (a.testBit i) (b.testBit i)) (carryBitWith a b c i) := by
  induction i generalizing a b c with
  | zero =>
    rw [testBit_zero_eq, testBit_zero_eq, testBit_zero_eq]
    simp only [carryBitWith]
    have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    cases c <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp [b2n, ha, hb, Nat.add_mod]
  | succ k ih =>
    let c' := (a.testBit 0 && b.testBit 0) || (a.testBit 0 && c) || (b.testBit 0 && c)
    have hdiv : (a + b + b2n c) / 2 = a / 2 + b / 2 + b2n c' := by
      have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
      dsimp only [c']
      rw [testBit_zero_eq a, testBit_zero_eq b]
      cases c <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
        simp [b2n, ha, hb] <;> omega
    rw [testBit_succ_eq, hdiv, testBit_succ_eq, testBit_succ_eq, ← carryBitWith_succ_shift]
    exact ih (a / 2) (b / 2) c'

theorem add_testBit_eq (a b i : Nat) :
    (a + b).testBit i = xor (xor (a.testBit i) (b.testBit i)) (carryBit a b i) := by
  have h := add_testBit_with_carry a b false i
  simpa [b2n, carryBit] using h

theorem carryInMask_testBit (a b i : Nat) :
    (carryInMask a b).testBit i = carryBit a b i := by
  unfold carryInMask
  rw [Nat.testBit_xor, Nat.testBit_xor, add_testBit_eq]
  cases a.testBit i <;> cases b.testBit i <;> cases carryBit a b i <;> rfl

theorem add_bit_conservation (a b i : Nat) :
    b2n (a.testBit i) + b2n (b.testBit i) + b2n (carryBit a b i) =
    b2n ((a + b).testBit i) + 2 * b2n (carryBit a b (i + 1)) := by
  rw [add_testBit_eq]
  simp only [carryBit, carryBitWith]
  cases a.testBit i <;> cases b.testBit i <;> cases carryBitWith a b false i <;> decide

theorem carryBit_eq_false_of_lt {a b N i : Nat} (ha : a < 2 ^ N) (hb : b < 2 ^ N) (hi : N + 1 ≤ i) :
    carryBit a b i = false := by
  rw [← carryInMask_testBit]
  apply testBit_false_of_lt_two_pow _ hi
  unfold carryInMask
  have hab : a + b < 2 ^ (N + 1) := by rw [Nat.pow_succ]; omega
  have ha' : a < 2 ^ (N + 1) := by rw [Nat.pow_succ]; omega
  have hb' : b < 2 ^ (N + 1) := by rw [Nat.pow_succ]; omega
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hab ha') hb'

/-- Kummer-Legendre Binary Carry-Count Identity:
    `popcount a + popcount b = popcount (a + b) + popcount (carryInMask a b)`. -/
theorem popcount_add_carry (a b : Nat) :
    popcount a + popcount b = popcount (a + b) + popcount (carryInMask a b) := by
  obtain ⟨Na, hNa⟩ := exists_lt_two_pow a
  obtain ⟨Nb, hNb⟩ := exists_lt_two_pow b
  let N := max Na Nb
  have ha : a < 2 ^ N := Nat.lt_of_lt_of_le hNa (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
  have hb : b < 2 ^ N := Nat.lt_of_lt_of_le hNb (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
  have hab : a + b < 2 ^ (N + 1) := by rw [Nat.pow_succ]; omega
  have ha1 : a < 2 ^ (N + 1) := by rw [Nat.pow_succ]; omega
  have hb1 : b < 2 ^ (N + 1) := by rw [Nat.pow_succ]; omega
  have hc1 : carryInMask a b < 2 ^ (N + 1) := by
    unfold carryInMask
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hab ha1) hb1
  rw [popcount_eq_sumNat a (N + 1) ha1,
      popcount_eq_sumNat b (N + 1) hb1,
      popcount_eq_sumNat (a + b) (N + 1) hab,
      popcount_eq_sumNat (carryInMask a b) (N + 1) hc1]
  have hsum : sumNat (N + 1) (fun i => b2n (a.testBit i) + b2n (b.testBit i) + b2n (carryBit a b i)) =
              sumNat (N + 1) (fun i => b2n ((a + b).testBit i) + 2 * b2n (carryBit a b (i + 1))) := by
    apply sumNat_congr
    intro i _
    exact add_bit_conservation a b i
  rw [sumNat_add, sumNat_add, sumNat_add] at hsum
  have h2 : sumNat (N + 1) (fun i => 2 * b2n (carryBit a b (i + 1))) =
            2 * sumNat (N + 1) (fun i => b2n (carryBit a b (i + 1))) := by
    clear hsum
    induction (N + 1) with
    | zero => rfl
    | succ k ih => simp only [sumNat, ih]; omega
  rw [h2] at hsum
  have hshift : sumNat (N + 1) (fun i => b2n (carryBit a b (i + 1))) =
                sumNat (N + 1) (fun i => b2n (carryBit a b i)) := by
    have h1 := sumNat_succ_shift (N + 1) (fun i => b2n (carryBit a b i))
    have h0 : b2n (carryBit a b 0) = 0 := rfl
    have htop : b2n (carryBit a b (N + 1)) = 0 := by
      rw [carryBit_eq_false_of_lt ha hb (Nat.le_refl _)]; rfl
    have hstep : sumNat (N + 2) (fun i => b2n (carryBit a b i)) =
                 sumNat (N + 1) (fun i => b2n (carryBit a b i)) + b2n (carryBit a b (N + 1)) := rfl
    rw [hstep, htop, Nat.add_zero] at h1
    rw [h0, Nat.zero_add] at h1
    exact h1.symm
  rw [hshift] at hsum
  have hc_eq : sumNat (N + 1) (fun i => b2n ((carryInMask a b).testBit i)) =
               sumNat (N + 1) (fun i => b2n (carryBit a b i)) := by
    apply sumNat_congr; intro i _; rw [carryInMask_testBit]
  rw [hc_eq]
  omega

/-! ### 1.3 `r`-Spaced Multiplication, Carryless Duality & Popcount Scaling -/

theorem isRSpaced_div_two {r d : Nat} (h : isRSpaced r d) : isRSpaced r (d / 2) := by
  intro i j hj1 hjr hi
  rw [← testBit_succ_eq] at hi ⊢
  have h1 := h (i + 1) j hj1 hjr hi
  have heq : i + j + 1 = i + 1 + j := by omega
  rw [heq]
  exact h1

theorem isRSpaced_div_two_pow {r d k : Nat} (h : isRSpaced r d) : isRSpaced r (d / 2 ^ k) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    exact isRSpaced_div_two ih

theorem isRSpaced_odd_decomp {r d : Nat} (hr : r ≥ 1) (hsp : isRSpaced r d) (hodd : d % 2 = 1) :
    d = 1 + 2 ^ r * (d / 2 ^ r) := by
  have hmod : d % 2 ^ r = 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < r
    · simp only [decide_eq_true hi, Bool.true_and]
      cases i with
      | zero => rw [testBit_zero_eq, hodd]; decide
      | succ k =>
        have hd0 : d.testBit 0 = true := by rw [testBit_zero_eq, hodd]; rfl
        have hfalse := hsp 0 (k + 1) (by omega) hi hd0
        simp only [Nat.zero_add] at hfalse
        have h1f : (1 : Nat).testBit (k + 1) = false :=
          testBit_false_of_lt_two_pow (show (1 : Nat) < 2 ^ 1 by decide) (by omega)
        rw [hfalse, h1f]
    · simp only [decide_eq_false hi, Bool.false_and]
      have h1 : (1 : Nat) < 2 ^ r := by
        have : 2 ^ 1 ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr
        omega
      exact (testBit_false_of_lt_two_pow h1 (by omega)).symm
  have hdiv := Nat.div_add_mod d (2 ^ r)
  omega

theorem clmul_zero_right (a : Nat) : clmul a 0 = 0 := by unfold clmul; simp

theorem clmul_mul_two_right (a b : Nat) : clmul a (2 * b) = 2 * clmul a b := by
  by_cases hb : b = 0
  · subst hb; simp [clmul_zero_right]
  · conv => lhs; unfold clmul
    have hne : 2 * b ≠ 0 := by omega
    have hmod : (2 * b) % 2 = 0 := by omega
    have hdiv : (2 * b) / 2 = b := by omega
    simp only [hne, ↓reduceIte, hmod, hdiv, Nat.shiftLeft_eq, Nat.pow_one]
    simp [Nat.mul_comm]

theorem clmul_two_pow_mul_right (a q m : Nat) : clmul a (2 ^ m * q) = 2 ^ m * clmul a q := by
  induction m with
  | zero => simp
  | succ m ihm =>
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, Nat.mul_assoc, clmul_mul_two_right, ihm, ← Nat.mul_assoc]

theorem clmul_add_two_pow (a q r : Nat) (hr : r ≥ 1) :
    clmul a (1 + 2 ^ r * q) = a ^^^ (2 ^ r * clmul a q) := by
  cases r with
  | zero => omega
  | succ k =>
    conv => lhs; unfold clmul
    have hne : 1 + 2 ^ (k + 1) * q ≠ 0 := by omega
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hmod : (1 + 2 ^ (k + 1) * q) % 2 = 1 := by rw [hpow, Nat.mul_assoc]; omega
    have hdiv : (1 + 2 ^ (k + 1) * q) / 2 = 2 ^ k * q := by rw [hpow, Nat.mul_assoc]; omega
    simp only [hne, ↓reduceIte, hmod, hdiv, clmul_two_pow_mul_right, Nat.shiftLeft_eq, Nat.pow_one]
    congr 1
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k * clmul a q) 2, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ k)]

theorem xor_eq_add_of_lt_two_pow (m q r : Nat) (hm : m < 2 ^ r) :
    m ^^^ (2 ^ r * q) = m + 2 ^ r * q := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  have hadd : (m + 2 ^ r * q).testBit i =
      if i < r then m.testBit i else q.testBit (i - r) := by
    have := Nat.testBit_two_pow_mul_add q hm i
    rw [Nat.add_comm] at this
    exact this
  rw [hadd]
  have hmul : (2 ^ r * q).testBit i = if i < r then false else q.testBit (i - r) := by
    have := Nat.testBit_two_pow_mul_add q (Nat.two_pow_pos r) i
    simpa using this
  rw [hmul]
  by_cases hi : i < r
  · simp [hi]
  · simp only [hi, ↓reduceIte]
    rw [testBit_false_of_lt_two_pow hm (by omega)]
    simp

/-- For any `r`-spaced `d` and `m < 2^r`, ordinary multiplication equals carryless `clmul`! -/
theorem mul_spaced_eq_clmul {r m d : Nat} (hr : r ≥ 1) (hm : m < 2 ^ r) (hsp : isRSpaced r d) :
    m * d = clmul m d := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hd0 : d = 0
    · subst hd0; simp [clmul_zero_right]
    · by_cases hpar : d % 2 = 0
      · have hd2 : d = 2 * (d / 2) := by omega
        have hlt : d / 2 < d := by omega
        have hsp' : isRSpaced r (d / 2) := isRSpaced_div_two hsp
        conv => lhs; rw [hd2, ← Nat.mul_assoc, Nat.mul_comm m 2, Nat.mul_assoc]
        conv => rhs; rw [hd2, clmul_mul_two_right]
        rw [ih (d / 2) hlt hsp']
      · have hodd : d % 2 = 1 := by omega
        have hdec : d = 1 + 2 ^ r * (d / 2 ^ r) := isRSpaced_odd_decomp hr hsp hodd
        have h2r : 2 ^ r ≥ 2 := by
          have := Nat.pow_le_pow_right (by omega : 2 ≥ 1) hr; omega
        have hlt : d / 2 ^ r < d := Nat.div_lt_self (by omega) h2r
        have hsp' : isRSpaced r (d / 2 ^ r) := isRSpaced_div_two_pow hsp
        conv => lhs; rw [hdec, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm m (2 ^ r), Nat.mul_assoc]
        conv => rhs; rw [hdec, clmul_add_two_pow m (d / 2 ^ r) r hr]
        rw [← ih (d / 2 ^ r) hlt hsp', xor_eq_add_of_lt_two_pow m (m * (d / 2 ^ r)) r hm]

/-- Exact popcount scaling for `r`-spaced `d` and `m < 2^r`: `popcount (m * d) = popcount m * popcount d`. -/
theorem popcount_mul_spaced {r m d : Nat} (hr : r ≥ 1) (hm : m < 2 ^ r) (hsp : isRSpaced r d) :
    popcount (m * d) = popcount m * popcount d := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hd0 : d = 0
    · subst hd0; simp [popcount_zero]
    · by_cases hpar : d % 2 = 0
      · have hd2 : d = 2 * (d / 2) := by omega
        have hlt : d / 2 < d := by omega
        have hsp' : isRSpaced r (d / 2) := isRSpaced_div_two hsp
        conv => lhs; rw [hd2, ← Nat.mul_assoc, Nat.mul_comm m 2, Nat.mul_assoc, popcount_mul_two]
        conv => rhs; rw [hd2, popcount_mul_two]
        exact ih (d / 2) hlt hsp'
      · have hodd : d % 2 = 1 := by omega
        have hdec : d = 1 + 2 ^ r * (d / 2 ^ r) := isRSpaced_odd_decomp hr hsp hodd
        have h2r : 2 ^ r ≥ 2 := by
          have := Nat.pow_le_pow_right (by omega : 2 ≥ 1) hr; omega
        have hlt : d / 2 ^ r < d := Nat.div_lt_self (by omega) h2r
        have hsp' : isRSpaced r (d / 2 ^ r) := isRSpaced_div_two_pow hsp
        have h1lt : 1 < 2 ^ r := by omega
        conv => lhs; rw [hdec, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm m (2 ^ r), Nat.mul_assoc,
                         popcount_add_low_high m (m * (d / 2 ^ r)) r hm]
        conv => rhs; rw [hdec, popcount_add_low_high 1 (d / 2 ^ r) r h1lt]
        rw [popcount_one, ih (d / 2 ^ r) hlt hsp', Nat.mul_add, Nat.mul_one]

/-- Exact bit formula for `m * d` when `d` is `r`-spaced and `m < 2^r`. -/
theorem mul_spaced_testBit_iff {r m d i : Nat} (hr : r ≥ 1) (hm : m < 2 ^ r) (hsp : isRSpaced r d) :
    (m * d).testBit i = true ↔ ∃ j, j < r ∧ j ≤ i ∧ m.testBit j = true ∧ d.testBit (i - j) = true := by
  induction d using Nat.strongRecOn generalizing i with
  | ind d ih =>
    by_cases hd0 : d = 0
    · subst hd0; simp
    · by_cases hpar : d % 2 = 0
      · have hd2 : d = 2 * (d / 2) := by omega
        have hlt : d / 2 < d := by omega
        have hsp' : isRSpaced r (d / 2) := isRSpaced_div_two hsp
        cases i with
        | zero =>
          have hmul : m * d = 2 * (m * (d / 2)) := by
            conv => lhs; rw [hd2]
            rw [← Nat.mul_assoc, Nat.mul_comm m 2, Nat.mul_assoc]
          rw [hmul, testBit_zero_eq]
          have hmod0 : (2 * (m * (d / 2))) % 2 = 0 := by omega
          rw [hmod0]
          constructor
          · intro h; simp at h
          · rintro ⟨j, _, hj0, _, hdj⟩
            have : j = 0 := by omega
            subst this
            rw [Nat.sub_zero, testBit_zero_eq, hpar] at hdj
            simp at hdj
        | succ k =>
          have hmul : m * d = 2 * (m * (d / 2)) := by
            conv => lhs; rw [hd2]
            rw [← Nat.mul_assoc, Nat.mul_comm m 2, Nat.mul_assoc]
          rw [hmul, testBit_succ_eq]
          have hdiv2 : (2 * (m * (d / 2))) / 2 = m * (d / 2) := by omega
          rw [hdiv2, ih (d / 2) hlt hsp']
          constructor
          · rintro ⟨j, hjr, hjk, hmj, hdk⟩
            refine ⟨j, hjr, by omega, hmj, ?_⟩
            have hsub : k + 1 - j = (k - j) + 1 := by omega
            rw [hsub, testBit_succ_eq]
            exact hdk
          · rintro ⟨j, hjr, hjk, hmj, hdk⟩
            by_cases hjeq : j = k + 1
            · subst hjeq
              rw [Nat.sub_self, testBit_zero_eq, hpar] at hdk
              simp at hdk
            · refine ⟨j, hjr, by omega, hmj, ?_⟩
              have hsub : k + 1 - j = (k - j) + 1 := by omega
              rw [hsub, testBit_succ_eq] at hdk
              exact hdk
      · have hodd : d % 2 = 1 := by omega
        have hdec : d = 1 + 2 ^ r * (d / 2 ^ r) := isRSpaced_odd_decomp hr hsp hodd
        have h2r : 2 ^ r ≥ 2 := by
          have := Nat.pow_le_pow_right (by omega : 2 ≥ 1) hr; omega
        have hlt : d / 2 ^ r < d := Nat.div_lt_self (by omega) h2r
        have hsp' : isRSpaced r (d / 2 ^ r) := isRSpaced_div_two_pow hsp
        have hmul : m * d = m + 2 ^ r * (m * (d / 2 ^ r)) := by
          conv => lhs; rw [hdec, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm m (2 ^ r), Nat.mul_assoc]
        rw [hmul]
        have htb := Nat.testBit_two_pow_mul_add (m * (d / 2 ^ r)) hm i
        rw [Nat.add_comm] at htb
        rw [htb]
        by_cases hir : i < r
        · simp only [hir, ↓reduceIte]
          constructor
          · intro hmi
            refine ⟨i, hir, Nat.le_refl _, hmi, ?_⟩
            rw [Nat.sub_self, testBit_zero_eq, hodd]; rfl
          · rintro ⟨j, _, hji, hmj, hdj⟩
            by_cases hjeq : j = i
            · subst hjeq; exact hmj
            · have hpos : 1 ≤ i - j := by omega
              have hlt' : i - j < r := by omega
              have hd0 : d.testBit 0 = true := by rw [testBit_zero_eq, hodd]; rfl
              have hfalse := hsp 0 (i - j) hpos hlt' hd0
              simp only [Nat.zero_add] at hfalse
              rw [hfalse] at hdj
              simp at hdj
        · simp only [hir, ↓reduceIte]
          rw [ih (d / 2 ^ r) hlt hsp']
          constructor
          · rintro ⟨j, hjr, hji, hmj, hdk⟩
            refine ⟨j, hjr, by omega, hmj, ?_⟩
            have h1lt : 1 < 2 ^ r := by omega
            have hdt := Nat.testBit_two_pow_mul_add (d / 2 ^ r) h1lt (i - j)
            rw [Nat.add_comm, ← hdec] at hdt
            rw [hdt]
            have hge : ¬ (i - j < r) := by omega
            simp only [hge, ↓reduceIte]
            have heq : i - j - r = i - r - j := by omega
            rw [heq]
            exact hdk
          · rintro ⟨j, hjr, _, hmj, hdj⟩
            have h1lt : 1 < 2 ^ r := by omega
            have hdt := Nat.testBit_two_pow_mul_add (d / 2 ^ r) h1lt (i - j)
            rw [Nat.add_comm, ← hdec] at hdt
            rw [hdt] at hdj
            by_cases hsub : i - j < r
            · simp only [hsub, ↓reduceIte] at hdj
              have hiz : i - j = 0 := by
                cases h : i - j with
                | zero => rfl
                | succ t =>
                  have h1f := testBit_false_of_lt_two_pow (show (1 : Nat) < 2 ^ 1 by decide) (show 1 ≤ t + 1 by omega)
                  rw [h, h1f] at hdj; simp at hdj
              omega
            · simp only [hsub, ↓reduceIte] at hdj
              refine ⟨j, hjr, by omega, hmj, ?_⟩
              have heq : i - r - j = i - j - r := by omega
              rw [heq]
              exact hdj

/-- Exact bit formula for `(2^(r+1) - 2) * d` when `d` is `r`-spaced. -/
theorem eigMask_mul_spaced_testBit_iff {r d i : Nat} (hr : r ≥ 1) (hsp : isRSpaced r d) :
    ((2 ^ (r + 1) - 2) * d).testBit i = true ↔
    ∃ m, 1 ≤ m ∧ m ≤ r ∧ m ≤ i ∧ d.testBit (i - m) = true := by
  have heq : (2 ^ (r + 1) - 2) * d = 2 * ((2 ^ r - 1) * d) := by
    have : 2 ^ r ≥ 1 := Nat.one_le_two_pow
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    have hsub : 2 ^ r * 2 - 2 = 2 * (2 ^ r - 1) := by omega
    rw [hsub, Nat.mul_assoc]
  rw [heq]
  have hm : 2 ^ r - 1 < 2 ^ r := by have := Nat.one_le_two_pow (n := r); omega
  cases i with
  | zero =>
    rw [testBit_zero_eq]
    have hmod : (2 * ((2 ^ r - 1) * d)) % 2 = 0 := by omega
    rw [hmod]
    constructor
    · intro h; simp at h
    · rintro ⟨m, hm1, _, hm0, _⟩; omega
  | succ k =>
    rw [testBit_succ_eq]
    have hdiv : (2 * ((2 ^ r - 1) * d)) / 2 = (2 ^ r - 1) * d := by omega
    rw [hdiv, mul_spaced_testBit_iff hr hm hsp]
    constructor
    · rintro ⟨j, hjr, hjk, _, hdj⟩
      refine ⟨j + 1, by omega, by omega, by omega, ?_⟩
      have hsub : k + 1 - (j + 1) = k - j := by omega
      rw [hsub]; exact hdj
    · rintro ⟨m, hm1, hmr, hmk, hdm⟩
      refine ⟨m - 1, by omega, by omega, ?_, ?_⟩
      · rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true (by omega)
      · have hsub : k - (m - 1) = k + 1 - m := by omega
        rw [hsub]; exact hdm

/-- Exact popcount of `(2^(r+1) - 2) * d` when `d` is `r`-spaced: `r * popcount d`. -/
theorem popcount_eigMask_mul_spaced {r d : Nat} (hr : r ≥ 1) (hsp : isRSpaced r d) :
    popcount ((2 ^ (r + 1) - 2) * d) = r * popcount d := by
  have heq : (2 ^ (r + 1) - 2) * d = 2 * ((2 ^ r - 1) * d) := by
    have : 2 ^ r ≥ 1 := Nat.one_le_two_pow
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    have hsub : 2 ^ r * 2 - 2 = 2 * (2 ^ r - 1) := by omega
    rw [hsub, Nat.mul_assoc]
  have hm : 2 ^ r - 1 < 2 ^ r := by have := Nat.one_le_two_pow (n := r); omega
  rw [heq, popcount_mul_two, popcount_mul_spaced hr hm hsp, popcount_two_pow_sub_one]

/-- Helper: XOR of `clmul a d` and `clmul b d` equals `clmul (a ^^^ b) d`. -/
theorem clmul_xor_left (a b d : Nat) : clmul (a ^^^ b) d = clmul a d ^^^ clmul b d := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hd0 : d = 0
    · subst hd0; simp [clmul_zero_right]
    · conv => lhs; unfold clmul
      conv => rhs; arg 1; unfold clmul
      conv => rhs; arg 2; unfold clmul
      simp only [hd0, ↓reduceIte]
      have hlt : d / 2 < d := by omega
      rw [ih (d / 2) hlt]
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hpar : d % 2 = 1
      · simp only [hpar, ↓reduceIte, Nat.testBit_xor, Nat.testBit_shiftLeft]
        by_cases hi : 1 ≤ i <;> simp [hi] <;>
          cases a.testBit i <;> cases b.testBit i <;>
          cases (clmul a (d / 2)).testBit (i - 1) <;> cases (clmul b (d / 2)).testBit (i - 1) <;> rfl
      · simp only [hpar, ↓reduceIte, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.zero_testBit,
                   Bool.false_xor]
        by_cases hi : 1 ≤ i <;> simp [hi]

theorem clmul_two_mul_left (a d : Nat) : clmul (2 * a) d = 2 * clmul a d := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hd0 : d = 0
    · subst hd0; simp [clmul_zero_right]
    · conv => lhs; unfold clmul
      conv => rhs; arg 2; unfold clmul
      simp only [hd0, ↓reduceIte]
      have hlt : d / 2 < d := by omega
      rw [ih (d / 2) hlt]
      apply Nat.eq_of_testBit_eq
      intro i
      have hsh : ∀ k, (2 * k) = k <<< 1 := fun k => by
        rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]
      by_cases hpar : d % 2 = 1
      · simp only [hpar, ↓reduceIte]
        rw [hsh a, hsh (clmul a (d / 2)), hsh (a ^^^ clmul a (d / 2) <<< 1)]
        simp only [Nat.testBit_shiftLeft]
        cases i <;> simp
      · simp only [hpar, ↓reduceIte, Nat.zero_xor]
        rw [hsh (clmul a (d / 2)), hsh (clmul a (d / 2) <<< 1)]

theorem add_bit_conservation_int (a b i : Nat) :
    b2i (a.testBit i) + b2i (b.testBit i) + b2i (carryBit a b i) =
    b2i ((a + b).testBit i) + 2 * b2i (carryBit a b (i + 1)) := by
  have h := add_bit_conservation a b i
  cases h1 : a.testBit i <;> cases h2 : b.testBit i <;> cases h3 : carryBit a b i <;>
  cases h4 : (a + b).testBit i <;> cases h5 : carryBit a b (i + 1) <;> simp_all

theorem sumInt_eq_zero {n : Nat} {f : Nat → Int} (h : ∀ i, i < n → f i = 0) :
    sumInt n f = 0 := by
  rw [sumInt_congr h, sumInt_zero]

theorem sumNat_eq_zero {n : Nat} {f : Nat → Nat} (h : ∀ i, i < n → f i = 0) :
    sumNat n f = 0 := by
  rw [sumNat_congr h, sumNat_zero]

/-! ## Section 2: Finite Recurrence Certificates & the (r+1)-State Carry-Bridge Transducer Engine -/

theorem RecCert.valid_r {c : RecCert} (h : c.isValid = true) : c.r ≥ 2 := by
  unfold isValid at h; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h; exact h.1.1

theorem RecCert.valid_odd {c : RecCert} (h : c.isValid = true) : c.maskS % 2 = 1 := by
  unfold isValid at h; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h; exact h.1.2

theorem RecCert.valid_lt {c : RecCert} (h : c.isValid = true) : c.maskS < 2 ^ c.r := by
  unfold isValid at h; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h; exact h.2

theorem RecCert.valid_bit0 {c : RecCert} (h : c.isValid = true) : c.maskS.testBit 0 = true := by
  rw [testBit_zero_eq, c.valid_odd h]; rfl

theorem RecCert.mS_lt {c : RecCert} (h : c.isValid = true) : c.mS < 2 ^ c.r := by
  unfold mS; have := c.valid_odd h; have := c.valid_lt h; omega

theorem RecCert.mS_odd {c : RecCert} (h : c.isValid = true) : c.mS % 2 = 1 := by
  unfold mS
  have hr := c.valid_r h; have hodd := c.valid_odd h; have hlt := c.valid_lt h
  have heven : 2 ^ c.r % 2 = 0 := by
    cases hreq : c.r with
    | zero => omega
    | succ k => rw [Nat.pow_succ]; omega
  omega

theorem RecCert.maskS_add_mS {c : RecCert} (h : c.isValid = true) : c.maskS + c.mS = 2 ^ c.r := by
  unfold mS; have := c.valid_lt h; omega

/-- Universal Two's-Complement Carry-In Identity: for ANY valid `RecCert c`,
    the binary carry-in bit of `maskS + mS = 2^r` is `decide (1 ≤ i ∧ i ≤ c.r)`, independent of `S`! -/
theorem RecCert.carryBit_maskS_mS {c : RecCert} (h : c.isValid = true) (i : Nat) :
    carryBit c.maskS c.mS i = decide (1 ≤ i ∧ i ≤ c.r) := by
  have hsum : c.maskS + c.mS = 2 ^ c.r := c.maskS_add_mS h
  have hr := c.valid_r h
  induction i with
  | zero => rfl
  | succ k ih =>
    have hcons := add_bit_conservation c.maskS c.mS k
    rw [hsum, ih] at hcons
    by_cases hk0 : k = 0
    · subst hk0
      have hm0 : c.maskS.testBit 0 = true := c.valid_bit0 h
      have hms0 : c.mS.testBit 0 = true := by rw [testBit_zero_eq, c.mS_odd h]; rfl
      have hp0 : (2 ^ c.r).testBit 0 = false := by
        rw [Nat.testBit_two_pow]; exact decide_eq_false (by omega)
      have hd0 : decide (1 ≤ 0 ∧ 0 ≤ c.r) = false := decide_eq_false (by omega)
      rw [hm0, hms0, hp0, hd0] at hcons
      cases hval : carryBit c.maskS c.mS 1
      · rw [hval] at hcons; simp at hcons
      · exact (decide_eq_true (by omega)).symm
    · by_cases hkr : k < c.r
      · have hp : (2 ^ c.r).testBit k = false := by
          rw [Nat.testBit_two_pow]; exact decide_eq_false (by omega)
        have hdec : decide (1 ≤ k ∧ k ≤ c.r) = true := decide_eq_true (by omega)
        rw [hp, hdec] at hcons
        cases hval : carryBit c.maskS c.mS (k + 1)
        · rw [hval] at hcons
          cases c.maskS.testBit k <;> cases c.mS.testBit k <;> simp at hcons
        · exact (decide_eq_true (by omega)).symm
      · have hm_f : c.maskS.testBit k = false := testBit_false_of_lt_two_pow (c.valid_lt h) (by omega)
        have hms_f : c.mS.testBit k = false := testBit_false_of_lt_two_pow (c.mS_lt h) (by omega)
        rw [hm_f, hms_f] at hcons
        by_cases hkeq : k = c.r
        · subst hkeq
          have hp : (2 ^ c.r).testBit c.r = true := by rw [Nat.testBit_two_pow]; simp
          have hdec : decide (1 ≤ c.r ∧ c.r ≤ c.r) = true := decide_eq_true (by omega)
          rw [hp, hdec] at hcons
          cases hval : carryBit c.maskS c.mS (c.r + 1)
          · exact (decide_eq_false (by omega)).symm
          · rw [hval] at hcons; simp at hcons
        · have hp : (2 ^ c.r).testBit k = false := by
            rw [Nat.testBit_two_pow]; exact decide_eq_false (by omega)
          have hdec : decide (1 ≤ k ∧ k ≤ c.r) = false := decide_eq_false (by omega)
          rw [hp, hdec] at hcons
          cases hval : carryBit c.maskS c.mS (k + 1)
          · exact (decide_eq_false (by omega)).symm
          · rw [hval] at hcons; simp at hcons

theorem eigMask_testBit (r i : Nat) :
    (2 ^ (r + 1) - 2).testBit i = decide (1 ≤ i ∧ i ≤ r) := by
  have heq : 2 ^ (r + 1) - 2 = 2 * (2 ^ r - 1) := by
    have : 2 ^ r ≥ 1 := Nat.one_le_two_pow
    rw [Nat.pow_succ]; omega
  rw [heq]
  cases i with
  | zero =>
    rw [testBit_zero_eq]
    have : (2 * (2 ^ r - 1)) % 2 = 0 := by omega
    simp [this]
  | succ k =>
    rw [testBit_succ_eq]
    have : (2 * (2 ^ r - 1)) / 2 = 2 ^ r - 1 := by omega
    rw [this, Nat.testBit_two_pow_sub_one]
    by_cases hk : k < r <;> simp [hk] <;> omega

theorem RecCert.carryInMask_maskS_mS {c : RecCert} (h : c.isValid = true) :
    carryInMask c.maskS c.mS = 2 ^ (c.r + 1) - 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [carryInMask_testBit, c.carryBit_maskS_mS h, eigMask_testBit]

theorem RecCert.popcount_mS {c : RecCert} (h : c.isValid = true) :
    popcount c.maskS + popcount c.mS = c.r + 1 := by
  have hk := popcount_add_carry c.maskS c.mS
  rw [c.maskS_add_mS h, c.carryInMask_maskS_mS h] at hk
  have hp2r : popcount (2 ^ c.r) = 1 := by
    have : 2 ^ c.r = 1 <<< c.r := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [this, popcount_shiftLeft, popcount_one]
  have hpeig : popcount (2 ^ (c.r + 1) - 2) = c.r := by
    have heq : 2 ^ (c.r + 1) - 2 = 2 * (2 ^ c.r - 1) := by
      have : 2 ^ c.r ≥ 1 := Nat.one_le_two_pow
      rw [Nat.pow_succ]; omega
    rw [heq, popcount_mul_two, popcount_two_pow_sub_one]
  rw [hp2r, hpeig] at hk
  omega

theorem RecCert.mS_xor_eigMask {c : RecCert} (h : c.isValid = true) :
    c.mS ^^^ (2 ^ (c.r + 1) - 2) = (2 ^ c.r) ^^^ c.maskS := by
  have hk := c.carryInMask_maskS_mS h
  unfold carryInMask at hk
  rw [c.maskS_add_mS h] at hk
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun n => n.testBit i) hk
  simp only [Nat.testBit_xor] at hi ⊢
  rw [← hi]
  cases (2 ^ c.r).testBit i <;> cases c.maskS.testBit i <;> cases c.mS.testBit i <;> rfl

theorem RecCert.bit_balance_local {c : RecCert} (h : c.isValid = true) (j : Nat) :
    b2i (c.mS.testBit j) + b2i ((2 ^ (c.r + 1) - 2).testBit j) -
      2 * b2i ((2 ^ (c.r + 1) - 2).testBit (j + 1)) =
    b2i ((2 ^ c.r).testBit j) - b2i (c.maskS.testBit j) := by
  have hcons := add_bit_conservation_int c.maskS c.mS j
  rw [c.maskS_add_mS h, ← carryInMask_testBit, ← carryInMask_testBit, c.carryInMask_maskS_mS h] at hcons
  omega

theorem RecCert.isDiffBasis_valid {c : RecCert} (h : c.isDiffBasis = true) : c.isValid = true := by
  unfold isDiffBasis at h; simp only [Bool.and_eq_true] at h; exact h.1

theorem RecCert.isDiffBasis_spec {c : RecCert} (h : c.isDiffBasis = true) :
    ∀ δ, 1 ≤ δ → δ < c.r →
      ∃ a b, a < c.r ∧ b < c.r ∧ c.maskS.testBit a = true ∧ c.maskS.testBit b = true ∧ a = b + δ := by
  unfold isDiffBasis at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne] at h
  have hvalid := h.1
  have hall := h.2
  intro δ hδ1 hδr
  have hne : (c.maskS &&& (c.maskS >>> δ)) ≠ 0 := by
    have hmem := hall (δ - 1) (by omega)
    have heq : δ - 1 + 1 = δ := by omega
    rw [heq] at hmem; exact hmem
  have hex : ∃ b, (c.maskS &&& (c.maskS >>> δ)).testBit b = true := by
    suffices ∀ n, n ≠ 0 → ∃ b, n.testBit b = true from this _ hne
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn0
      by_cases hpar : n % 2 = 1
      · exact ⟨0, by rw [testBit_zero_eq, hpar]; rfl⟩
      · obtain ⟨b, hb⟩ := ih (n / 2) (by omega) (by omega)
        exact ⟨b + 1, by rw [testBit_succ_eq]; exact hb⟩
  obtain ⟨b, hb⟩ := hex
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true] at hb
  have hb_lt : b < c.r := by
    by_cases hlt : b < c.r
    · exact hlt
    · have hf := testBit_false_of_lt_two_pow (c.valid_lt hvalid) (by omega : c.r ≤ b)
      rw [hf] at hb; simp at hb
  have ha_lt : b + δ < c.r := by
    by_cases hlt : b + δ < c.r
    · exact hlt
    · have hf := testBit_false_of_lt_two_pow (c.valid_lt hvalid) (by omega : c.r ≤ b + δ)
      rw [Nat.add_comm] at hb; rw [hf] at hb; simp at hb
  refine ⟨b + δ, b, ha_lt, hb_lt, ?_, hb.1, rfl⟩
  rw [Nat.add_comm] at hb; exact hb.2

/-! ### 2.2 The (r+1)-State Carry-Bridge Transducer Engine -/

theorem evalRecInt_zero (G : Nat → Int) : evalRecInt G 0 = 0 := by unfold evalRecInt; simp
theorem evalRecNat_zero (G : Nat → Nat) : evalRecNat G 0 = 0 := by unfold evalRecNat; simp

theorem evalRecInt_eq_sumInt (G : Nat → Int) (x N : Nat) (hN : x < 2 ^ N) :
    evalRecInt G x = sumInt N (fun i => b2i (x.testBit i) * G i) := by
  induction N generalizing G x with
  | zero =>
    have : x = 0 := by simp at hN; omega
    subst this; simp [evalRecInt_zero, sumInt]
  | succ k ih =>
    have hsum_shift : sumInt (k + 1) (fun i => b2i (x.testBit i) * G i) =
        b2i (x.testBit 0) * G 0 + sumInt k (fun i => b2i ((x / 2).testBit i) * G (i + 1)) := by
      clear ih hN
      induction k with
      | zero => simp [sumInt]
      | succ m ihm =>
        simp only [sumInt] at ihm ⊢
        rw [testBit_succ_eq]; omega
    rw [hsum_shift]
    by_cases hx0 : x = 0
    · subst hx0
      simp only [evalRecInt_zero, Nat.zero_testBit, b2i_false, Int.zero_mul, Int.zero_add, Nat.zero_div]
      exact (sumInt_eq_zero (fun i _ => by simp)).symm
    · conv => lhs; unfold evalRecInt
      simp only [hx0, ↓reduceIte]
      have hdiv : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hN; omega
      rw [ih (fun j => G (j + 1)) (x / 2) hdiv]
      have hbit0 : b2i (x.testBit 0) * G 0 = if x % 2 = 1 then G 0 else 0 := by
        rw [testBit_zero_eq]
        have h : x % 2 = 0 ∨ x % 2 = 1 := by omega
        rcases h with h | h <;> simp [h]
      rw [hbit0]

theorem evalRecNat_eq_sumNat (G : Nat → Nat) (x N : Nat) (hN : x < 2 ^ N) :
    evalRecNat G x = sumNat N (fun i => b2n (x.testBit i) * G i) := by
  induction N generalizing G x with
  | zero =>
    have : x = 0 := by simp at hN; omega
    subst this; simp [evalRecNat_zero, sumNat]
  | succ k ih =>
    rw [sumNat_succ_shift]
    by_cases hx0 : x = 0
    · subst hx0
      simp only [evalRecNat_zero, Nat.zero_testBit, b2n_false, Nat.zero_mul, Nat.zero_add]
      exact (sumNat_eq_zero (fun i _ => by simp)).symm
    · conv => lhs; unfold evalRecNat
      simp only [hx0, ↓reduceIte]
      have hdiv : x / 2 < 2 ^ k := by rw [Nat.pow_succ] at hN; omega
      rw [ih (fun j => G (j + 1)) (x / 2) hdiv]
      have hbit0 : b2n (x.testBit 0) * G 0 = if x % 2 = 1 then G 0 else 0 := by
        rw [testBit_zero_eq]
        have h : x % 2 = 0 ∨ x % 2 = 1 := by omega
        rcases h with h | h <;> simp [h]
      rw [hbit0]
      congr 1
      exact sumNat_congr (fun i _ => by rw [testBit_succ_eq])

/-! ### 2.3 Modular Transducer Invariant & Soundness Proofs -/

theorem transducerRun_prefix {c : RecCert} {x p d n k : Nat} {age : Fin (c.r + 1)}
    (hrun : transducerRun c x p d n = some age) (hk : k ≤ n) :
    ∃ agek, transducerRun c x p d k = some agek := by
  induction n generalizing age with
  | zero =>
    have : k = 0 := by omega
    subst this; exact ⟨age, hrun⟩
  | succ m ih =>
    by_cases hkeq : k = m + 1
    · subst hkeq; exact ⟨age, hrun⟩
    · simp only [transducerRun] at hrun
      cases hprev : transducerRun c x p d m with
      | none => rw [hprev] at hrun; simp at hrun
      | some agem => exact ih hprev (by omega)

theorem transducerStep_eq_some_iff (c : RecCert) (age age' : Fin (c.r + 1)) (xi pi di : Bool) :
    transducerStep c age xi pi di = some age' ↔
    (di && decide (age.val < c.r - 1)) = false ∧
    let ci : Bool := decide (age.val < c.r)
    let msd_i : Bool :=
      if di then c.mS.testBit 0
      else if age.val < c.r - 1 then c.mS.testBit (age.val + 1)
      else false
    let ageNext : Fin (c.r + 1) :=
      if di then ⟨0, Nat.zero_lt_succ c.r⟩
      else ⟨min (age.val + 1) c.r, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    let ciNext : Bool := decide (ageNext.val < c.r)
    b2n xi + b2n msd_i + b2n ci = b2n pi + 2 * b2n ciNext ∧ age' = ageNext := by
  unfold transducerStep
  by_cases hbad : (di && decide (age.val < c.r - 1)) = true
  · simp [hbad]
  · have hbadf : (di && decide (age.val < c.r - 1)) = false := Bool.eq_false_iff.mpr hbad
    simp only [hbadf, Bool.false_eq_true, ↓reduceIte, true_and]
    by_cases hchk :
        (b2n xi +
          b2n (if di = true then c.mS.testBit 0 else if age.val < c.r - 1 then c.mS.testBit (age.val + 1) else false) +
          b2n (decide (age.val < c.r))) =
        (b2n pi +
          2 * b2n (decide ((if di = true then (⟨0, Nat.zero_lt_succ c.r⟩ : Fin (c.r + 1))
                            else ⟨min (age.val + 1) c.r, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩).val < c.r)))
    · simp only [hchk, beq_self_eq_true, ↓reduceIte, Option.some.injEq, true_and, eq_comm]
    · have hbeqf :
          ((b2n xi +
            b2n (if di = true then c.mS.testBit 0 else if age.val < c.r - 1 then c.mS.testBit (age.val + 1) else false) +
            b2n (decide (age.val < c.r))) ==
          (b2n pi +
            2 * b2n (decide ((if di = true then (⟨0, Nat.zero_lt_succ c.r⟩ : Fin (c.r + 1))
                              else ⟨min (age.val + 1) c.r, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩).val < c.r)))) = false :=
        beq_false_of_ne hchk
      simp only [hbeqf, Bool.false_eq_true, ↓reduceIte]
      exact ⟨fun h => by simp at h, fun ⟨h, _⟩ => absurd h hchk⟩

theorem transducerRun_ageInv {c : RecCert} (hv : c.isValid = true) {x p d n : Nat}
    {age : Fin (c.r + 1)} (hrun : transducerRun c x p d n = some age) :
    AgeInv c.r d n age := by
  have hr := c.valid_r hv
  induction n generalizing age with
  | zero =>
    simp only [transducerRun, Option.some.injEq] at hrun
    subst hrun
    exact ⟨fun _ _ hi => by omega, fun h => by simp at h, fun _ _ _ ht => by omega⟩
  | succ k ih =>
    simp only [transducerRun] at hrun
    cases hprev : transducerRun c x p d k with
    | none => rw [hprev] at hrun; simp at hrun
    | some age0 =>
      rw [hprev] at hrun
      obtain ⟨hsp0, hlt0, heq0⟩ := ih hprev
      obtain ⟨hbadf, _, hage_eq_next⟩ := (transducerStep_eq_some_iff c age0 age (x.testBit k) (p.testBit k) (d.testBit k)).mp hrun
      subst hage_eq_next
      by_cases hdk : d.testBit k = true
      · simp only [hdk, ↓reduceIte]
        have hge : age0.val ≥ c.r - 1 := by
          by_cases h : age0.val < c.r - 1
          · simp [hdk, h] at hbadf
          · omega
        refine ⟨?_, ?_, ?_⟩
        · intro i j hi hj1 hjr hij hdi
          by_cases hij_lt : i + j < k
          · exact hsp0 i j (by omega) hj1 hjr hij_lt hdi
          · have hsum : i + j = k := by omega
            have ht : k - 1 - (j - 1) = i := by omega
            by_cases hage_eq : age0.val = c.r
            · have hf := heq0 hage_eq (j - 1) (by omega) (by omega)
              rw [ht, hdi] at hf; simp at hf
            · have hage_val : age0.val = c.r - 1 := by omega
              have ⟨_, _, hfalse⟩ := hlt0 (by omega)
              have hf := hfalse (j - 1) (by omega)
              rw [ht, hdi] at hf; simp at hf
        · intro _; refine ⟨by simp, ?_, fun t ht => by simp at ht⟩
          simpa using hdk
        · intro h; simp at h; omega
      · have hdkf : d.testBit k = false := Bool.eq_false_iff.mpr hdk
        simp only [hdkf, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · intro i j hi hj1 hjr hij hdi
          by_cases hij_lt : i + j < k
          · exact hsp0 i j (by omega) hj1 hjr hij_lt hdi
          · have : i + j = k := by omega
            rw [this]; exact hdkf
        · intro hmin
          simp only at hmin
          have hlt_a : age0.val + 1 < c.r := by omega
          have hmin_eq : min (age0.val + 1) c.r = age0.val + 1 := by omega
          obtain ⟨ha_lt, ha_bit, ha_zero⟩ := hlt0 (by omega)
          refine ⟨by simp [hmin_eq]; omega, ?_, ?_⟩
          · simp only [hmin_eq]
            have hidx : k + 1 - 1 - (age0.val + 1) = k - 1 - age0.val := by omega
            rw [hidx]; exact ha_bit
          · intro t ht
            simp only [hmin_eq] at ht
            cases t with
            | zero => simpa using hdkf
            | succ t' =>
              have hidx : k + 1 - 1 - (t' + 1) = k - 1 - t' := by omega
              rw [hidx]; exact ha_zero t' (by omega)
        · intro hmin t htr htk
          cases t with
          | zero => simpa using hdkf
          | succ t' =>
            have hidx : k + 1 - 1 - (t' + 1) = k - 1 - t' := by omega
            rw [hidx]
            have hage_ge : age0.val + 1 ≥ c.r := by simp at hmin; omega
            by_cases hage_eq : age0.val = c.r
            · exact heq0 hage_eq t' (by omega) (by omega)
            · have hage_val : age0.val = c.r - 1 := by
                have := age0.isLt; omega
              have ⟨_, _, hfalse⟩ := hlt0 (by omega)
              exact hfalse t' (by omega)

/-- Helper: `r`-spacing + `p = x + mS * d` + `carryInMask = (2^(r+1)-2) * d` implies exact pointwise
    bit-balance `p_i - x_i = d_{i-r} - ∑_{j ∈ S} d_{i-j}`. -/
theorem bit_balance_of_carry_eigenvalue {c : RecCert} (hv : c.isValid = true) {x p d : Nat}
    (hsp : isRSpaced c.r d) (hp : p = x + c.mS * d)
    (hcarry : carryInMask x (c.mS * d) = (2 ^ (c.r + 1) - 2) * d) (i : Nat) :
    b2i (p.testBit i) - b2i (x.testBit i) =
      (if i ≥ c.r then b2i (d.testBit (i - c.r)) else 0) -
      sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then b2i (d.testBit (i - j)) else 0) := by
  have hr := c.valid_r hv
  have hr1 : c.r ≥ 1 := by omega
  have hcons := add_bit_conservation_int x (c.mS * d) i
  rw [← hp, ← carryInMask_testBit, ← carryInMask_testBit, hcarry] at hcons
  -- Express `b2i ((c.mS * d).testBit i)` as `sumInt (c.r + 1) ...`
  have hms_sum : b2i ((c.mS * d).testBit i) =
      sumInt (c.r + 1) (fun j => if j ≤ i then b2i (c.mS.testBit j) * b2i (d.testBit (i - j)) else 0) := by
    have huniq : ∀ j1 j2, j1 < c.r → j2 < c.r → j1 ≤ i → j2 ≤ i →
        d.testBit (i - j1) = true → d.testBit (i - j2) = true → j1 = j2 := by
      intro j1 j2 h1 h2 hi1 hi2 hd1 hd2
      by_cases hlt : j1 < j2
      · have hf := hsp (i - j2) (j2 - j1) (by omega) (by omega) hd2
        have heq : i - j2 + (j2 - j1) = i - j1 := by omega
        rw [heq, hd1] at hf; simp at hf
      · by_cases hgt : j2 < j1
        · have hf := hsp (i - j1) (j1 - j2) (by omega) (by omega) hd1
          have heq : i - j1 + (j1 - j2) = i - j2 := by omega
          rw [heq, hd2] at hf; simp at hf
        · omega
    have htop : (if c.r ≤ i then b2i (c.mS.testBit c.r) * b2i (d.testBit (i - c.r)) else 0) = 0 := by
      rw [testBit_false_of_lt_two_pow (c.mS_lt hv) (Nat.le_refl _)]; simp
    simp only [sumInt, htop, Int.add_zero]
    by_cases hex : ∃ j, j < c.r ∧ j ≤ i ∧ c.mS.testBit j = true ∧ d.testBit (i - j) = true
    · rw [(mul_spaced_testBit_iff hr1 (c.mS_lt hv) hsp).mpr hex, b2i_true]
      obtain ⟨j0, hj0r, hj0i, hmj0, hdj0⟩ := hex
      suffices ∀ n, j0 < n → n ≤ c.r →
          sumInt n (fun j => if j ≤ i then b2i (c.mS.testBit j) * b2i (d.testBit (i - j)) else 0) = 1 from
        (this c.r hj0r (Nat.le_refl _)).symm
      intro n hjn hnr
      induction n with
      | zero => omega
      | succ k ihk =>
        simp only [sumInt]
        by_cases hjk : j0 = k
        · subst hjk
          have hz : sumInt j0 (fun j => if j ≤ i then b2i (c.mS.testBit j) * b2i (d.testBit (i - j)) else 0) = 0 := by
            apply sumInt_eq_zero; intro j hjl
            by_cases hji : j ≤ i
            · cases hd : d.testBit (i - j)
              · simp [hji]
              · have := huniq j j0 (by omega) hj0r hji hj0i hd hdj0; omega
            · simp [hji]
          rw [hz]; simp [hj0i, hmj0, hdj0]
        · rw [ihk (by omega) (by omega)]
          by_cases hki : k ≤ i
          · cases hd : d.testBit (i - k)
            · simp [hki]
            · have := huniq k j0 (by omega) hj0r hki hj0i hd hdj0; omega
          · simp [hki]
    · have hfalse : (c.mS * d).testBit i = false := by
        cases h : (c.mS * d).testBit i
        · rfl
        · exfalso; exact hex ((mul_spaced_testBit_iff hr1 (c.mS_lt hv) hsp).mp h)
      rw [hfalse, b2i_false]
      symm
      apply sumInt_eq_zero; intro j hjr
      by_cases hji : j ≤ i
      · cases hmj : c.mS.testBit j <;> cases hdj : d.testBit (i - j) <;> try (simp [hji]; done)
        exfalso; exact hex ⟨j, hjr, hji, hmj, hdj⟩
      · simp [hji]
  -- Express `b2i (((2^(r+1)-2) * d).testBit t)` as `sumInt (c.r + 1) ...`
  have heig_sum : ∀ t, b2i (((2 ^ (c.r + 1) - 2) * d).testBit t) =
      sumInt (c.r + 1) (fun j => if j ≤ t then b2i ((2 ^ (c.r + 1) - 2).testBit j) * b2i (d.testBit (t - j)) else 0) := by
    intro t
    have huniq : ∀ j1 j2, 1 ≤ j1 → j1 ≤ c.r → 1 ≤ j2 → j2 ≤ c.r → j1 ≤ t → j2 ≤ t →
        d.testBit (t - j1) = true → d.testBit (t - j2) = true → j1 = j2 := by
      intro j1 j2 h1l h1u h2l h2u ht1 ht2 hd1 hd2
      by_cases hlt : j1 < j2
      · have hf := hsp (t - j2) (j2 - j1) (by omega) (by omega) hd2
        have heq : t - j2 + (j2 - j1) = t - j1 := by omega
        rw [heq, hd1] at hf; simp at hf
      · by_cases hgt : j2 < j1
        · have hf := hsp (t - j1) (j1 - j2) (by omega) (by omega) hd1
          have heq : t - j1 + (j1 - j2) = t - j2 := by omega
          rw [heq, hd2] at hf; simp at hf
        · omega
    by_cases hex : ∃ m, 1 ≤ m ∧ m ≤ c.r ∧ m ≤ t ∧ d.testBit (t - m) = true
    · rw [(eigMask_mul_spaced_testBit_iff hr1 hsp).mpr hex, b2i_true]
      obtain ⟨m0, hm01, hm0r, hm0t, hdm0⟩ := hex
      suffices ∀ n, m0 < n → n ≤ c.r + 1 →
          sumInt n (fun j => if j ≤ t then b2i ((2 ^ (c.r + 1) - 2).testBit j) * b2i (d.testBit (t - j)) else 0) = 1 from
        (this (c.r + 1) (by omega) (Nat.le_refl _)).symm
      intro n hmn hnr
      induction n with
      | zero => omega
      | succ k ihk =>
        simp only [sumInt]
        by_cases hmk : m0 = k
        · subst hmk
          have hz : sumInt m0 (fun j => if j ≤ t then b2i ((2 ^ (c.r + 1) - 2).testBit j) * b2i (d.testBit (t - j)) else 0) = 0 := by
            apply sumInt_eq_zero; intro j hjl
            by_cases hjt : j ≤ t
            · simp only [hjt, ↓reduceIte, eigMask_testBit]
              by_cases hj1 : 1 ≤ j
              · cases hd : d.testBit (t - j)
                · simp
                · have := huniq j m0 hj1 (by omega) hm01 hm0r hjt hm0t hd hdm0; omega
              · simp [decide_eq_false (by omega : ¬(1 ≤ j ∧ j ≤ c.r))]
            · simp [hjt]
          rw [hz, eigMask_testBit]; simp [hm0t, decide_eq_true (by omega : 1 ≤ m0 ∧ m0 ≤ c.r), hdm0]
        · rw [ihk (by omega) (by omega)]
          by_cases hkt : k ≤ t
          · simp only [hkt, ↓reduceIte, eigMask_testBit]
            by_cases hk1 : 1 ≤ k
            · cases hd : d.testBit (t - k)
              · simp
              · have := huniq k m0 hk1 (by omega) hm01 hm0r hkt hm0t hd hdm0; omega
            · simp [decide_eq_false (by omega : ¬(1 ≤ k ∧ k ≤ c.r))]
          · simp [hkt]
    · have hfalse : ((2 ^ (c.r + 1) - 2) * d).testBit t = false := by
        cases h : ((2 ^ (c.r + 1) - 2) * d).testBit t
        · rfl
        · exfalso; exact hex ((eigMask_mul_spaced_testBit_iff hr1 hsp).mp h)
      rw [hfalse, b2i_false]
      symm
      apply sumInt_eq_zero; intro j hjr
      by_cases hjt : j ≤ t
      · simp only [hjt, ↓reduceIte, eigMask_testBit]
        by_cases hj1 : 1 ≤ j
        · cases hdj : d.testBit (t - j)
          · simp
          · exfalso; exact hex ⟨j, hj1, by omega, hjt, hdj⟩
        · simp [decide_eq_false (by omega : ¬(1 ≤ j ∧ j ≤ c.r))]
      · simp [hjt]
  -- Reindex `heig_sum (i + 1)`
  have heig_succ : b2i (((2 ^ (c.r + 1) - 2) * d).testBit (i + 1)) =
      sumInt (c.r + 1) (fun j => if j ≤ i then b2i ((2 ^ (c.r + 1) - 2).testBit (j + 1)) * b2i (d.testBit (i - j)) else 0) := by
    rw [heig_sum (i + 1)]
    have hshift : ∀ n (f : Nat → Int), sumInt (n + 1) f = f 0 + sumInt n (fun j => f (j + 1)) := by
      intro n f; induction n with | zero => simp [sumInt] | succ k ihk => simp only [sumInt] at ihk ⊢; omega
    rw [hshift c.r]
    have h0 : (2 ^ (c.r + 1) - 2).testBit 0 = false := by rw [eigMask_testBit]; rfl
    have htop : (2 ^ (c.r + 1) - 2).testBit (c.r + 1) = false := by
      rw [eigMask_testBit]; exact decide_eq_false (by omega)
    simp only [h0, b2i_false, Int.zero_mul, ite_self, Int.zero_add]
    have htop_term : (if c.r ≤ i then b2i ((2 ^ (c.r + 1) - 2).testBit (c.r + 1)) * b2i (d.testBit (i - c.r)) else 0) = 0 := by
      simp [htop]
    simp only [sumInt, htop_term, Int.add_zero]
    apply sumInt_congr; intro j _
    by_cases hji : j ≤ i
    · have h1 : j + 1 ≤ i + 1 := by omega
      have h2 : i + 1 - (j + 1) = i - j := by omega
      simp [hji, h1, h2]
    · have h1 : ¬(j + 1 ≤ i + 1) := by omega
      simp [hji, h1]
  have hpi_xi : b2i (p.testBit i) - b2i (x.testBit i) =
      b2i ((c.mS * d).testBit i) + b2i (((2 ^ (c.r + 1) - 2) * d).testBit i) -
      2 * b2i (((2 ^ (c.r + 1) - 2) * d).testBit (i + 1)) := by omega
  rw [hpi_xi, hms_sum, heig_sum i, heig_succ]
  have hmul2 : ∀ n (f : Nat → Int), 2 * sumInt n f = sumInt n (fun j => 2 * f j) := by
    intro n f; induction n with | zero => rfl | succ k ihk => simp only [sumInt]; omega
  rw [hmul2, ← sumInt_add, ← sumInt_sub]
  have hcomb : sumInt (c.r + 1) (fun j =>
      (if j ≤ i then b2i (c.mS.testBit j) * b2i (d.testBit (i - j)) else 0) +
      (if j ≤ i then b2i ((2 ^ (c.r + 1) - 2).testBit j) * b2i (d.testBit (i - j)) else 0) -
      2 * (if j ≤ i then b2i ((2 ^ (c.r + 1) - 2).testBit (j + 1)) * b2i (d.testBit (i - j)) else 0)) =
    sumInt (c.r + 1) (fun j =>
      if j ≤ i then (b2i ((2 ^ c.r).testBit j) - b2i (c.maskS.testBit j)) * b2i (d.testBit (i - j)) else 0) := by
    apply sumInt_congr; intro j _
    by_cases hji : j ≤ i
    · simp only [hji, ↓reduceIte]
      have hloc := c.bit_balance_local hv j
      cases d.testBit (i - j) <;> simp at hloc ⊢ <;> omega
    · simp [hji]
  rw [hcomb]
  simp only [sumInt]
  have htop_r : (if c.r ≤ i then (b2i ((2 ^ c.r).testBit c.r) - b2i (c.maskS.testBit c.r)) * b2i (d.testBit (i - c.r)) else 0) =
      (if i ≥ c.r then b2i (d.testBit (i - c.r)) else 0) := by
    have h1 : (2 ^ c.r).testBit c.r = true := by rw [Nat.testBit_two_pow]; simp
    have h2 : c.maskS.testBit c.r = false := testBit_false_of_lt_two_pow (c.valid_lt hv) (Nat.le_refl _)
    by_cases hri : c.r ≤ i <;> simp [hri, h1, h2]
  rw [htop_r]
  have hlow : sumInt c.r (fun j =>
      if j ≤ i then (b2i ((2 ^ c.r).testBit j) - b2i (c.maskS.testBit j)) * b2i (d.testBit (i - j)) else 0) =
    -(sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then b2i (d.testBit (i - j)) else 0)) := by
    have hneg : ∀ n (f : Nat → Int), sumInt n (fun j => -(f j)) = -(sumInt n f) := by
      intro n f; induction n with | zero => rfl | succ k ihk => simp only [sumInt, ihk]; omega
    rw [← hneg]
    apply sumInt_congr; intro j hjr
    have h2f : (2 ^ c.r).testBit j = false := by
      rw [Nat.testBit_two_pow]; exact decide_eq_false (by omega)
    by_cases hji : j ≤ i <;> cases hmj : c.maskS.testBit j <;> simp [hji, h2f]
  rw [hlow]; omega

/-- Helper: pointwise bit-balance telescopes to `evalRecInt G p = evalRecInt G x` for ANY `G` obeying `c`. -/
theorem evalRecInt_of_bit_balance {c : RecCert} {x p d : Nat}
    (hbal : ∀ i, b2i (p.testBit i) - b2i (x.testBit i) =
      (if i ≥ c.r then b2i (d.testBit (i - c.r)) else 0) -
      sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then b2i (d.testBit (i - j)) else 0))
    (G : Nat → Int) (hG : ObeysRecInt c G) :
    evalRecInt G p = evalRecInt G x := by
  obtain ⟨Nx, hNx⟩ := exists_lt_two_pow x
  obtain ⟨Np, hNp⟩ := exists_lt_two_pow p
  obtain ⟨Nd, hNd⟩ := exists_lt_two_pow d
  let N := max Nx (max Np Nd)
  have hxN : x < 2 ^ N := Nat.lt_of_lt_of_le hNx (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
  have hpN : p < 2 ^ N := Nat.lt_of_lt_of_le hNp (Nat.pow_le_pow_right (by omega)
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
  have hdN : d < 2 ^ N := Nat.lt_of_lt_of_le hNd (Nat.pow_le_pow_right (by omega)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
  let W := N + c.r + 1
  have hxW : x < 2 ^ W := Nat.lt_of_lt_of_le hxN (Nat.pow_le_pow_right (by omega) (by omega))
  have hpW : p < 2 ^ W := Nat.lt_of_lt_of_le hpN (Nat.pow_le_pow_right (by omega) (by omega))
  rw [evalRecInt_eq_sumInt G p W hpW, evalRecInt_eq_sumInt G x W hxW]
  suffices hdiff : sumInt W (fun i => (b2i (p.testBit i) - b2i (x.testBit i)) * G i) = 0 by
    have hsplit : sumInt W (fun i => (b2i (p.testBit i) - b2i (x.testBit i)) * G i) =
                  sumInt W (fun i => b2i (p.testBit i) * G i) -
                  sumInt W (fun i => b2i (x.testBit i) * G i) := by
      rw [← sumInt_sub]; exact sumInt_congr (fun i _ => Int.sub_mul _ _ _)
    rw [hsplit] at hdiff; omega
  have h1 : sumInt W (fun i => (b2i (p.testBit i) - b2i (x.testBit i)) * G i) =
      sumInt W (fun i => if i ≥ c.r then b2i (d.testBit (i - c.r)) * G i else 0) -
      sumInt W (fun i => sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then b2i (d.testBit (i - j)) * G i else 0)) := by
    rw [← sumInt_sub]
    apply sumInt_congr; intro i _
    rw [hbal i, Int.sub_mul]
    congr 1
    · by_cases hri : i ≥ c.r <;> simp [hri]
    · clear hbal
      induction c.r with
      | zero => simp [sumInt]
      | succ m ihm =>
        simp only [sumInt, Int.add_mul, ihm]
        congr 1
        by_cases hb : (c.maskS.testBit m && decide (m ≤ i)) = true <;> simp [hb]
  rw [h1]
  have hshift_gen : ∀ s M (f : Nat → Int),
      sumInt (M + s) (fun i => if s ≤ i then f (i - s) else 0) = sumInt M f := by
    intro s M f
    induction M with
    | zero =>
      simp only [Nat.zero_add]
      exact sumInt_eq_zero (fun i hi => by simp [show ¬(s ≤ i) by omega])
    | succ m ihm =>
      have heq : m + 1 + s = (m + s) + 1 := by omega
      rw [heq, sumInt, ihm]
      simp [show s ≤ m + s by omega, show m + s - s = m by omega, sumInt]
  have hterm1 : sumInt W (fun i => if i ≥ c.r then b2i (d.testBit (i - c.r)) * G i else 0) =
      sumInt N (fun k => b2i (d.testBit k) * G (k + c.r)) := by
    have hW_eq : W = (N + 1) + c.r := by omega
    have hrew : sumInt W (fun i => if i ≥ c.r then b2i (d.testBit (i - c.r)) * G i else 0) =
        sumInt ((N + 1) + c.r) (fun i => if c.r ≤ i then b2i (d.testBit (i - c.r)) * G (i - c.r + c.r) else 0) := by
      rw [hW_eq]
      apply sumInt_congr; intro i _
      by_cases hri : c.r ≤ i
      · have hsub : i - c.r + c.r = i := by omega
        simp [hri, hsub]
      · simp [hri]
    rw [hrew, hshift_gen c.r (N + 1) (fun k => b2i (d.testBit k) * G (k + c.r))]
    simp only [sumInt, testBit_false_of_lt_two_pow hdN (Nat.le_refl _), b2i_false, Int.zero_mul, Int.add_zero]
  have hswap : ∀ M R (F : Nat → Nat → Int),
      sumInt M (fun i => sumInt R (fun j => F i j)) =
      sumInt R (fun j => sumInt M (fun i => F i j)) := by
    intro M R F
    induction M with
    | zero =>
      simp only [sumInt]; exact (sumInt_eq_zero (fun _ _ => rfl)).symm
    | succ m ihm => simp only [sumInt, ihm, ← sumInt_add]
  have hterm2 :
      sumInt W (fun i => sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then b2i (d.testBit (i - j)) * G i else 0)) =
      sumInt N (fun k => b2i (d.testBit k) * sumInt c.r (fun j => if c.maskS.testBit j then G (k + j) else 0)) := by
    rw [hswap W c.r]
    have hinner : ∀ j, j < c.r →
        sumInt W (fun i => if c.maskS.testBit j && decide (j ≤ i) then b2i (d.testBit (i - j)) * G i else 0) =
        sumInt N (fun k => if c.maskS.testBit j then b2i (d.testBit k) * G (k + j) else 0) := by
      intro j hjr
      by_cases hmj : c.maskS.testBit j = true
      · simp only [hmj, Bool.true_and, decide_eq_true_eq, ↓reduceIte]
        have hW_split : W = (W - j) + j := by omega
        have hrew : sumInt W (fun i => if j ≤ i then b2i (d.testBit (i - j)) * G i else 0) =
            sumInt ((W - j) + j) (fun i => if j ≤ i then b2i (d.testBit (i - j)) * G (i - j + j) else 0) := by
          conv => lhs; rw [hW_split]
          apply sumInt_congr; intro i _
          by_cases hji : j ≤ i
          · have hsub : i - j + j = i := by omega
            simp [hji, hsub]
          · simp [hji]
        rw [hrew, hshift_gen j (W - j) (fun k => b2i (d.testBit k) * G (k + j))]
        apply sumInt_eq_of_zero_above (by omega : N ≤ W - j)
        intro k hkN _
        rw [testBit_false_of_lt_two_pow hdN hkN]; simp
      · have hmjf : c.maskS.testBit j = false := Bool.eq_false_iff.mpr hmj
        simp only [hmjf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [sumInt_zero, sumInt_zero]
    rw [sumInt_congr hinner, ← hswap N c.r]
    apply sumInt_congr; intro k _
    clear hinner hswap hterm1 h1
    induction c.r with
    | zero => simp [sumInt]
    | succ m ihm =>
      simp only [sumInt, Int.mul_add, ihm]
      congr 1
      by_cases hmj : c.maskS.testBit m = true <;> simp [hmj]
  rw [hterm1, hterm2, ← sumInt_sub]
  apply sumInt_eq_zero; intro k _
  rw [← Int.mul_sub, hG k, Int.sub_self, Int.mul_zero]

/-- **REUSABLE FINITE-STATE CARRY-BRIDGE TRANSDUCER SOUNDNESS ENGINE.**
    Any triple `(x, p, d)` accepted by the `(r+1)`-state Carry-Bridge Transducer for a valid
    finite recurrence certificate `c : RecCert` simultaneously satisfies ALL SIX infinite laws. -/
theorem transducer_sound {c : RecCert} (hv : c.isValid = true) {x p d : Nat}
    (hacc : TransducerAccepts c x p d) :
    isRSpaced c.r d ∧
    p = x + c.mS * d ∧
    carryInMask x (c.mS * d) = (2 ^ (c.r + 1) - 2) * d ∧
    p ^^^ x = clmul ((2 ^ c.r) ^^^ c.maskS) d ∧
    popcount x = popcount p + (popcount c.maskS - 1) * popcount d ∧
    popcount (carryInMask x (c.mS * d)) = c.r * popcount d ∧
    (∀ G, ObeysRecInt c G → evalRecInt G p = evalRecInt G x) := by
  have hr := c.valid_r hv
  have hr1 : c.r ≥ 1 := by omega
  obtain ⟨N, hxN, hpN, hdN, hrun⟩ := hacc
  let W := N + c.r + 1
  have hinvW := transducerRun_ageInv hv hrun
  -- 1. Global `r`-spacing
  have hsp : isRSpaced c.r d := by
    intro i j hj1 hjr hdi
    have hiN : i < N := by
      by_cases hlt : i < N
      · exact hlt
      · have hf := testBit_false_of_lt_two_pow hdN (show N ≤ i by omega)
        rw [hf] at hdi; simp at hdi
    exact hinvW.1 i j (by omega) hj1 hjr (by omega) hdi
  -- 2. Bit-slice induction: carry & sum agreement up to `W`
  have hstep_inv : ∀ k, k ≤ W →
      ∃ agek, transducerRun c x p d k = some agek ∧
        carryBit x (c.mS * d) k = decide (agek.val < c.r) ∧
        (∀ i, i < k → (x + c.mS * d).testBit i = p.testBit i) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨⟨c.r, Nat.lt_succ_self c.r⟩, rfl, ?_, fun i hi => by omega⟩
      simp [carryBit, carryBitWith]
    | succ m ihm =>
      obtain ⟨agem, hrm, hcm, hpm⟩ := ihm (by omega)
      obtain ⟨agem1, hrm1⟩ := transducerRun_prefix hrun hk
      have hstep : transducerStep c agem (x.testBit m) (p.testBit m) (d.testBit m) = some agem1 := by
        simp only [transducerRun, hrm] at hrm1; exact hrm1
      have hinvm := transducerRun_ageInv hv hrm
      have hmsd_eq :
          (if d.testBit m then c.mS.testBit 0
           else if agem.val < c.r - 1 then c.mS.testBit (agem.val + 1)
           else false) = (c.mS * d).testBit m := by
        apply Bool.eq_iff_iff.mpr
        rw [mul_spaced_testBit_iff hr1 (c.mS_lt hv) hsp]
        by_cases hdm : d.testBit m = true
        · simp only [hdm, ↓reduceIte]
          constructor
          · intro hm0; exact ⟨0, by omega, Nat.zero_le m, hm0, by simpa using hdm⟩
          · rintro ⟨j, hjr, hjm, hmj, hdj⟩
            by_cases hj0 : j = 0
            · subst hj0; exact hmj
            · have hf := hsp (m - j) j (by omega) hjr hdj
              have hadd : m - j + j = m := by omega
              rw [hadd, hdm] at hf; simp at hf
        · have hdmf : d.testBit m = false := by cases h : d.testBit m <;> simp_all
          simp only [hdmf, Bool.false_eq_true, ↓reduceIte]
          by_cases hag : agem.val < c.r - 1
          · simp only [hag, ↓reduceIte]
            obtain ⟨ha_lt, ha_bit, ha_zero⟩ := hinvm.2.1 (by omega)
            constructor
            · intro hmj
              refine ⟨agem.val + 1, by omega, by omega, hmj, ?_⟩
              have hidx : m - (agem.val + 1) = m - 1 - agem.val := by omega
              rw [hidx]; exact ha_bit
            · rintro ⟨j, hjr, hjm, hmj, hdj⟩
              by_cases hj0 : j = 0
              · subst hj0; simp [hdmf] at hdj
              · have hjeq : j = agem.val + 1 := by
                  by_cases hltj : j - 1 < agem.val
                  · have hf := ha_zero (j - 1) hltj
                    have hidx : m - 1 - (j - 1) = m - j := by omega
                    rw [hidx, hdj] at hf; simp at hf
                  · by_cases hgtj : agem.val < j - 1
                    · have hf := hsp (m - j) ((j - 1) - agem.val) (by omega) (by omega) hdj
                      have hidx : m - j + (j - 1 - agem.val) = m - 1 - agem.val := by omega
                      rw [hidx, ha_bit] at hf; simp at hf
                    · omega
                subst hjeq; exact hmj
          · simp only [hag, ↓reduceIte, Bool.false_eq_true, false_iff, not_exists, not_and]
            intro j hjr hjm _ hdj
            by_cases hj0 : j = 0
            · subst hj0; simp [hdmf] at hdj
            · by_cases haeq : agem.val = c.r
              · have hf := hinvm.2.2 haeq (j - 1) (by omega) (by omega)
                have hidx : m - 1 - (j - 1) = m - j := by omega
                rw [hidx, hdj] at hf; simp at hf
              · have haval : agem.val = c.r - 1 := by omega
                have ⟨_, _, ha_zero⟩ := hinvm.2.1 (by omega)
                have hf := ha_zero (j - 1) (by omega)
                have hidx : m - 1 - (j - 1) = m - j := by omega
                rw [hidx, hdj] at hf; simp at hf
      obtain ⟨_, hcheck, hage1_eq⟩ :=
        (transducerStep_eq_some_iff c agem agem1 (x.testBit m) (p.testBit m) (d.testBit m)).mp hstep
      rw [hmsd_eq, ← hcm, ← hage1_eq] at hcheck
      have hcons := add_bit_conservation x (c.mS * d) m
      have hcomb_m : b2n ((x + c.mS * d).testBit m) + 2 * b2n (carryBit x (c.mS * d) (m + 1)) =
                     b2n (p.testBit m) + 2 * b2n (decide (agem1.val < c.r)) := by
        rw [← hcons, hcheck]
      have hbit_eq : (x + c.mS * d).testBit m = p.testBit m := by
        cases h1 : (x + c.mS * d).testBit m <;> cases h2 : p.testBit m <;>
        cases h3 : carryBit x (c.mS * d) (m + 1) <;> cases h4 : decide (agem1.val < c.r) <;>
        simp only [h1, h2, h3, h4, b2n_true, b2n_false] at hcomb_m <;>
        first | rfl | omega
      have hcarry_eq : carryBit x (c.mS * d) (m + 1) = decide (agem1.val < c.r) := by
        cases h1 : (x + c.mS * d).testBit m <;> cases h2 : p.testBit m <;>
        cases h3 : carryBit x (c.mS * d) (m + 1) <;> cases h4 : decide (agem1.val < c.r) <;>
        simp only [h1, h2, h3, h4, b2n_true, b2n_false] at hcomb_m <;>
        first | rfl | omega
      refine ⟨agem1, hrm1, hcarry_eq, fun i hi => ?_⟩
      by_cases him : i < m
      · exact hpm i him
      · have : i = m := by omega
        subst this; exact hbit_eq
  -- 3. `p = x + c.mS * d`
  obtain ⟨_, _, _, hpW⟩ := hstep_inv W (Nat.le_refl W)
  have hmsd_lt : c.mS * d < 2 ^ (N + c.r) := by
    have h1 : c.mS < 2 ^ c.r := c.mS_lt hv
    have h2 : c.mS * d < 2 ^ c.r * 2 ^ N := by
      calc c.mS * d < 2 ^ c.r * (d + 1) := by
            have hle : c.mS + 1 ≤ 2 ^ c.r := h1
            have hmul : (c.mS + 1) * d ≤ 2 ^ c.r * d := Nat.mul_le_mul_right d hle
            rw [Nat.add_mul, Nat.one_mul] at hmul
            rw [Nat.mul_add, Nat.mul_one]
            have := Nat.two_pow_pos c.r; omega
           _ ≤ 2 ^ c.r * 2 ^ N := Nat.mul_le_mul_left _ hdN
    rw [Nat.pow_add, Nat.mul_comm (2 ^ N) (2 ^ c.r)]; exact h2
  have hx_lt_nr : x < 2 ^ (N + c.r) :=
    Nat.lt_of_lt_of_le hxN (Nat.pow_le_pow_right (by omega) (by omega))
  have hsum_lt_W : x + c.mS * d < 2 ^ W := by
    have : W = (N + c.r) + 1 := rfl
    rw [this, Nat.pow_succ]; omega
  have hp_lt_W : p < 2 ^ W :=
    Nat.lt_of_lt_of_le hpN (Nat.pow_le_pow_right (by omega) (by omega))
  have hp_eq : p = x + c.mS * d := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < W
    · exact (hpW i hi).symm
    · rw [testBit_false_of_lt_two_pow hp_lt_W (by omega),
          testBit_false_of_lt_two_pow hsum_lt_W (by omega)]
  -- 4. `carryInMask x (c.mS * d) = (2^(c.r+1) - 2) * d`
  have hcarry_eq : carryInMask x (c.mS * d) = (2 ^ (c.r + 1) - 2) * d := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [carryInMask_testBit]
    apply Bool.eq_iff_iff.mpr
    rw [eigMask_mul_spaced_testBit_iff hr1 hsp]
    by_cases hi : i ≤ W
    · obtain ⟨agei, hri, hci, _⟩ := hstep_inv i hi
      have hinvi := transducerRun_ageInv hv hri
      rw [hci, decide_eq_true_eq]
      constructor
      · intro hlt_r
        obtain ⟨ha_lt, ha_bit, _⟩ := hinvi.2.1 hlt_r
        refine ⟨agei.val + 1, by omega, by omega, by omega, ?_⟩
        have hidx : i - (agei.val + 1) = i - 1 - agei.val := by omega
        rw [hidx]; exact ha_bit
      · rintro ⟨m, hm1, hmr, hmi, hdm⟩
        by_cases hlt_r : agei.val < c.r
        · exact hlt_r
        · have heq_r : agei.val = c.r := by omega
          have hf := hinvi.2.2 heq_r (m - 1) (by omega) (by omega)
          have hidx : i - 1 - (m - 1) = i - m := by omega
          rw [hidx, hdm] at hf; simp at hf
    · have hcf : carryBit x (c.mS * d) i = false :=
        carryBit_eq_false_of_lt hx_lt_nr hmsd_lt (by omega)
      rw [hcf]
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro m _ hmr _ hdm
      have hf := testBit_false_of_lt_two_pow hdN (by omega : N ≤ i - m)
      rw [hf] at hdm; simp at hdm
  -- 5. `p ^^^ x = clmul ((2^c.r) ^^^ c.maskS) d`
  have hclmul_eq : p ^^^ x = clmul ((2 ^ c.r) ^^^ c.maskS) d := by
    have hpx : p ^^^ x = (c.mS * d) ^^^ ((2 ^ (c.r + 1) - 2) * d) := by
      have hk := hcarry_eq
      unfold carryInMask at hk; rw [← hp_eq] at hk
      apply Nat.eq_of_testBit_eq; intro i
      have hi := congrArg (fun n => n.testBit i) hk
      simp only [Nat.testBit_xor] at hi ⊢; rw [← hi]
      cases p.testBit i <;> cases x.testBit i <;> cases (c.mS * d).testBit i <;> rfl
    rw [hpx, mul_spaced_eq_clmul hr1 (c.mS_lt hv) hsp]
    have heig_clm : (2 ^ (c.r + 1) - 2) * d = clmul (2 ^ (c.r + 1) - 2) d := by
      have heq1 : (2 ^ (c.r + 1) - 2) = 2 * (2 ^ c.r - 1) := by
        have : 2 ^ c.r ≥ 1 := Nat.one_le_two_pow; rw [Nat.pow_succ]; omega
      have hlt1 : 2 ^ c.r - 1 < 2 ^ c.r := by have := Nat.one_le_two_pow (n := c.r); omega
      rw [heq1, Nat.mul_assoc, mul_spaced_eq_clmul hr1 hlt1 hsp, clmul_two_mul_left]
    rw [heig_clm, ← clmul_xor_left, c.mS_xor_eigMask hv]
  -- 6. Kummer & Popcount laws
  have hkummer : popcount (carryInMask x (c.mS * d)) = c.r * popcount d := by
    rw [hcarry_eq, popcount_eigMask_mul_spaced hr1 hsp]
  have hpop : popcount x = popcount p + (popcount c.maskS - 1) * popcount d := by
    have hka := popcount_add_carry x (c.mS * d)
    rw [← hp_eq, hkummer, popcount_mul_spaced hr1 (c.mS_lt hv) hsp] at hka
    have hpmS := c.popcount_mS hv
    have hpmask_pos : popcount c.maskS ≥ 1 := by
      rw [popcount_div_two_add, c.valid_odd hv]; omega
    have hmul_sum : (popcount c.maskS - 1) * popcount d + popcount c.mS * popcount d = c.r * popcount d := by
      rw [← Nat.add_mul]
      have : popcount c.maskS - 1 + popcount c.mS = c.r := by omega
      rw [this]
    omega
  -- 7. Arbitrary recurrence conservation law
  have hrec : ∀ G, ObeysRecInt c G → evalRecInt G p = evalRecInt G x :=
    fun G hG => evalRecInt_of_bit_balance (bit_balance_of_carry_eigenvalue hv hsp hp_eq hcarry_eq) G hG
  exact ⟨hsp, hp_eq, hcarry_eq, hclmul_eq, hpop, hkummer, hrec⟩

/-- **TRANSDUCER COMPLETENESS:** Any `r`-spaced `d` and `(x, p)` satisfying the pointwise
    bit-balance law is ACCEPTED by the `(r+1)`-state Carry-Bridge Transducer. -/
theorem transducer_complete_of_bit_balance {c : RecCert} (hv : c.isValid = true) {x p d : Nat}
    (hsp : isRSpaced c.r d)
    (hbal : ∀ i, b2i (p.testBit i) - b2i (x.testBit i) =
      (if i ≥ c.r then b2i (d.testBit (i - c.r)) else 0) -
      sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then b2i (d.testBit (i - j)) else 0)) :
    TransducerAccepts c x p d := by
  have hr := c.valid_r hv
  obtain ⟨Nx, hNx⟩ := exists_lt_two_pow x
  obtain ⟨Np, hNp⟩ := exists_lt_two_pow p
  obtain ⟨Nd, hNd⟩ := exists_lt_two_pow d
  let N := max Nx (max Np Nd)
  have hxN : x < 2 ^ N := Nat.lt_of_lt_of_le hNx (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
  have hpN : p < 2 ^ N := Nat.lt_of_lt_of_le hNp (Nat.pow_le_pow_right (by omega)
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
  have hdN : d < 2 ^ N := Nat.lt_of_lt_of_le hNd (Nat.pow_le_pow_right (by omega)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
  have hrun_some : ∀ n, ∃ age, transducerRun c x p d n = some age := by
    intro n
    induction n with
    | zero => exact ⟨⟨c.r, Nat.lt_succ_self c.r⟩, rfl⟩
    | succ k ih =>
      obtain ⟨agek, hrk⟩ := ih
      have hinv := transducerRun_ageInv hv hrk
      simp only [transducerRun, hrk]
      have hnotbad : (d.testBit k && decide (agek.val < c.r - 1)) = false := by
        by_cases hdk : d.testBit k = true
        · by_cases hag : agek.val < c.r - 1
          · exfalso
            obtain ⟨_, ha_bit, _⟩ := hinv.2.1 (by omega)
            have hf := hsp (k - 1 - agek.val) (agek.val + 1) (by omega) (by omega) ha_bit
            have hidx : k - 1 - agek.val + (agek.val + 1) = k := by omega
            rw [hidx, hdk] at hf; simp at hf
          · simp [hdk, hag]
        · have hdkf : d.testBit k = false := Bool.eq_false_iff.mpr hdk
          simp [hdkf]
      let ci : Bool := decide (agek.val < c.r)
      let msd_i : Bool :=
        if d.testBit k then c.mS.testBit 0
        else if agek.val < c.r - 1 then c.mS.testBit (agek.val + 1)
        else false
      let ageNext : Fin (c.r + 1) :=
        if d.testBit k then ⟨0, Nat.zero_lt_succ c.r⟩
        else ⟨min (agek.val + 1) c.r, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      let ciNext : Bool := decide (ageNext.val < c.r)
      have hint : b2i msd_i + b2i ci - 2 * b2i ciNext =
          (if k ≥ c.r then b2i (d.testBit (k - c.r)) else 0) -
          sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ k) then b2i (d.testBit (k - j)) else 0) := by
        by_cases hdk : d.testBit k = true
        · have hge : agek.val ≥ c.r - 1 := by
            by_cases h : agek.val < c.r - 1
            · simp [hdk, h] at hnotbad
            · omega
          have hmsd_val : msd_i = true := by
            dsimp only [msd_i]; simp [hdk, c.mS_odd hv]
          have hciNext_val : ciNext = true := by
            dsimp only [ciNext, ageNext]; simp [hdk]; omega
          have hsum_val : sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ k) then b2i (d.testBit (k - j)) else 0) = 1 := by
            suffices ∀ n, 1 ≤ n → n ≤ c.r →
                sumInt n (fun j => if c.maskS.testBit j && decide (j ≤ k) then b2i (d.testBit (k - j)) else 0) = 1 from
              this c.r (by omega) (Nat.le_refl _)
            intro n hn1 hnr
            induction n with
            | zero => omega
            | succ m ihm =>
              simp only [sumInt]
              cases m with
              | zero => simp [sumInt, c.valid_bit0 hv, hdk]
              | succ m' =>
                rw [ihm (by omega) (by omega)]
                by_cases hmk : m' + 1 ≤ k
                · have hdf : d.testBit (k - (m' + 1)) = false := by
                    cases h : d.testBit (k - (m' + 1))
                    · rfl
                    · exfalso
                      have hf := hsp (k - (m' + 1)) (m' + 1) (by omega) (by omega) h
                      have hidx : k - (m' + 1) + (m' + 1) = k := by omega
                      rw [hidx, hdk] at hf; simp at hf
                  simp [hmk, hdf]
                · simp [hmk]
          rw [hmsd_val, hciNext_val, hsum_val]
          by_cases hage_eq : agek.val = c.r
          · have hci_val : ci = false := by dsimp only [ci]; exact decide_eq_false (by omega)
            have htop_f : (if k ≥ c.r then b2i (d.testBit (k - c.r)) else 0) = 0 := by
              by_cases hkr : k ≥ c.r
              · have hf := hinv.2.2 hage_eq (c.r - 1) (by omega) (by omega)
                have hidx : k - 1 - (c.r - 1) = k - c.r := by omega
                rw [hidx] at hf; simp [hkr, hf]
              · simp [hkr]
            rw [hci_val, htop_f]; rfl
          · have hage_val : agek.val = c.r - 1 := by omega
            have hci_val : ci = true := by dsimp only [ci]; exact decide_eq_true (by omega)
            obtain ⟨ha_lt, ha_bit, _⟩ := hinv.2.1 (by omega)
            have htop_t : (if k ≥ c.r then b2i (d.testBit (k - c.r)) else 0) = 1 := by
              have hkr : k ≥ c.r := by omega
              have hidx : k - 1 - agek.val = k - c.r := by omega
              rw [hidx] at ha_bit; simp [hkr, ha_bit]
            rw [hci_val, htop_t]; rfl
        · have hdkf : d.testBit k = false := by cases h : d.testBit k <;> simp_all
          by_cases hag : agek.val < c.r - 1
          · obtain ⟨ha_lt, ha_bit, ha_zero⟩ := hinv.2.1 (by omega)
            have hci_val : ci = true := by dsimp only [ci]; exact decide_eq_true (by omega)
            have hciNext_val : ciNext = true := by
              dsimp only [ciNext, ageNext]; simp [hdkf]; omega
            have hmsd_val : msd_i = c.mS.testBit (agek.val + 1) := by
              dsimp only [msd_i]; simp [hdkf, hag]
            have htop_f : (if k ≥ c.r then b2i (d.testBit (k - c.r)) else 0) = 0 := by
              by_cases hkr : k ≥ c.r
              · have hdf : d.testBit (k - c.r) = false := by
                  cases h : d.testBit (k - c.r)
                  · rfl
                  · exfalso
                    have hf := hsp (k - c.r) (c.r - 1 - agek.val) (by omega) (by omega) h
                    have hidx : k - c.r + (c.r - 1 - agek.val) = k - 1 - agek.val := by omega
                    rw [hidx, ha_bit] at hf; simp at hf
                simp [hkr, hdf]
              · simp [hkr]
            have hsum_val : sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ k) then b2i (d.testBit (k - j)) else 0) =
                b2i (c.maskS.testBit (agek.val + 1)) := by
              suffices ∀ n, agek.val + 1 < n → n ≤ c.r →
                  sumInt n (fun j => if c.maskS.testBit j && decide (j ≤ k) then b2i (d.testBit (k - j)) else 0) =
                  b2i (c.maskS.testBit (agek.val + 1)) from
                this c.r (by omega) (Nat.le_refl _)
              intro n hln hnr
              induction n with
              | zero => omega
              | succ m ihm =>
                simp only [sumInt]
                by_cases hmeq : agek.val + 1 = m
                · subst hmeq
                  have hz : sumInt (agek.val + 1) (fun j => if c.maskS.testBit j && decide (j ≤ k) then b2i (d.testBit (k - j)) else 0) = 0 := by
                    apply sumInt_eq_zero; intro j hjlt
                    cases j with
                    | zero => simp [hdkf]
                    | succ j' =>
                      by_cases hjk : j' + 1 ≤ k
                      · have hf := ha_zero j' (by omega)
                        have hidx : k - 1 - j' = k - (j' + 1) := by omega
                        rw [hidx] at hf; simp [hjk, hf]
                      · simp [hjk]
                  rw [hz, Int.zero_add]
                  have hle : agek.val + 1 ≤ k := by omega
                  have hidx : k - (agek.val + 1) = k - 1 - agek.val := by omega
                  rw [hidx, ha_bit]
                  cases c.maskS.testBit (agek.val + 1) <;> simp [hle]
                · rw [ihm (by omega) (by omega)]
                  by_cases hmk : m ≤ k
                  · have hdf : d.testBit (k - m) = false := by
                      cases h : d.testBit (k - m)
                      · rfl
                      · exfalso
                        have hf := hsp (k - m) (m - (agek.val + 1)) (by omega) (by omega) h
                        have hidx : k - m + (m - (agek.val + 1)) = k - 1 - agek.val := by omega
                        rw [hidx, ha_bit] at hf; simp at hf
                    simp [hmk, hdf]
                  · simp [hmk]
            rw [hci_val, hciNext_val, hmsd_val, htop_f, hsum_val]
            have hloc := c.bit_balance_local hv (agek.val + 1)
            have h2r_f : (2 ^ c.r).testBit (agek.val + 1) = false := by
              rw [Nat.testBit_two_pow]; exact decide_eq_false (by omega)
            have he1 : (2 ^ (c.r + 1) - 2).testBit (agek.val + 1) = true := by
              rw [eigMask_testBit]; exact decide_eq_true (by omega)
            have he2 : (2 ^ (c.r + 1) - 2).testBit (agek.val + 2) = true := by
              rw [eigMask_testBit]; exact decide_eq_true (by omega)
            rw [h2r_f, he1, he2] at hloc
            simp only [b2i_true, b2i_false] at hloc ⊢
            omega
          · have hmsd_val : msd_i = false := by dsimp only [msd_i]; simp [hdkf, hag]
            have hciNext_val : ciNext = false := by
              dsimp only [ciNext, ageNext]; simp [hdkf]; omega
            have hsum_zero : sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ k) then b2i (d.testBit (k - j)) else 0) = 0 := by
              apply sumInt_eq_zero; intro j hjr
              cases j with
              | zero => simp [hdkf]
              | succ j' =>
                by_cases hjk : j' + 1 ≤ k
                · have hdf : d.testBit (k - (j' + 1)) = false := by
                    have hidx : k - 1 - j' = k - (j' + 1) := by omega
                    rw [← hidx]
                    by_cases haeq : agek.val = c.r
                    · exact hinv.2.2 haeq j' (by omega) (by omega)
                    · have ⟨_, _, ha_zero⟩ := hinv.2.1 (by omega)
                      exact ha_zero j' (by omega)
                  simp [hjk, hdf]
                · simp [hjk]
            rw [hmsd_val, hciNext_val, hsum_zero]
            by_cases haeq : agek.val = c.r
            · have hci_val : ci = false := by dsimp only [ci]; exact decide_eq_false (by omega)
              have htop_f : (if k ≥ c.r then b2i (d.testBit (k - c.r)) else 0) = 0 := by
                by_cases hkr : k ≥ c.r
                · have hf := hinv.2.2 haeq (c.r - 1) (by omega) (by omega)
                  have hidx : k - 1 - (c.r - 1) = k - c.r := by omega
                  rw [hidx] at hf; simp [hkr, hf]
                · simp [hkr]
              rw [hci_val, htop_f]; rfl
            · have haval : agek.val = c.r - 1 := by omega
              have hci_val : ci = true := by dsimp only [ci]; exact decide_eq_true (by omega)
              obtain ⟨ha_lt, ha_bit, _⟩ := hinv.2.1 (by omega)
              have htop_t : (if k ≥ c.r then b2i (d.testBit (k - c.r)) else 0) = 1 := by
                have hkr : k ≥ c.r := by omega
                have hidx : k - 1 - agek.val = k - c.r := by omega
                rw [hidx] at ha_bit; simp [hkr, ha_bit]
              rw [hci_val, htop_t]; rfl
      have hcheck : b2n (x.testBit k) + b2n msd_i + b2n ci = b2n (p.testBit k) + 2 * b2n ciNext := by
        have hbalk := hbal k
        have hdiff_eq : b2i (p.testBit k) - b2i (x.testBit k) = b2i msd_i + b2i ci - 2 * b2i ciNext := by
          rw [hbalk, hint]
        cases h1 : x.testBit k <;> cases h2 : p.testBit k <;> cases h3 : msd_i <;>
        cases h4 : ci <;> cases h5 : ciNext <;>
        simp only [h1, h2, h3, h4, h5, b2n_true, b2n_false, b2i_true, b2i_false] at hdiff_eq ⊢ <;>
        omega
      refine ⟨ageNext, (transducerStep_eq_some_iff c agek ageNext (x.testBit k) (p.testBit k) (d.testBit k)).mpr ?_⟩
      exact ⟨hnotbad, hcheck, rfl⟩
  obtain ⟨ageW, hrunW⟩ := hrun_some (N + c.r + 1)
  have hinvW := transducerRun_ageInv hv hrunW
  have hage_eq : ageW = ⟨c.r, Nat.lt_succ_self c.r⟩ := by
    apply Fin.ext
    have hlt_succ : ageW.val < c.r + 1 := ageW.isLt
    by_cases hlt : ageW.val < c.r
    · exfalso
      obtain ⟨_, ha_bit, _⟩ := hinvW.2.1 hlt
      have hf := testBit_false_of_lt_two_pow hdN (by omega : N ≤ N + c.r + 1 - 1 - ageW.val)
      rw [hf] at ha_bit; simp at ha_bit
    · simp only; omega
  rw [hage_eq] at hrunW
  exact ⟨N, hxN, hpN, hdN, hrunW⟩

/-- **MASTER CARRY-BRIDGE EQUIVALENCE (Transducer ↔ Binary Carry-Eigenvalue ↔ Bit-Balance):**
    For any valid `RecCert c`, any `x p : Nat`, and any `r`-spaced `d : Nat`:
    `TransducerAccepts c x p d ↔ (p = x + c.mS * d ∧ carryInMask x (c.mS * d) = (2^(c.r+1) - 2) * d)`. -/
theorem master_carry_bridge_iff {c : RecCert} (hv : c.isValid = true) {x p d : Nat}
    (hsp : isRSpaced c.r d) :
    TransducerAccepts c x p d ↔
      (p = x + c.mS * d ∧ carryInMask x (c.mS * d) = (2 ^ (c.r + 1) - 2) * d) := by
  constructor
  · intro hacc
    have ⟨_, hp, hc, _, _, _, _⟩ := transducer_sound hv hacc
    exact ⟨hp, hc⟩
  · rintro ⟨hp, hc⟩
    exact transducer_complete_of_bit_balance hv hsp (bit_balance_of_carry_eigenvalue hv hsp hp hc)

end CarryBridge
namespace CarryBridge
theorem add_eq_xor_of_and_zero {a b : Nat} (h : (a &&& b) = 0) : a + b = a ^^^ b := by
  have hc : ∀ i, carryBit a b i = false := by
    intro i
    induction i with
    | zero => rfl
    | succ k ih =>
      simp only [carryBit, carryBitWith] at ih ⊢
      rw [ih]
      have hand := congrArg (fun n => n.testBit k) h
      rw [Nat.testBit_and, Nat.zero_testBit] at hand
      simp [hand]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [add_testBit_eq, hc i, Nat.testBit_xor, Bool.xor_false]

theorem sRewriteStep_testBit_eq {c : RecCert} (hv : c.isValid = true) {k w w' : Nat}
    (hst : SRewriteStep c k w w') (i : Nat) :
    w'.testBit i =
      if i = k + c.r then true
      else if k ≤ i ∧ i < k + c.r ∧ c.maskS.testBit (i - k) = true then false
      else w.testBit i := by
  obtain ⟨hkr_f, hall_t, hw'⟩ := hst
  subst hw'
  -- Split `w = w % 2^k + 2^k * (w / 2^k)`
  let lo := w % 2 ^ k
  let u := w / 2 ^ k
  have hlo : lo < 2 ^ k := Nat.mod_lt w (Nat.two_pow_pos k)
  have hw_dec : w = lo + 2 ^ k * u := by
    have := Nat.div_add_mod w (2 ^ k); dsimp only [lo, u]; omega
  have hadd_dec : w + c.mS * 2 ^ k = lo + 2 ^ k * (u + c.mS) := by
    rw [hw_dec, Nat.mul_add, Nat.mul_comm c.mS (2 ^ k)]; omega
  -- Prove `u + c.mS = (u ^^^ c.maskS) ^^^ 2^c.r` via zero-carry addition!
  have hu_mask_and : ((u ^^^ c.maskS) &&& c.maskS) = 0 := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    cases hmj : c.maskS.testBit j
    · simp
    · have hjr : j < c.r := by
        by_cases hlt : j < c.r
        · exact hlt
        · have hf := testBit_false_of_lt_two_pow (c.valid_lt hv) (show c.r ≤ j by omega)
          rw [hf] at hmj; simp at hmj
      have huj : u.testBit j = true := by
        have htb := hall_t j hjr hmj
        have hdiv_tb : (w / 2 ^ k).testBit j = w.testBit (k + j) := by
          rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
        rw [hdiv_tb]; exact htb
      simp [huj]
  have hu_eq : (u ^^^ c.maskS) + c.maskS = u := by
    rw [add_eq_xor_of_and_zero hu_mask_and]
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_xor, Nat.testBit_xor]
    cases u.testBit j <;> cases c.maskS.testBit j <;> rfl
  have hu_cr_f : (u ^^^ c.maskS).testBit c.r = false := by
    rw [Nat.testBit_xor]
    have h1 : u.testBit c.r = false := by
      have hdiv_tb : (w / 2 ^ k).testBit c.r = w.testBit (k + c.r) := by
        rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
      rw [hdiv_tb]; exact hkr_f
    have h2 : c.maskS.testBit c.r = false := testBit_false_of_lt_two_pow (c.valid_lt hv) (Nat.le_refl _)
    simp [h1, h2]
  have hu_pow_and : ((u ^^^ c.maskS) &&& (2 ^ c.r)) = 0 := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hjr : c.r = j
    · subst hjr; simp [hu_cr_f]
    · simp [hjr]
  have hu_add : u + c.mS = (u ^^^ c.maskS) ^^^ (2 ^ c.r) := by
    calc u + c.mS = ((u ^^^ c.maskS) + c.maskS) + c.mS := by rw [hu_eq]
         _ = (u ^^^ c.maskS) + (c.maskS + c.mS) := Nat.add_assoc _ _ _
         _ = (u ^^^ c.maskS) + 2 ^ c.r := by rw [c.maskS_add_mS hv]
         _ = (u ^^^ c.maskS) ^^^ 2 ^ c.r := add_eq_xor_of_and_zero hu_pow_and
  -- Now test bit `i` of `lo + 2^k * (u + c.mS)` vs `lo + 2^k * u`!
  rw [hadd_dec]
  have htb1 := Nat.testBit_two_pow_mul_add (u + c.mS) hlo i
  rw [Nat.add_comm] at htb1
  rw [htb1]
  have htb0 := Nat.testBit_two_pow_mul_add u hlo i
  rw [Nat.add_comm, ← hw_dec] at htb0
  by_cases hik : i < k
  · simp only [hik, ↓reduceIte]
    have h1 : ¬(i = k + c.r) := by omega
    have h2 : ¬(k ≤ i ∧ i < k + c.r ∧ c.maskS.testBit (i - k) = true) := by omega
    simp only [h1, h2, ↓reduceIte]
    rw [htb0]; simp [hik]
  · simp only [hik, ↓reduceIte, hu_add, Nat.testBit_xor, Nat.testBit_two_pow]
    have hu_bit : u.testBit (i - k) = w.testBit i := by
      rw [htb0]; simp [hik]
    rw [hu_bit]
    by_cases hieq : i = k + c.r
    · subst hieq
      have hsub : k + c.r - k = c.r := by omega
      have hmf : c.maskS.testBit c.r = false := testBit_false_of_lt_two_pow (c.valid_lt hv) (Nat.le_refl _)
      simp [hsub, hkr_f, hmf]
    · simp only [hieq, ↓reduceIte]
      have hne : c.r ≠ i - k := by omega
      simp only [decide_eq_false hne, Bool.xor_false]
      by_cases hilt : i < k + c.r
      · by_cases hmj : c.maskS.testBit (i - k) = true
        · have hwt : w.testBit i = true := by
            have := hall_t (i - k) (by omega) hmj
            have hadd : k + (i - k) = i := by omega
            rw [hadd] at this; exact this
          simp [show k ≤ i by omega, hilt, hmj, hwt]
        · have hmjf : c.maskS.testBit (i - k) = false := Bool.eq_false_iff.mpr hmj
          simp [hmjf]
      · have hmjf : c.maskS.testBit (i - k) = false :=
          testBit_false_of_lt_two_pow (c.valid_lt hv) (show c.r ≤ i - k by omega)
        simp [hilt, hmjf]

theorem sRewriteStep_bit_delta {c : RecCert} (hv : c.isValid = true) {k w w' : Nat}
    (hst : SRewriteStep c k w w') (i : Nat) :
    b2i (w'.testBit i) - b2i (w.testBit i) =
      (if i = k + c.r then 1 else 0) -
      (if k ≤ i ∧ i < k + c.r ∧ c.maskS.testBit (i - k) = true then 1 else 0) := by
  have hr := c.valid_r hv
  rw [sRewriteStep_testBit_eq hv hst i]
  by_cases hieq : i = k + c.r
  · subst hieq
    have hnot : ¬(k ≤ k + c.r ∧ k + c.r < k + c.r ∧ c.maskS.testBit (k + c.r - k) = true) := by omega
    simp [hst.1]
  · simp only [hieq, ↓reduceIte]
    by_cases hcond : k ≤ i ∧ i < k + c.r ∧ c.maskS.testBit (i - k) = true
    · have hwt : w.testBit i = true := by
        have := hst.2.1 (i - k) (by omega) hcond.2.2
        have hadd : k + (i - k) = i := by omega
        rw [hadd] at this; exact this
      simp [hcond, hwt]
    · simp [hcond]

/-! ### 3.2 Derivation Composition, Bit-Flip Tracing & Difference-Basis Spacing Proof -/

theorem SRewriteDeriv.append {c : RecCert} {ks1 ks2 : List Nat} {w0 w1 w2 : Nat}
    (h1 : SRewriteDeriv c ks1 w0 w1) (h2 : SRewriteDeriv c ks2 w1 w2) :
    SRewriteDeriv c (ks1 ++ ks2) w0 w2 := by
  induction h1 with
  | nil _ => exact h2
  | cons hst _ ih => exact SRewriteDeriv.cons hst (ih h2)

theorem SRewriteDeriv.split_append {c : RecCert} {ks1 ks2 : List Nat} {w0 w2 : Nat}
    (h : SRewriteDeriv c (ks1 ++ ks2) w0 w2) :
    ∃ w1, SRewriteDeriv c ks1 w0 w1 ∧ SRewriteDeriv c ks2 w1 w2 := by
  induction ks1 generalizing w0 with
  | nil => exact ⟨w0, SRewriteDeriv.nil w0, h⟩
  | cons k ks ih =>
    cases h with
    | cons hst hrest =>
      obtain ⟨w1, hd1, hd2⟩ := ih hrest
      exact ⟨w1, SRewriteDeriv.cons hst hd1, hd2⟩

theorem deriv_bit_changed_0_to_1 {c : RecCert} (hv : c.isValid = true) {ks : List Nat} {w0 wt m : Nat}
    (h : SRewriteDeriv c ks w0 wt) (h0 : w0.testBit m = false) (ht : wt.testBit m = true) :
    ∃ k, k ∈ ks ∧ k + c.r = m := by
  induction h with
  | nil w => rw [h0] at ht; simp at ht
  | cons hst hrest ih =>
    rename_i k ks' w w1 w2
    by_cases hw1 : w1.testBit m = true
    · rw [sRewriteStep_testBit_eq hv hst m] at hw1
      by_cases hmeq : m = k + c.r
      · exact ⟨k, List.Mem.head _, hmeq.symm⟩
      · simp only [hmeq, ↓reduceIte] at hw1
        by_cases hc : k ≤ m ∧ m < k + c.r ∧ c.maskS.testBit (m - k) = true
        · simp [hc] at hw1
        · simp only [hc, ↓reduceIte, h0] at hw1; simp at hw1
    · have hw1f : w1.testBit m = false := Bool.eq_false_iff.mpr hw1
      obtain ⟨k', hk'mem, hk'eq⟩ := ih hw1f ht
      exact ⟨k', List.Mem.tail _ hk'mem, hk'eq⟩

/-- **THE DIFFERENCE-BASIS SPACING THEOREM:**
    If `c.isDiffBasis = true`, then EVERY finite `S`-rewrite derivation (in ANY rewrite order!)
    fires pairwise at distance `≥ c.r` (zero duplicates, zero overlaps within width `c.r`). -/
theorem diff_basis_deriv_spaced {c : RecCert} (hdb : c.isDiffBasis = true) {ks : List Nat} {x p : Nat}
    (hd : SRewriteDeriv c ks x p) : PairwiseRSpaced c.r ks := by
  have hv : c.isValid = true := c.isDiffBasis_valid hdb
  have hr : c.r ≥ 2 := c.valid_r hv
  -- Induct on `ks.length` from the right (splitting off the last element)
  suffices ∀ n (ks : List Nat) (x p : Nat), ks.length = n → SRewriteDeriv c ks x p → PairwiseRSpaced c.r ks from
    this ks.length ks x p rfl hd
  intro n
  induction n with
  | zero =>
    intro ks x p hlen _
    cases ks with
    | nil => exact List.Pairwise.nil
    | cons _ _ => simp at hlen
  | succ m ih =>
    intro ks x p hlen hd
    -- Split `ks = init ++ [kt]`
    have hne : ks ≠ [] := by intro h; subst h; simp at hlen
    have hsplit_last : ∀ (l : List Nat), l ≠ [] → ∃ init kt, l = init ++ [kt] := by
      intro l
      induction l with
      | nil => intro h; exact absurd rfl h
      | cons a tl ihtl =>
        intro _
        cases tl with
        | nil => exact ⟨[], a, rfl⟩
        | cons b tl' =>
          obtain ⟨init', kt', heq⟩ := ihtl (by simp)
          exact ⟨a :: init', kt', by simp [heq]⟩
    obtain ⟨init, kt, hks_eq⟩ := hsplit_last ks hne
    have hinit_len : init.length = m := by
      have := congrArg List.length hks_eq; simp at this; omega
    rw [hks_eq] at hd ⊢
    obtain ⟨wprev, hd_init, hd_last⟩ := SRewriteDeriv.split_append hd
    have hsp_init : PairwiseRSpaced c.r init := ih init x wprev hinit_len hd_init
    cases hd_last with
    | cons hst_t hnil =>
      cases hnil
      -- To show `PairwiseRSpaced c.r (init ++ [kt])`, it suffices to show every `ku ∈ init` satisfies `ku + c.r ≤ kt ∨ kt + c.r ≤ ku`
      have hpw_append : ∀ (l : List Nat) (y : Nat),
          PairwiseRSpaced c.r l → (∀ u, u ∈ l → u + c.r ≤ y ∨ y + c.r ≤ u) →
          PairwiseRSpaced c.r (l ++ [y]) := by
        intro l y hl hall
        induction l with
        | nil => simp [PairwiseRSpaced]
        | cons a tl ihtl =>
          simp only [List.cons_append, PairwiseRSpaced, List.pairwise_cons] at hl ⊢
          refine ⟨?_, ihtl hl.2 (fun u hu => hall u (List.Mem.tail _ hu))⟩
          intro v hvmem
          rcases List.mem_append.mp hvmem with htl | hlast
          · exact hl.1 v htl
          · simp only [List.mem_singleton] at hlast
            subst hlast
            exact hall a (List.Mem.head _)
      apply hpw_append init kt hsp_init
      -- Helper to split `init = pref ++ [ku] ++ suff` and trace bit `m` from `ku` to `kt`!
      have hsplit_mem : ∀ u, u ∈ init →
          ∃ pref suff w_after, init = pref ++ (u :: suff) ∧
            (∀ j, j < c.r → c.maskS.testBit j = true → w_after.testBit (u + j) = false) ∧
            SRewriteDeriv c suff w_after wprev ∧
            (∀ v, v ∈ suff → u + c.r ≤ v ∨ v + c.r ≤ u) := by
        intro u humem
        obtain ⟨pref, suff, hdecomp⟩ := List.append_of_mem humem
        have hd_init' := hd_init
        rw [hdecomp] at hd_init'
        obtain ⟨w_before, _, hd_usuff⟩ := SRewriteDeriv.split_append hd_init'
        cases hd_usuff with
        | cons hst_u hd_suff =>
          rename_i w_after
          have hpw_suff : ∀ v, v ∈ suff → u + c.r ≤ v ∨ v + c.r ≤ u := by
            have hpw' := hsp_init
            rw [hdecomp] at hpw'
            unfold PairwiseRSpaced at hpw'
            have hpw_r := (List.pairwise_append.mp hpw').2.1
            exact (List.pairwise_cons.mp hpw_r).1
          refine ⟨pref, suff, w_after, hdecomp, ?_, hd_suff, hpw_suff⟩
          intro j hjr hmj
          rw [sRewriteStep_testBit_eq hv hst_u (u + j)]
          have hne_r : ¬(u + j = u + c.r) := by omega
          have hcond : u ≤ u + j ∧ u + j < u + c.r ∧ c.maskS.testBit (u + j - u) = true := by
            have hsub : u + j - u = j := by omega
            exact ⟨by omega, by omega, by rw [hsub]; exact hmj⟩
          simp [show j ≠ c.r by omega, hmj, hcond]
      -- Step 1: Rule out `ku < kt ∧ kt < ku + c.r` for ANY `ku ∈ init`!
      have hno_above : ∀ ku, ku ∈ init → ¬(ku < kt ∧ kt < ku + c.r) := by
        intro ku kumem ⟨hlt1, hlt2⟩
        let δ := kt - ku
        obtain ⟨a, b, har, hbr, hma, hmb, hab⟩ := c.isDiffBasis_spec hdb δ (by omega) (by omega)
        obtain ⟨_, suff, w_after, _, hclear, hd_suff, hpw_suff⟩ := hsplit_mem ku kumem
        have hm0 : w_after.testBit (ku + a) = false := hclear a har hma
        have hmt : wprev.testBit (ku + a) = true := by
          have heq : ku + a = kt + b := by omega
          rw [heq]; exact hst_t.2.1 b hbr hmb
        obtain ⟨kw, kwmem, kweq⟩ := deriv_bit_changed_0_to_1 hv hd_suff hm0 hmt
        have hdist := hpw_suff kw kwmem
        omega
      -- Now prove `ku + c.r ≤ kt ∨ kt + c.r ≤ ku` for every `ku ∈ init`!
      intro ku kumem
      by_cases hcase : ku + c.r ≤ kt ∨ kt + c.r ≤ ku
      · exact hcase
      · exfalso
        by_cases hlt : ku < kt
        · exact hno_above ku kumem ⟨hlt, by omega⟩
        · by_cases hgt : kt < ku
          · -- Case 2: `kt < ku < kt + c.r`
            let δ := ku - kt
            obtain ⟨a, b, har, hbr, hma, hmb, hab⟩ := c.isDiffBasis_spec hdb δ (by omega) (by omega)
            obtain ⟨pref, suff, w_after, hdecomp, hclear, hd_suff, hpw_suff⟩ := hsplit_mem ku kumem
            have hm0 : w_after.testBit (ku + b) = false := hclear b hbr hmb
            have hmt : wprev.testBit (ku + b) = true := by
              have heq : ku + b = kt + a := by omega
              rw [heq]; exact hst_t.2.1 a har hma
            obtain ⟨kw, kwmem, kweq⟩ := deriv_bit_changed_0_to_1 hv hd_suff hm0 hmt
            by_cases hb0 : b = 0
            · -- `kw + c.r = ku`, hence `kw < kt < kw + c.r` with `kw ∈ init`: killed by Step 1!
              have kw_in_init : kw ∈ init := by
                rw [hdecomp]; exact List.mem_append_right _ (List.Mem.tail _ kwmem)
              exact hno_above kw kw_in_init (by omega)
            · have hdist := hpw_suff kw kwmem
              omega
          · -- Case 3: `kt = ku`
            have hkeq : kt = ku := by omega
            obtain ⟨a, b, har, _, hma, _, hab⟩ := c.isDiffBasis_spec hdb 1 (by omega) (by omega)
            obtain ⟨_, suff, w_after, _, hclear, hd_suff, hpw_suff⟩ := hsplit_mem ku kumem
            have hm0 : w_after.testBit (ku + a) = false := hclear a har hma
            have hmt : wprev.testBit (ku + a) = true := by
              rw [← hkeq]; exact hst_t.2.1 a har hma
            obtain ⟨kw, kwmem, kweq⟩ := deriv_bit_changed_0_to_1 hv hd_suff hm0 hmt
            have hdist := hpw_suff kw kwmem
            omega

/-! ### 3.3 Lifting `PairwiseRSpaced` Derivations to the Carry-Bridge Transducer -/

theorem sumPow2_testBit_of_pairwise {r : Nat} {ks : List Nat} (hr : r ≥ 1)
    (hpw : PairwiseRSpaced r ks) (i : Nat) :
    (sumPow2 ks).testBit i = decide (i ∈ ks) := by
  induction ks generalizing i with
  | nil => simp [sumPow2]
  | cons k tl ih =>
    unfold PairwiseRSpaced at hpw
    rw [List.pairwise_cons] at hpw
    have ihtl : ∀ j, (sumPow2 tl).testBit j = decide (j ∈ tl) := fun j => ih hpw.2 j
    simp only [sumPow2]
    have hand : ((2 ^ k) &&& sumPow2 tl) = 0 := by
      apply Nat.eq_of_testBit_eq; intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow, ihtl j, Nat.zero_testBit]
      by_cases hkj : k = j
      · subst hkj
        have hnotmem : k ∉ tl := by
          intro hmem; have := hpw.1 k hmem; omega
        simp [hnotmem]
      · simp [hkj]
    rw [add_eq_xor_of_and_zero hand, Nat.testBit_xor, Nat.testBit_two_pow, ihtl i]
    by_cases hki : k = i
    · subst hki
      have hnotmem : k ∉ tl := by
        intro hmem; have := hpw.1 k hmem; omega
      simp [hnotmem]
    · have hine : i ≠ k := fun h => hki h.symm
      simp [hki, hine]

theorem isRSpaced_sumPow2_of_pairwise {r : Nat} {ks : List Nat} (hr : r ≥ 1)
    (hpw : PairwiseRSpaced r ks) : isRSpaced r (sumPow2 ks) := by
  intro i j hj1 hjr hi
  rw [sumPow2_testBit_of_pairwise hr hpw i, decide_eq_true_eq] at hi
  rw [sumPow2_testBit_of_pairwise hr hpw (i + j), decide_eq_false_iff_not]
  intro hij
  -- Show any two members `u, v` of a `PairwiseRSpaced r ks` list either coincide or satisfy `|u - v| ≥ r`
  have hmem_dist : ∀ (l : List Nat) (u v : Nat),
      PairwiseRSpaced r l → u ∈ l → v ∈ l → u = v ∨ u + r ≤ v ∨ v + r ≤ u := by
    intro l u v hl hu hv
    induction l with
    | nil => cases hu
    | cons a tl ihtl =>
      unfold PairwiseRSpaced at hl; rw [List.pairwise_cons] at hl
      cases hu with
      | head =>
        cases hv with
        | head => exact Or.inl rfl
        | tail _ hvt => exact Or.inr (hl.1 v hvt)
      | tail _ hut =>
        cases hv with
        | head =>
          rcases hl.1 u hut with h1 | h2
          · exact Or.inr (Or.inr h1)
          · exact Or.inr (Or.inl h2)
        | tail _ hvt => exact ihtl hl.2 hut hvt
  rcases hmem_dist ks i (i + j) hpw hi hij with h1 | h2 | h3 <;> omega

theorem deriv_bit_balance_of_pairwise {c : RecCert} (hv : c.isValid = true) {ks : List Nat} {x p : Nat}
    (hd : SRewriteDeriv c ks x p) (hpw : PairwiseRSpaced c.r ks) (i : Nat) :
    b2i (p.testBit i) - b2i (x.testBit i) =
      (if i ≥ c.r then b2i ((sumPow2 ks).testBit (i - c.r)) else 0) -
      sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then b2i ((sumPow2 ks).testBit (i - j)) else 0) := by
  have hr1 : c.r ≥ 1 := by have := c.valid_r hv; omega
  induction hd with
  | nil w =>
    simp only [sumPow2, Nat.zero_testBit, b2i_false, ite_self, sumInt_zero]
    omega
  | cons hst hrest ih =>
    rename_i k tl w w1 w2
    unfold PairwiseRSpaced at hpw; rw [List.pairwise_cons] at hpw
    have ihtl := ih hpw.2
    have hstep := sRewriteStep_bit_delta hv hst i
    have hd_all : ∀ m, (sumPow2 (k :: tl)).testBit m = (decide (m = k) || (sumPow2 tl).testBit m) := by
      intro m
      rw [sumPow2_testBit_of_pairwise hr1 (List.pairwise_cons.mpr hpw) m,
          sumPow2_testBit_of_pairwise hr1 hpw.2 m]
      by_cases hmk : m = k <;> simp [hmk]
    have hnotmem : k ∉ tl := fun hm => by have := hpw.1 k hm; omega
    have hb2i_add : ∀ m, b2i ((sumPow2 (k :: tl)).testBit m) =
        (if m = k then 1 else 0) + b2i ((sumPow2 tl).testBit m) := by
      intro m
      rw [hd_all m]
      by_cases hmk : m = k
      · subst hmk
        have htlf : (sumPow2 tl).testBit m = false := by
          rw [sumPow2_testBit_of_pairwise hr1 hpw.2 m]; exact decide_eq_false hnotmem
        simp [htlf]
      · simp [hmk]
    have htop_split :
        (if i ≥ c.r then b2i ((sumPow2 (k :: tl)).testBit (i - c.r)) else 0) =
        (if i = k + c.r then 1 else 0) + (if i ≥ c.r then b2i ((sumPow2 tl).testBit (i - c.r)) else 0) := by
      by_cases hri : i ≥ c.r
      · simp only [hri, ↓reduceIte, hb2i_add (i - c.r)]
        have heq : (i - c.r = k) ↔ (i = k + c.r) := by omega
        by_cases h : i = k + c.r <;> simp [h, heq]
      · have hne : i ≠ k + c.r := by omega
        simp [hri, hne]
    have hsum_split :
        sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then b2i ((sumPow2 (k :: tl)).testBit (i - j)) else 0) =
        (if k ≤ i ∧ i < k + c.r ∧ c.maskS.testBit (i - k) = true then 1 else 0) +
        sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then b2i ((sumPow2 tl).testBit (i - j)) else 0) := by
      have hadd_f : sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then b2i ((sumPow2 (k :: tl)).testBit (i - j)) else 0) =
          sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then (if i - j = k then 1 else 0) else 0) +
          sumInt c.r (fun j => if c.maskS.testBit j && decide (j ≤ i) then b2i ((sumPow2 tl).testBit (i - j)) else 0) := by
        rw [← sumInt_add]
        apply sumInt_congr; intro j _
        by_cases hc : (c.maskS.testBit j && decide (j ≤ i)) = true
        · simp only [hc, ↓reduceIte, hb2i_add (i - j)]
        · have hcf : (c.maskS.testBit j && decide (j ≤ i)) = false := Bool.eq_false_iff.mpr hc
          simp [hcf]
      rw [hadd_f]; congr 1
      -- Evaluate the Kronecker sum over `j < c.r`
      by_cases hcond : k ≤ i ∧ i < k + c.r ∧ c.maskS.testBit (i - k) = true
      · simp only [hcond]
        suffices ∀ n, i - k < n → n ≤ c.r →
            sumInt n (fun j => if c.maskS.testBit j && decide (j ≤ i) then (if i - j = k then 1 else 0) else 0) = 1 from
          this c.r (by omega) (Nat.le_refl _)
        intro n hln hnr
        induction n with
        | zero => omega
        | succ m ihm =>
          simp only [sumInt]
          by_cases hmeq : i - k = m
          · subst hmeq
            have hz : sumInt (i - k) (fun j => if c.maskS.testBit j && decide (j ≤ i) then (if i - j = k then 1 else 0) else 0) = 0 := by
              apply sumInt_eq_zero; intro j hjl
              have hne : i - j ≠ k := by omega
              simp [hne]
            rw [hz, Int.zero_add]
            have hle : i - k ≤ i := by omega
            have hsub : i - (i - k) = k := by omega
            simp [hcond.2.2, hle, hsub]
          · rw [ihm (by omega) (by omega)]
            by_cases hmi : m ≤ i
            · have hne : i - m ≠ k := by omega
              simp [hne]
            · simp [hmi]
      · simp only [hcond, ↓reduceIte]
        apply sumInt_eq_zero; intro j hjr
        by_cases hji : j ≤ i
        · by_cases heqk : i - j = k
          · have hjeq : j = i - k := by omega
            subst hjeq
            have hmf : c.maskS.testBit (i - k) = false := by
              cases h : c.maskS.testBit (i - k)
              · rfl
              · exfalso; exact hcond ⟨by omega, by omega, h⟩
            simp [hmf]
          · simp [heqk]
        · simp [hji]
    rw [htop_split, hsum_split]
    omega

/-- **FORWARD DIRECTION OF THE DIFFERENCE-BASIS CARRY-BRIDGE DICHOTOMY:**
    Any finite certificate passing `c.isDiffBasis = true` (checked by `decide`) guarantees
    that EVERY `S`-rewrite derivation `x →*_S p` (in ANY order!) is accepted by the `(r+1)`-state
    Carry-Bridge Transducer and obeys ALL SIX infinite binary/Kummer/`clmul`/recurrence laws! -/
theorem diff_basis_implies_all_laws {c : RecCert} (hdb : c.isDiffBasis = true)
    {ks : List Nat} {x p : Nat} (hd : SRewriteDeriv c ks x p) :
    let d := sumPow2 ks
    TransducerAccepts c x p d ∧
    isRSpaced c.r d ∧
    p = x + c.mS * d ∧
    carryInMask x (c.mS * d) = (2 ^ (c.r + 1) - 2) * d ∧
    p ^^^ x = clmul ((2 ^ c.r) ^^^ c.maskS) d ∧
    popcount x = popcount p + (popcount c.maskS - 1) * popcount d ∧
    popcount (carryInMask x (c.mS * d)) = c.r * popcount d ∧
    (∀ G, ObeysRecInt c G → evalRecInt G p = evalRecInt G x) := by
  have hv := c.isDiffBasis_valid hdb
  have hr1 : c.r ≥ 1 := by have := c.valid_r hv; omega
  have hpw := diff_basis_deriv_spaced hdb hd
  have hsp := isRSpaced_sumPow2_of_pairwise hr1 hpw
  have hbal := deriv_bit_balance_of_pairwise hv hd hpw
  have hacc := transducer_complete_of_bit_balance hv hsp hbal
  exact ⟨hacc, transducer_sound hv hacc⟩

/-- **CONVERSE / SHARPNESS DIRECTION OF THE DICHOTOMY:**
    If `c` is valid (`r ≥ 2`, `0 ∈ S`, `maskS < 2^r`) and NOT a difference basis (`c.isDiffBasis = false`),
    then there is an explicit 2-step derivation `x →_δ w1 →_0 p` at `x = maskS ||| (maskS <<< δ)`
    with `d = 2^δ + 1` that VIOLATES both `r`-spacing AND the binary carry-eigenvalue law! -/
theorem not_diff_basis_refutation {c : RecCert} (hv : c.isValid = true) (hndb : c.isDiffBasis = false) :
    ∃ ks x p, SRewriteDeriv c ks x p ∧
      let d := sumPow2 ks
      ¬ isRSpaced c.r d ∧
      carryInMask x (c.mS * d) ≠ (2 ^ (c.r + 1) - 2) * d := by
  have hr := c.valid_r hv
  -- Extract witness `1 ≤ δ < c.r` with `c.maskS &&& (c.maskS >>> δ) = 0`
  have hex_δ : ∃ δ, 1 ≤ δ ∧ δ < c.r ∧ (c.maskS &&& (c.maskS >>> δ)) = 0 := by
    unfold RecCert.isDiffBasis at hndb
    rw [hv, Bool.true_and] at hndb
    have hnotall : ¬((List.range (c.r - 1)).all (fun t => (c.maskS &&& (c.maskS >>> (t + 1))) != 0) = true) := by
      rw [hndb]; simp
    rw [List.all_eq_true] at hnotall
    -- Decidable search in `{0 .. c.r - 2}`
    suffices ∀ n, (∃ t, t < n ∧ (c.maskS &&& (c.maskS >>> (t + 1))) = 0) ∨
        (∀ t, t < n → (c.maskS &&& (c.maskS >>> (t + 1))) != 0) by
      rcases this (c.r - 1) with ⟨t, ht, hzero⟩ | hall
      · exact ⟨t + 1, by omega, by omega, hzero⟩
      · exfalso; apply hnotall
        intro t htmem; exact hall t (List.mem_range.mp htmem)
    intro n
    induction n with
    | zero => exact Or.inr (fun t ht => by omega)
    | succ k ih =>
      rcases ih with ⟨t, ht, hz⟩ | hall
      · exact Or.inl ⟨t, by omega, hz⟩
      · by_cases hk : (c.maskS &&& (c.maskS >>> (k + 1))) = 0
        · exact Or.inl ⟨k, by omega, hk⟩
        · exact Or.inr (fun t ht => by
            by_cases htk : t < k
            · exact hall t htk
            · have htk_eq : t = k := by omega
              subst htk_eq; exact bne_iff_ne.mpr hk)
  obtain ⟨δ, hδ1, hδr, hdisj⟩ := hex_δ
  -- Disjointness in bit form: `c.maskS` and `c.maskS <<< δ` have ZERO overlapping 1-bits!
  have hdisj_shift : (c.maskS &&& (c.maskS <<< δ)) = 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit]
    by_cases hi : δ ≤ i
    · simp only [decide_eq_true hi, Bool.true_and]
      have h0 := congrArg (fun n => n.testBit (i - δ)) hdisj
      rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.zero_testBit] at h0
      have heq : δ + (i - δ) = i := by omega
      rw [heq] at h0
      rw [Bool.and_comm]; exact h0
    · simp [hi]
  let x := c.maskS ||| (c.maskS <<< δ)
  let w1 := x + c.mS * 2 ^ δ
  let p := w1 + c.mS * 2 ^ 0
  have hx_eq_add : x = c.maskS + c.maskS * 2 ^ δ := by
    have hor_xor : c.maskS ||| (c.maskS <<< δ) = c.maskS ^^^ (c.maskS <<< δ) := by
      apply Nat.eq_of_testBit_eq; intro i
      have h0 := congrArg (fun n => n.testBit i) hdisj_shift
      rw [Nat.testBit_and, Nat.zero_testBit] at h0
      rw [Nat.testBit_or, Nat.testBit_xor]
      cases h1 : c.maskS.testBit i <;> cases h2 : (c.maskS <<< δ).testBit i <;> simp_all
    dsimp only [x]
    rw [hor_xor, ← add_eq_xor_of_and_zero hdisj_shift, Nat.shiftLeft_eq]
  -- Step 1: `SRewriteStep c δ x w1`
  have hst1 : SRewriteStep c δ x w1 := by
    refine ⟨?_, ?_, rfl⟩
    · dsimp only [x]
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      have h1 : c.maskS.testBit (δ + c.r) = false := testBit_false_of_lt_two_pow (c.valid_lt hv) (by omega)
      have h2 : c.maskS.testBit (δ + c.r - δ) = false := by
        have : δ + c.r - δ = c.r := by omega
        rw [this]; exact testBit_false_of_lt_two_pow (c.valid_lt hv) (Nat.le_refl _)
      rw [h1, h2]; simp
    · intro j hjr hmj
      dsimp only [x]
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      have hge : δ ≤ δ + j := by omega
      have hsub : δ + j - δ = j := by omega
      simp [hge, hsub, hmj]
  -- Compute `w1 = c.maskS + 2^(c.r + δ)`!
  have hw1_eq : w1 = c.maskS + 2 ^ (c.r + δ) := by
    dsimp only [w1]
    rw [hx_eq_add, Nat.add_assoc, ← Nat.add_mul, c.maskS_add_mS hv, ← Nat.pow_add]
  -- Step 2: `SRewriteStep c 0 w1 p`
  have hst2 : SRewriteStep c 0 w1 p := by
    have hdisj_w1 : (c.maskS &&& (2 ^ (c.r + δ))) = 0 := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : c.r + δ = i
      · subst hi
        rw [testBit_false_of_lt_two_pow (c.valid_lt hv) (by omega)]; simp
      · simp [hi]
    have hw1_xor : w1 = c.maskS ^^^ (2 ^ (c.r + δ)) := by
      rw [hw1_eq, add_eq_xor_of_and_zero hdisj_w1]
    refine ⟨?_, ?_, rfl⟩
    · rw [hw1_xor, Nat.testBit_xor, Nat.testBit_two_pow, Nat.zero_add]
      have h1 : c.maskS.testBit c.r = false := testBit_false_of_lt_two_pow (c.valid_lt hv) (Nat.le_refl _)
      have h2 : ¬(c.r + δ = c.r) := by omega
      rw [h1, decide_eq_false h2]; rfl
    · intro j hjr hmj
      rw [hw1_xor, Nat.testBit_xor, Nat.testBit_two_pow, Nat.zero_add]
      have h2 : ¬(c.r + δ = j) := by omega
      rw [hmj, decide_eq_false h2]; rfl
  have hderiv : SRewriteDeriv c [δ, 0] x p :=
    SRewriteDeriv.cons hst1 (SRewriteDeriv.cons hst2 (SRewriteDeriv.nil p))
  -- Compute `d = 2^δ + 1` and `p = 2^c.r + 2^(c.r + δ)`
  have hd_val : sumPow2 [δ, 0] = 2 ^ δ + 1 := by simp [sumPow2]
  have hp_val : p = 2 ^ c.r + 2 ^ (c.r + δ) := by
    dsimp only [p]
    rw [hw1_eq, Nat.pow_zero, Nat.mul_one, Nat.add_right_comm, c.maskS_add_mS hv]
  have hp_eq_add : p = x + c.mS * (2 ^ δ + 1) := by
    dsimp only [p, w1]; rw [Nat.pow_zero, Nat.mul_one, Nat.mul_add, Nat.mul_one]; omega
  refine ⟨[δ, 0], x, p, hderiv, ?_, ?_⟩
  · -- `¬ isRSpaced c.r (2^δ + 1)`
    rw [hd_val]
    intro hsp
    have hdisj_d : ((2 ^ δ) &&& 1) = 0 := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      cases i with
      | zero => simp [show δ ≠ 0 by omega]
      | succ k =>
        rw [testBit_false_of_lt_two_pow (show (1 : Nat) < 2 ^ 1 by decide) (by omega)]; simp
    have hd_xor : 2 ^ δ + 1 = (2 ^ δ) ^^^ 1 := add_eq_xor_of_and_zero hdisj_d
    have hd0 : (2 ^ δ + 1).testBit 0 = true := by
      rw [hd_xor, Nat.testBit_xor, Nat.testBit_two_pow]
      have hne : δ ≠ 0 := by omega
      have h10 : (1 : Nat).testBit 0 = true := by decide
      simp [hne, h10]
    have hdδ : (2 ^ δ + 1).testBit δ = true := by
      rw [hd_xor, Nat.testBit_xor, Nat.testBit_two_pow]
      have h1δ : (1 : Nat).testBit δ = false :=
        testBit_false_of_lt_two_pow (show (1 : Nat) < 2 ^ 1 by decide) hδ1
      simp [h1δ]
    have hf := hsp 0 δ hδ1 hδr hd0
    simp only [Nat.zero_add] at hf
    rw [hf] at hdδ; simp at hdδ
  · -- `carryInMask x (c.mS * d) < 2^(c.r + δ + 1) ≤ (2^(c.r+1) - 2) * d`!
    rw [hd_val]
    have hp_lt : p < 2 ^ (c.r + δ + 1) := by
      rw [hp_val, Nat.pow_succ]
      have hlt_pow : 2 ^ c.r < 2 ^ (c.r + δ) := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have hx_lt : x < 2 ^ (c.r + δ + 1) := by omega
    have hmd_lt : c.mS * (2 ^ δ + 1) < 2 ^ (c.r + δ + 1) := by omega
    have hK_lt : carryInMask x (c.mS * (2 ^ δ + 1)) < 2 ^ (c.r + δ + 1) := by
      unfold carryInMask
      rw [← hp_eq_add]
      exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hp_lt hx_lt) hmd_lt
    have hRHS_ge : 2 ^ (c.r + δ + 1) ≤ (2 ^ (c.r + 1) - 2) * (2 ^ δ + 1) := by
      have h2r : 2 ^ (c.r + 1) ≥ 4 := by
        have := Nat.pow_le_pow_right (by omega : 2 ≥ 1) (show c.r + 1 ≥ 2 by omega); omega
      have h2δ_le : 2 ^ δ ≤ 2 ^ (c.r - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2r_eq : 2 ^ c.r = 2 * 2 ^ (c.r - 1) := by
        have : c.r = (c.r - 1) + 1 := by omega
        conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
      have hprod : (2 ^ (c.r + 1) - 2) * (2 ^ δ + 1) + 2 * (2 ^ δ + 1) = 2 ^ (c.r + 1) * (2 ^ δ + 1) := by
        rw [← Nat.add_mul, show 2 ^ (c.r + 1) - 2 + 2 = 2 ^ (c.r + 1) by omega]
      have hexp : 2 ^ (c.r + 1) * (2 ^ δ + 1) = 2 ^ (c.r + δ + 1) + 2 ^ (c.r + 1) := by
        rw [Nat.mul_add, Nat.mul_one, ← Nat.pow_add]
        have heq : c.r + 1 + δ = c.r + δ + 1 := by omega
        rw [heq]
      have hgap : 2 * (2 ^ δ + 1) ≤ 2 ^ (c.r + 1) := by
        rw [Nat.pow_succ]; omega
      omega
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hK_lt hRHS_ge)

/-- **THE DIFFERENCE-BASIS CARRY-BRIDGE DICHOTOMY THEOREM (EXACT IFF):**
    For EVERY valid finite recurrence certificate `c : RecCert`, `c` is a difference basis
    IF AND ONLY IF every `S`-rewrite derivation obeys `r`-spacing and the universal binary
    carry-eigenvalue law `carryInMask x (c.mS * d) = (2^(c.r+1) - 2) * d`! -/
theorem difference_basis_carry_bridge_dichotomy {c : RecCert} (hv : c.isValid = true) :
    c.isDiffBasis = true ↔
      ∀ ks x p, SRewriteDeriv c ks x p →
        let d := sumPow2 ks
        isRSpaced c.r d ∧ carryInMask x (c.mS * d) = (2 ^ (c.r + 1) - 2) * d := by
  constructor
  · intro hdb ks x p hd
    have h := diff_basis_implies_all_laws hdb hd
    exact ⟨h.2.1, h.2.2.2.1⟩
  · intro hall
    cases hdb : c.isDiffBasis
    · exfalso
      obtain ⟨ks, x, p, hd, hnsp, _⟩ := not_diff_basis_refutation hv hdb
      exact hnsp (hall ks x p hd).1
    · rfl

/-! ## Section 4: Universal r-Bonacci Pure-Binary Characterization & Automatic r-Spacing (ALL r ≥ 2) -/

theorem rBonacciCert_mS (r : Nat) : (rBonacciCert r).mS = 1 := by
  dsimp only [rBonacciCert, RecCert.mS]
  have : 2 ^ r ≥ 1 := Nat.one_le_two_pow
  omega

theorem rBonacciCert_isValid {r : Nat} (hr : r ≥ 2) : (rBonacciCert r).isValid = true := by
  unfold rBonacciCert RecCert.isValid
  have h2r : 2 ^ r ≥ 4 := by
    have := Nat.pow_le_pow_right (by omega : 2 ≥ 1) hr; omega
  have heven : 2 ^ r % 2 = 0 := by
    cases r with | zero => omega | succ k => rw [Nat.pow_succ]; omega
  have hodd : (2 ^ r - 1) % 2 = 1 := by omega
  simp [hr, hodd, show 2 ^ r - 1 < 2 ^ r by omega]

theorem rBonacciCert_isDiffBasis {r : Nat} (hr : r ≥ 2) : (rBonacciCert r).isDiffBasis = true := by
  unfold RecCert.isDiffBasis
  rw [rBonacciCert_isValid hr, Bool.true_and, List.all_eq_true]
  intro t htmem
  have ht : t < r - 1 := List.mem_range.mp htmem
  rw [bne_iff_ne]
  intro hzero
  have h0 := congrArg (fun n => n.testBit 0) hzero
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_zero, Nat.zero_testBit] at h0
  simp only [rBonacciCert, Nat.testBit_two_pow_sub_one] at h0
  have h1 : 0 < r := by omega
  have h2 : t + 1 < r := by omega
  simp [h1, h2] at h0

/-! ### 4.1 Automatic `r`-Spacing from the Carry-Eigenvalue Equation Alone (`m_S = 1`) -/

/-- **AUTOMATIC `r`-SPACING THEOREM:**
    For ALL `r ≥ 2` and ALL `x, d : Nat`, the binary carry-eigenvalue equation
    `carryInMask x d = (2^(r+1) - 2) * d` ALONE forces `d` to be `r`-spaced! -/
theorem automatic_r_spacing {r : Nat} (hr : r ≥ 2) :
    ∀ d x, carryInMask x d = (2 ^ (r + 1) - 2) * d → isRSpaced r d := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro x hcarry
    by_cases hd0 : d = 0
    · subst hd0; intro i j _ _ h; simp at h
    · by_cases hpar : d % 2 = 0
      · -- Even `d = 2 * d'`: shift right by 1 preserves carry-eigenvalue equation
        have hlt : d / 2 < d := by omega
        have hc_div : carryInMask (x / 2) (d / 2) = (2 ^ (r + 1) - 2) * (d / 2) := by
          apply Nat.eq_of_testBit_eq; intro i
          rw [carryInMask_testBit]
          have hcb_shift : carryBit (x / 2) (d / 2) i = carryBit x d (i + 1) := by
            have h1 := carryBitWith_succ_shift x d false i
            have hd_bit0 : d.testBit 0 = false := by rw [testBit_zero_eq, hpar]; rfl
            simp only [hd_bit0, Bool.and_false, Bool.or_false] at h1
            exact h1
          rw [hcb_shift, ← carryInMask_testBit, hcarry, testBit_succ_eq]
          have hdiv_eq : ((2 ^ (r + 1) - 2) * d) / 2 = (2 ^ (r + 1) - 2) * (d / 2) := by
            have hd2 : d = 2 * (d / 2) := by omega
            conv => lhs; rw [hd2, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (r + 1) - 2) 2, Nat.mul_assoc]
            omega
          rw [hdiv_eq]
        have hsp' := ih (d / 2) hlt (x / 2) hc_div
        intro i j hj1 hjr hdi
        cases i with
        | zero => rw [testBit_zero_eq, hpar] at hdi; simp at hdi
        | succ k =>
          rw [testBit_succ_eq] at hdi
          have heq : k + 1 + j = (k + j) + 1 := by omega
          rw [heq, testBit_succ_eq]
          exact hsp' k j hj1 hjr hdi
      · -- Odd `d`: first prove bits `1, ..., r - 1` of `d` are ALL `false`!
        have hodd : d % 2 = 1 := by omega
        have hlow_zero : ∀ j, 1 ≤ j → j < r → d.testBit j = false := by
          intro j hj1 hjr
          -- Strong induction on `j` so `j` is the smallest index ≥ 1 with `d.testBit j = true`!
          induction j using Nat.strongRecOn with
          | ind m ihm =>
            cases hdm : d.testBit m
            · rfl
            · exfalso
              -- All bits `1 .. m-1` are `false`, bit `0` is `true`, bit `m` is `true`:
              -- therefore `d % 2^(m+1) = 1 + 2^m`!
              have hd_mod : d % 2 ^ (m + 1) = 1 + 2 ^ m := by
                apply Nat.eq_of_testBit_eq; intro i
                rw [Nat.testBit_mod_two_pow]
                have h1m_and : (1 &&& (2 ^ m)) = 0 := by
                  apply Nat.eq_of_testBit_eq; intro t
                  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
                  cases t with
                  | zero => simp [show m ≠ 0 by omega]
                  | succ s => rw [testBit_false_of_lt_two_pow (show (1 : Nat) < 2 ^ 1 by decide) (by omega)]; simp
                rw [add_eq_xor_of_and_zero h1m_and, Nat.testBit_xor, Nat.testBit_two_pow]
                by_cases hi : i < m + 1
                · simp only [decide_eq_true hi, Bool.true_and]
                  cases i with
                  | zero =>
                    have hne : m ≠ 0 := by omega
                    have h10 : (1 : Nat).testBit 0 = true := by decide
                    rw [testBit_zero_eq, hodd]; simp [hne, h10]
                  | succ s =>
                    have h1s : (1 : Nat).testBit (s + 1) = false :=
                      testBit_false_of_lt_two_pow (show (1 : Nat) < 2 ^ 1 by decide) (by omega)
                    rw [h1s, Bool.false_xor]
                    by_cases hms : m = s + 1
                    · rw [← hms]; simp [hdm]
                    · simp only [decide_eq_false hms]
                      exact ihm (s + 1) (by omega) (by omega) (by omega)
                · simp only [decide_eq_false hi, Bool.false_and]
                  have h1i : (1 : Nat).testBit i = false :=
                    testBit_false_of_lt_two_pow (show (1 : Nat) < 2 ^ 1 by decide) (by omega)
                  have hne : m ≠ i := by omega
                  simp [h1i, hne]
              -- Write `d = (1 + 2^m) + 2^(m+1) * q`, and reduce `(2^(r+1) - 2) * d` mod `2^(m+2)`!
              let q := d / 2 ^ (m + 1)
              have hd_dec : d = (1 + 2 ^ m) + 2 ^ (m + 1) * q := by
                have := Nat.div_add_mod d (2 ^ (m + 1)); dsimp only [q]; omega
              have hmod_eig : ((2 ^ (r + 1) - 2) * d) % 2 ^ (m + 2) = 2 ^ (m + 1) - 2 := by
                have hdiv_r : 2 ^ (m + 2) ∣ 2 ^ (r + 1) := by
                  refine ⟨2 ^ (r + 1 - (m + 2)), ?_⟩
                  rw [← Nat.pow_add]; congr 1; omega
                obtain ⟨A, hA⟩ := hdiv_r
                have hA_pos : A ≥ 1 := by
                  have : 2 ^ (r + 1) ≥ 1 := Nat.one_le_two_pow
                  cases A with | zero => simp at hA | succ _ => omega
                have h2m2 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
                have h2m1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
                have h2m_pos : 2 ^ m ≥ 2 := by
                  have := Nat.pow_le_pow_right (by omega : 2 ≥ 1) hj1; omega
                have hmul_eq : (2 ^ (r + 1) - 2) * d =
                    (2 ^ (m + 1) - 2) + 2 ^ (m + 2) * (A * (1 + 2 ^ m) - 1 + (2 ^ r - 1) * q) := by
                  have h2r1 : 2 ^ (r + 1) - 2 = 2 * (2 ^ r - 1) := by
                    have : 2 ^ r ≥ 1 := Nat.one_le_two_pow; rw [Nat.pow_succ]; omega
                  have hq_term : (2 ^ (r + 1) - 2) * (2 ^ (m + 1) * q) = 2 ^ (m + 2) * ((2 ^ r - 1) * q) := by
                    rw [h2r1, h2m2]; ac_rfl
                  have hlow_term : (2 ^ (r + 1) - 2) * (1 + 2 ^ m) =
                      (2 ^ (m + 1) - 2) + 2 ^ (m + 2) * (A * (1 + 2 ^ m) - 1) := by
                    have h2rp1_ge : 2 ^ (r + 1) ≥ 2 := by
                      have : 2 ^ r ≥ 1 := Nat.one_le_two_pow; rw [Nat.pow_succ]; omega
                    have h1 : (2 ^ (r + 1) - 2) * (1 + 2 ^ m) + 2 * (1 + 2 ^ m) = 2 ^ (r + 1) * (1 + 2 ^ m) := by
                      rw [← Nat.add_mul, show 2 ^ (r + 1) - 2 + 2 = 2 ^ (r + 1) by omega]
                    have h2 : 2 ^ (r + 1) * (1 + 2 ^ m) = 2 ^ (m + 2) * (A * (1 + 2 ^ m)) := by
                      rw [hA, Nat.mul_assoc]
                    have h3 : 2 ^ (m + 2) * (A * (1 + 2 ^ m)) = 2 ^ (m + 2) * (A * (1 + 2 ^ m) - 1) + 2 ^ (m + 2) := by
                      have hpos : A * (1 + 2 ^ m) ≥ 1 := by
                        have := Nat.mul_le_mul hA_pos (show 1 ≤ 1 + 2 ^ m by omega); omega
                      conv => lhs; rw [show A * (1 + 2 ^ m) = (A * (1 + 2 ^ m) - 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
                    omega
                  rw [hd_dec, Nat.mul_add, hlow_term, hq_term, Nat.add_assoc, ← Nat.mul_add]
                rw [hmul_eq, Nat.add_mul_mod_self_left]
                exact Nat.mod_eq_of_lt (by omega)
              -- Extract bit `m` (= `true`) and bit `m+1` (= `false`) from `hmod_eig`!
              have hcm : carryBit x d m = true := by
                rw [← carryInMask_testBit, hcarry]
                have htb := congrArg (fun n => n.testBit m) hmod_eig
                rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega), Bool.true_and, eigMask_testBit] at htb
                rw [htb]; exact decide_eq_true (by omega)
              have hcm1 : carryBit x d (m + 1) = false := by
                rw [← carryInMask_testBit, hcarry]
                have htb := congrArg (fun n => n.testBit (m + 1)) hmod_eig
                rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega), Bool.true_and, eigMask_testBit] at htb
                rw [htb]; exact decide_eq_false (by omega)
              -- Contradiction: `d.testBit m = true` AND `carryBit x d m = true` FORCES `carryBit x d (m + 1) = true`!
              simp only [carryBit, carryBitWith] at hcm hcm1
              rw [hdm, hcm] at hcm1
              simp at hcm1
        -- Now `d = 1 + 2^r * d''`! Show `∃ x', carryInMask x' (d / 2^r) = (2^(r+1) - 2) * (d / 2^r)`!
        let d'' := d / 2 ^ r
        have hd_dec : d = 1 + 2 ^ r * d'' := by
          have hmod : d % 2 ^ r = 1 := by
            apply Nat.eq_of_testBit_eq; intro i
            rw [Nat.testBit_mod_two_pow]
            by_cases hi : i < r
            · simp only [decide_eq_true hi, Bool.true_and]
              cases i with
              | zero => rw [testBit_zero_eq, hodd]; decide
              | succ s =>
                rw [hlow_zero (s + 1) (by omega) hi,
                    testBit_false_of_lt_two_pow (show (1 : Nat) < 2 ^ 1 by decide) (by omega)]
            · simp only [decide_eq_false hi, Bool.false_and]
              have h1lt : (1 : Nat) < 2 ^ r := by
                have := Nat.pow_le_pow_right (by omega : 2 ≥ 1) hr; omega
              exact (testBit_false_of_lt_two_pow h1lt (by omega)).symm
          have := Nat.div_add_mod d (2 ^ r); dsimp only [d'']; omega
        have heig_dec : (2 ^ (r + 1) - 2) * d = (2 ^ (r + 1) - 2) + 2 ^ r * ((2 ^ (r + 1) - 2) * d'') := by
          conv => lhs; rw [hd_dec, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc,
                           Nat.mul_comm (2 ^ (r + 1) - 2) (2 ^ r), Nat.mul_assoc]
        -- Notice bits `r + i` (`i ≥ 1`) of `(2^(r+1) - 2) * d` equal bits `i` of `(2^(r+1) - 2) * d''`!
        have heig_hi : ∀ i, 1 ≤ i → ((2 ^ (r + 1) - 2) * d).testBit (r + i) = ((2 ^ (r + 1) - 2) * d'').testBit i := by
          intro i hi1
          have heq1 : (2 ^ (r + 1) - 2) * d = (2 ^ (r + 1) - 2) ^^^ (2 ^ r * ((2 ^ (r + 1) - 2) * d'')) := by
            rw [heig_dec]
            apply add_eq_xor_of_and_zero
            apply Nat.eq_of_testBit_eq; intro t
            rw [Nat.testBit_and, eigMask_testBit, Nat.zero_testBit]
            have hmul_tb : (2 ^ r * ((2 ^ (r + 1) - 2) * d'')).testBit t =
                if t < r then false else ((2 ^ (r + 1) - 2) * d'').testBit (t - r) := by
              have := Nat.testBit_two_pow_mul_add ((2 ^ (r + 1) - 2) * d'') (Nat.two_pow_pos r) t
              simpa using this
            rw [hmul_tb]
            by_cases htr : t < r
            · simp [htr]
            · by_cases hteq : t = r
              · rw [hteq]
                simp only [Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, testBit_zero_eq]
                have hev : ((2 ^ (r + 1) - 2) * d'') % 2 = 0 := by
                  have h2 : 2 ^ (r + 1) - 2 = 2 * (2 ^ r - 1) := by
                    have : 2 ^ r ≥ 1 := Nat.one_le_two_pow; rw [Nat.pow_succ]; omega
                  rw [h2, Nat.mul_assoc]; omega
                simp [hev]
              · simp [decide_eq_false (by omega : ¬(1 ≤ t ∧ t ≤ r))]
          rw [heq1, Nat.testBit_xor, eigMask_testBit, decide_eq_false (by omega : ¬(1 ≤ r + i ∧ r + i ≤ r)),
              Bool.false_xor]
          have hmul_tb := Nat.testBit_two_pow_mul_add ((2 ^ (r + 1) - 2) * d'') (Nat.two_pow_pos r) (r + i)
          simp only [Nat.add_zero] at hmul_tb
          rw [hmul_tb]
          simp [show ¬(r + i < r) by omega, show r + i - r = i by omega]
        -- Choose `x' := if d'' % 2 = 0 then x / 2^r else (x / 2^r) ||| 1`!
        let x' := if d'' % 2 = 0 then x / 2 ^ r else (x / 2 ^ r) ||| 1
        have hcarry' : carryInMask x' d'' = (2 ^ (r + 1) - 2) * d'' := by
          -- Show `carryBit x' d'' i = ((2^(r+1) - 2) * d'').testBit i` for all `i`!
          have hcb_eq : ∀ i, carryBit x' d'' i = ((2 ^ (r + 1) - 2) * d'').testBit i := by
            intro i
            cases i with
            | zero =>
              have hev : ((2 ^ (r + 1) - 2) * d'') % 2 = 0 := by
                have h2 : 2 ^ (r + 1) - 2 = 2 * (2 ^ r - 1) := by
                  have : 2 ^ r ≥ 1 := Nat.one_le_two_pow; rw [Nat.pow_succ]; omega
                rw [h2, Nat.mul_assoc]; omega
              rw [testBit_zero_eq, hev]; rfl
            | succ k =>
              -- Show by induction on `k` that `carryBit x' d'' (k + 1) = carryBit x d (r + k + 1)`!
              suffices hshift : carryBit x' d'' (k + 1) = carryBit x d (r + (k + 1)) by
                rw [hshift, ← carryInMask_testBit, hcarry, heig_hi (k + 1) (by omega)]
              induction k with
              | zero =>
                -- Check `carryBit x' d'' 1 = carryBit x d (r + 1)`!
                have hcr : carryBit x d r = true := by
                  rw [← carryInMask_testBit, hcarry]
                  -- Bit `r` of `(2^(r+1) - 2) * d` is `true`!
                  have hdiv_tb : ((2 ^ (r + 1) - 2) * d) % 2 ^ (r + 1) = 2 ^ (r + 1) - 2 := by
                    rw [heig_dec]
                    have hmul_even : 2 ^ (r + 1) ∣ 2 ^ r * ((2 ^ (r + 1) - 2) * d'') := by
                      have h2 : 2 ^ (r + 1) - 2 = 2 * (2 ^ r - 1) := by
                        have : 2 ^ r ≥ 1 := Nat.one_le_two_pow; rw [Nat.pow_succ]; omega
                      refine ⟨(2 ^ r - 1) * d'', ?_⟩
                      rw [h2, Nat.pow_succ]; ac_rfl
                    obtain ⟨B, hB⟩ := hmul_even
                    rw [hB, Nat.add_mul_mod_self_left]
                    have h2rp1_ge : 2 ^ (r + 1) ≥ 2 := by
                      have : 2 ^ r ≥ 1 := Nat.one_le_two_pow; rw [Nat.pow_succ]; omega
                    exact Nat.mod_eq_of_lt (by omega)
                  have htb := congrArg (fun n => n.testBit r) hdiv_tb
                  rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega), Bool.true_and, eigMask_testBit] at htb
                  rw [htb]; exact decide_eq_true (by omega)
                have hcr1 : carryBit x d (r + 1) = (d''.testBit 0) := by
                  rw [← carryInMask_testBit, hcarry, heig_hi 1 (by omega)]
                  have h2 : (2 ^ (r + 1) - 2) * d'' = 2 * ((2 ^ r - 1) * d'') := by
                    have : 2 ^ r ≥ 1 := Nat.one_le_two_pow
                    rw [Nat.pow_succ, ← Nat.mul_assoc]
                    have : 2 ^ r * 2 - 2 = 2 * (2 ^ r - 1) := by omega
                    rw [this, Nat.mul_assoc]
                  rw [h2, testBit_succ_eq]
                  have hdiv : (2 * ((2 ^ r - 1) * d'')) / 2 = (2 ^ r - 1) * d'' := by omega
                  rw [hdiv, testBit_zero_eq, testBit_zero_eq, Nat.mul_mod]
                  have h2rmod : (2 ^ r - 1) % 2 = 1 := by
                    have hev : 2 ^ r % 2 = 0 := by
                      cases hreq : r with | zero => omega | succ t => rw [Nat.pow_succ]; omega
                    have : 2 ^ r ≥ 1 := Nat.one_le_two_pow; omega
                  rw [h2rmod, Nat.one_mul, Nat.mod_mod]
                rw [hcr1]
                simp only [carryBit, carryBitWith, Bool.and_false, Bool.or_false]
                by_cases hd''p : d'' % 2 = 0
                · have hdb0 : d''.testBit 0 = false := by rw [testBit_zero_eq, hd''p]; rfl
                  simp [hdb0]
                · have hd''o : d'' % 2 = 1 := by omega
                  have hdb0 : d''.testBit 0 = true := by rw [testBit_zero_eq, hd''o]; rfl
                  have hx'0 : x'.testBit 0 = true := by
                    dsimp only [x']; simp [hd''p]
                  simp [hdb0, hx'0]
              | succ m ihm =>
                have hx_bit : x'.testBit (m + 1) = x.testBit (r + (m + 1)) := by
                  have hdiv : (x / 2 ^ r).testBit (m + 1) = x.testBit (r + (m + 1)) := by
                    rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
                  dsimp only [x']
                  by_cases hp : d'' % 2 = 0
                  · simp [hp, hdiv]
                  · simp only [hp, ↓reduceIte, Nat.testBit_or, hdiv]
                    rw [testBit_false_of_lt_two_pow (show (1 : Nat) < 2 ^ 1 by decide) (by omega), Bool.or_false]
                have hd_bit : d''.testBit (m + 1) = d.testBit (r + (m + 1)) := by
                  dsimp only [d'']; rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
                have hidx : r + (m + 1 + 1) = (r + (m + 1)) + 1 := by omega
                rw [hidx]
                simp only [carryBit, carryBitWith] at ihm ⊢
                rw [hx_bit, hd_bit, ihm]
          apply Nat.eq_of_testBit_eq; intro i
          rw [carryInMask_testBit, hcb_eq i]
        have h2r : 2 ^ r ≥ 2 := by
          have := Nat.pow_le_pow_right (by omega : 2 ≥ 1) (show r ≥ 1 by omega); omega
        have hlt_d'' : d'' < d := Nat.div_lt_self (by omega) h2r
        have hsp_d'' : isRSpaced r d'' := ih d'' hlt_d'' x' hcarry'
        -- Combine `hlow_zero` with `hsp_d''` to get `isRSpaced r d`!
        intro i j hj1 hjr hdi
        by_cases hir : i < r
        · have hi0 : i = 0 := by
            cases i with
            | zero => rfl
            | succ s => rw [hlow_zero (s + 1) (by omega) hir] at hdi; simp at hdi
          subst hi0; simp only [Nat.zero_add]; exact hlow_zero j hj1 hjr
        · have hdi'' : d''.testBit (i - r) = true := by
            dsimp only [d'']; rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
            have : r + (i - r) = i := by omega
            rw [this]; exact hdi
          have hf := hsp_d'' (i - r) j hj1 hjr hdi''
          dsimp only [d''] at hf
          rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight] at hf
          have : r + (i - r + j) = i + j := by omega
          rw [this] at hf; exact hf

/-! ### 4.2 Canonical `r`-Bonacci Weights, Uniqueness & Existence of Normalization -/

theorem rBonacciWeight_lt {r n : Nat} (h : n < r) : rBonacciWeight r n = 2 ^ n := by
  conv => lhs; unfold rBonacciWeight
  simp [h]

theorem rBonacciWeight_ge {r k : Nat} :
    rBonacciWeight r (k + r) = sumNat r (fun j => rBonacciWeight r (k + j)) := by
  conv => lhs; unfold rBonacciWeight
  have hnot : ¬(k + r < r) := by omega
  simp only [hnot, ↓reduceDIte]
  apply sumNat_congr; intro j hjr
  simp [hjr]

theorem rBonacciWeight_obeysRecInt {r : Nat} (_hr : r ≥ 2) :
    ObeysRecInt (rBonacciCert r) (fun k => (rBonacciWeight r k : Int)) := by
  intro k
  simp only [rBonacciCert]
  rw [rBonacciWeight_ge]
  have hcast : ∀ n (f : Nat → Nat), (sumNat n f : Int) = sumInt n (fun j => (f j : Int)) := by
    intro n f; induction n with | zero => rfl | succ m ihm => simp only [sumNat, sumInt]; omega
  rw [hcast]
  apply sumInt_congr; intro j hjr
  have htb : (2 ^ r - 1).testBit j = true := by
    rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hjr
  simp [htb]

theorem evalRecInt_ofNat (G : Nat → Nat) (x : Nat) :
    evalRecInt (fun k => (G k : Int)) x = (evalRecNat G x : Int) := by
  induction x using Nat.strongRecOn generalizing G with
  | ind x ih =>
    by_cases hx0 : x = 0
    · subst hx0; simp [evalRecInt_zero, evalRecNat_zero]
    · conv => lhs; unfold evalRecInt
      conv => rhs; unfold evalRecNat
      simp only [hx0, ↓reduceIte]
      have hih := ih (x / 2) (by omega) (fun k => G (k + 1))
      by_cases hpar : x % 2 = 1 <;> simp only [hpar, ↓reduceIte] <;> omega

/-- Key canonical bound: if `p < 2^n` has no `r` consecutive 1-bits, then `evalRecNat (rBonacciWeight r) p < rBonacciWeight r n`. -/
theorem evalRecNat_lt_rBonacciWeight {r : Nat} (_hr : r ≥ 2) :
    ∀ n p, p < 2 ^ n → noROnes r p → evalRecNat (rBonacciWeight r) p < rBonacciWeight r n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro p hpn hno
    by_cases hnr : n < r
    · rw [evalRecNat_eq_sumNat _ p n hpn, rBonacciWeight_lt hnr]
      have hbin : ∀ m x, m ≤ r → x < 2 ^ m → sumNat m (fun i => b2n (x.testBit i) * rBonacciWeight r i) = x := by
        intro m
        induction m with
        | zero => intro x _ hx; simp at hx; subst hx; rfl
        | succ k ihk =>
          intro x hkr hx
          have hmod_lt : x % 2 ^ k < 2 ^ k := Nat.mod_lt x (Nat.two_pow_pos k)
          simp only [sumNat]
          have hlow : sumNat k (fun i => b2n (x.testBit i) * rBonacciWeight r i) =
                      sumNat k (fun i => b2n ((x % 2 ^ k).testBit i) * rBonacciWeight r i) := by
            apply sumNat_congr; intro i hik
            rw [Nat.testBit_mod_two_pow, decide_eq_true hik, Bool.true_and]
          rw [hlow, ihk (x % 2 ^ k) (by omega) hmod_lt, rBonacciWeight_lt (by omega)]
          have hdiv_lt : x / 2 ^ k < 2 :=
            Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ] at hx; omega)
          have hdiv_bit : b2n (x.testBit k) = x / 2 ^ k := by
            have htb : x.testBit k = (x / 2 ^ k).testBit 0 := by
              rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight, Nat.add_zero]
            rw [htb, b2n_testBit_zero, Nat.mod_eq_of_lt hdiv_lt]
          rw [hdiv_bit]
          have hdm := Nat.div_add_mod x (2 ^ k)
          rw [Nat.mul_comm] at hdm; omega
      rw [hbin n p (by omega) hpn]; exact hpn
    · obtain ⟨j0, hj0r, hj0f⟩ := hno (n - r)
      let m := n - r + j0
      have hm_lt : m < n := by omega
      have hlo_lt : p % 2 ^ m < 2 ^ m := Nat.mod_lt p (Nat.two_pow_pos m)
      have hlo_no : noROnes r (p % 2 ^ m) := by
        intro i
        obtain ⟨j, hjr, hjf⟩ := hno i
        refine ⟨j, hjr, ?_⟩
        rw [Nat.testBit_mod_two_pow]
        simp [hjf]
      have hlo_bound := ih m hm_lt (p % 2 ^ m) hlo_lt hlo_no
      rw [evalRecNat_eq_sumNat _ p n hpn]
      rw [evalRecNat_eq_sumNat _ (p % 2 ^ m) m hlo_lt] at hlo_bound
      have hsplit : ∀ A B (f : Nat → Nat), A ≤ B →
          sumNat B f = sumNat A f + sumNat (B - A) (fun t => f (A + t)) := by
        intro A B f hAB
        induction B with
        | zero =>
          have hA0 : A = 0 := by omega
          rw [hA0]; rfl
        | succ k ihk =>
          by_cases hAk : A = k + 1
          · subst hAk; simp [sumNat]
          · have hsub : k + 1 - A = (k - A) + 1 := by omega
            have hadd : A + (k - A) = k := by omega
            simp only [sumNat, hsub, hadd, ihk (by omega)]; omega
      rw [hsplit m n _ (by omega)]
      have hlo_eq : sumNat m (fun i => b2n (p.testBit i) * rBonacciWeight r i) =
                    sumNat m (fun i => b2n ((p % 2 ^ m).testBit i) * rBonacciWeight r i) := by
        apply sumNat_congr; intro i him
        rw [Nat.testBit_mod_two_pow, decide_eq_true him, Bool.true_and]
      rw [hlo_eq]
      have hhi_le : sumNat (n - m) (fun t => b2n (p.testBit (m + t)) * rBonacciWeight r (m + t)) +
                    rBonacciWeight r m ≤
                    sumNat (n - m) (fun t => rBonacciWeight r (m + t)) := by
        have hnm_eq : n - m = (n - m - 1) + 1 := by omega
        rw [hnm_eq, sumNat_succ_shift, sumNat_succ_shift]
        have hpmf : p.testBit (m + 0) = false := by simpa [m] using hj0f
        rw [hpmf, b2n_false, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
        have htail_le : sumNat (n - m - 1) (fun t => b2n (p.testBit (m + (t + 1))) * rBonacciWeight r (m + (t + 1))) ≤
                        sumNat (n - m - 1) (fun t => rBonacciWeight r (m + (t + 1))) := by
          clear hlo_bound hlo_eq hsplit
          induction (n - m - 1) with
          | zero => exact Nat.le_refl 0
          | succ k ihk =>
            simp only [sumNat]
            have h1 : b2n (p.testBit (m + (k + 1))) * rBonacciWeight r (m + (k + 1)) ≤ rBonacciWeight r (m + (k + 1)) := by
              cases p.testBit (m + (k + 1)) <;> simp
            omega
        omega
      -- And `sumNat (n - m) (fun t => G (m + t)) ≤ sumNat r (fun j => G ((n - r) + j)) = G n`!
      have hrec_eq : rBonacciWeight r n = sumNat r (fun j => rBonacciWeight r ((n - r) + j)) := by
        have hn_eq : n = (n - r) + r := by omega
        conv => lhs; rw [hn_eq, rBonacciWeight_ge]
      rw [hrec_eq, hsplit j0 r (fun j => rBonacciWeight r ((n - r) + j)) (by omega)]
      have htail_eq : sumNat (r - j0) (fun t => rBonacciWeight r (n - r + (j0 + t))) =
                      sumNat (n - m) (fun t => rBonacciWeight r (m + t)) := by
        have hlen : r - j0 = n - m := by omega
        rw [hlen]
        apply sumNat_congr; intro t _
        have : n - r + (j0 + t) = m + t := by omega
        rw [this]
      rw [htail_eq]
      omega

/-- **CANONICAL `r`-BONACCI UNIQUENESS THEOREM (ALL `r ≥ 2`):**
    Two canonical `r`-Zeckendorf bitmasks with the same `r`-bonacci value MUST be equal! -/
theorem rbonacci_uniqueness {r : Nat} (hr : r ≥ 2) {p₁ p₂ : Nat}
    (h1 : noROnes r p₁) (h2 : noROnes r p₂)
    (heval : evalRecNat (rBonacciWeight r) p₁ = evalRecNat (rBonacciWeight r) p₂) :
    p₁ = p₂ := by
  obtain ⟨N1, hN1⟩ := exists_lt_two_pow p₁
  obtain ⟨N2, hN2⟩ := exists_lt_two_pow p₂
  let N := max N1 N2
  have hp1 : p₁ < 2 ^ N := Nat.lt_of_lt_of_le hN1 (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
  have hp2 : p₂ < 2 ^ N := Nat.lt_of_lt_of_le hN2 (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
  -- Induct on `N`!
  suffices ∀ M a b, a < 2 ^ M → b < 2 ^ M → noROnes r a → noROnes r b →
      evalRecNat (rBonacciWeight r) a = evalRecNat (rBonacciWeight r) b → a = b from
    this N p₁ p₂ hp1 hp2 h1 h2 heval
  intro M
  induction M with
  | zero => intro a b ha hb _ _ _; simp at ha hb; omega
  | succ k ih =>
    intro a b ha hb hna hnb hev
    -- Compare top bit `k` of `a` and `b`!
    have hsplit_top : ∀ x, x < 2 ^ (k + 1) →
        evalRecNat (rBonacciWeight r) x =
          evalRecNat (rBonacciWeight r) (x % 2 ^ k) + b2n (x.testBit k) * rBonacciWeight r k := by
      intro x hx
      have hmod_lt : x % 2 ^ k < 2 ^ k := Nat.mod_lt x (Nat.two_pow_pos k)
      rw [evalRecNat_eq_sumNat _ x (k + 1) hx, evalRecNat_eq_sumNat _ (x % 2 ^ k) k hmod_lt]
      simp only [sumNat]
      congr 1
      apply sumNat_congr; intro i hik
      rw [Nat.testBit_mod_two_pow, decide_eq_true hik, Bool.true_and]
    have hno_mod : ∀ x, noROnes r x → noROnes r (x % 2 ^ k) := by
      intro x hx i
      obtain ⟨j, hjr, hjf⟩ := hx i
      exact ⟨j, hjr, by rw [Nat.testBit_mod_two_pow]; simp [hjf]⟩
    have hmod_a_lt : a % 2 ^ k < 2 ^ k := Nat.mod_lt a (Nat.two_pow_pos k)
    have hmod_b_lt : b % 2 ^ k < 2 ^ k := Nat.mod_lt b (Nat.two_pow_pos k)
    have hbd_a := evalRecNat_lt_rBonacciWeight hr k (a % 2 ^ k) hmod_a_lt (hno_mod a hna)
    have hbd_b := evalRecNat_lt_rBonacciWeight hr k (b % 2 ^ k) hmod_b_lt (hno_mod b hnb)
    rw [hsplit_top a ha, hsplit_top b hb] at hev
    have hbit_eq : a.testBit k = b.testBit k := by
      cases hta : a.testBit k <;> cases htb : b.testBit k <;> simp [hta, htb] at hev ⊢ <;> omega
    have hmod_eq : a % 2 ^ k = b % 2 ^ k := by
      apply ih (a % 2 ^ k) (b % 2 ^ k) hmod_a_lt hmod_b_lt (hno_mod a hna) (hno_mod b hnb)
      rw [hbit_eq] at hev; omega
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hik : i < k
    · have := congrArg (fun n => n.testBit i) hmod_eq
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, decide_eq_true hik, Bool.true_and, Bool.true_and] at this
      exact this
    · by_cases hieq : i = k
      · subst hieq; exact hbit_eq
      · rw [testBit_false_of_lt_two_pow ha (by omega), testBit_false_of_lt_two_pow hb (by omega)]

/-- **EXISTENCE OF CANONICAL `r`-BONACCI NORMALIZATION BY POPCOUNT DESCENT (ALL `r ≥ 2`):**
    Every `x : Nat` reaches a canonical `noROnes r p` bitmask via a finite `r`-bonacci rewrite derivation! -/
theorem rbonacci_normalization_exists {r : Nat} (hr : r ≥ 2) :
    ∀ x, ∃ ks p, SRewriteDeriv (rBonacciCert r) ks x p ∧ noROnes r p := by
  intro x
  suffices ∀ m x, popcount x = m → ∃ ks p, SRewriteDeriv (rBonacciCert r) ks x p ∧ noROnes r p from
    this (popcount x) x rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro x hpop
    obtain ⟨N, hN⟩ := exists_lt_two_pow x
    have hdec_all : ∀ i, (∀ j, j < r → x.testBit (i + j) = true) ∨ (∃ j, j < r ∧ x.testBit (i + j) = false) := by
      intro i
      suffices ∀ t, (∀ j, j < t → x.testBit (i + j) = true) ∨ (∃ j, j < t ∧ x.testBit (i + j) = false) from this r
      intro t; induction t with
      | zero => exact Or.inl (fun _ h => by omega)
      | succ s ihs =>
        rcases ihs with hall | ⟨j, hj, hf⟩
        · cases hbit : x.testBit (i + s)
          · exact Or.inr ⟨s, by omega, hbit⟩
          · exact Or.inl (fun j hj => by
              by_cases hjs : j < s
              · exact hall j hjs
              · have hjeq : j = s := by omega
                subst hjeq; exact hbit)
        · exact Or.inr ⟨j, by omega, hf⟩
    -- Find either a valid fire position `k` (all `r` bits true and bit `k+r` false) OR prove `noROnes r x`!
    have hstep_or_done :
        (∃ k, x.testBit (k + r) = false ∧ ∀ j, j < r → x.testBit (k + j) = true) ∨ noROnes r x := by
      -- Prove by induction on `L` that either there is a valid fire position `k` OR no `i < L` has all `r` bits true
      -- using the highest `k < N` with all `r` bits true (since `x.testBit t = false` for all `t ≥ N`)!
      suffices ∀ L, (∀ t, L ≤ t → (∃ j, j < r ∧ x.testBit (t + j) = false)) →
          (∃ k, x.testBit (k + r) = false ∧ ∀ j, j < r → x.testBit (k + j) = true) ∨
          (∀ i, ∃ j, j < r ∧ x.testBit (i + j) = false) by
        apply this N
        intro t ht
        exact ⟨0, by omega, by simp [testBit_false_of_lt_two_pow hN ht]⟩
      intro L
      induction L with
      | zero => intro hall; exact Or.inr (fun i => hall i (Nat.zero_le _))
      | succ s ihs =>
        intro hall_above
        rcases hdec_all s with hs_all | hs_no
        · -- `s` has all `r` bits `true`, while `s + 1` has SOME bit `j < r` `false`!
          -- Since bits `s + 1 .. s + r - 1` are all `true` (from `hs_all`), bit `(s + 1) + (r - 1) = s + r` MUST be `false`!
          obtain ⟨j0, hj0r, hj0f⟩ := hall_above (s + 1) (Nat.le_refl _)
          have hsr_f : x.testBit (s + r) = false := by
            by_cases hj_top : j0 = r - 1
            · subst hj_top
              have : s + 1 + (r - 1) = s + r := by omega
              rw [this] at hj0f; exact hj0f
            · have ht := hs_all (j0 + 1) (by omega)
              have : s + (j0 + 1) = s + 1 + j0 := by omega
              rw [this, hj0f] at ht; simp at ht
          exact Or.inl ⟨s, hsr_f, hs_all⟩
        · apply ihs
          intro t ht
          by_cases hteq : t = s
          · subst hteq; exact hs_no
          · exact hall_above t (by omega)
    rcases hstep_or_done with ⟨k, hkr_f, hall_t⟩ | hno
    · -- Fire one `r`-bonacci step at `k`!
      let x1 := x + 1 * 2 ^ k
      have hst : SRewriteStep (rBonacciCert r) k x x1 := by
        refine ⟨hkr_f, ?_, ?_⟩
        · intro j hjr _; exact hall_t j hjr
        · simp [x1, rBonacciCert_mS]
      -- Popcount strictly drops by `r - 1 ≥ 1` (by our own `diff_basis_implies_all_laws` on the 1-step derivation!)
      have hd1 : SRewriteDeriv (rBonacciCert r) [k] x x1 :=
        SRewriteDeriv.cons hst (SRewriteDeriv.nil x1)
      have hall1 := diff_basis_implies_all_laws (rBonacciCert_isDiffBasis hr) hd1
      have hpop_drop : popcount x = popcount x1 + (r - 1) := by
        have h1 := hall1.2.2.2.2.2.1
        have hpc_mask : popcount (rBonacciCert r).maskS = r := popcount_two_pow_sub_one r
        have hpc_d : popcount (sumPow2 [k]) = 1 := by
          simp only [sumPow2, Nat.add_zero]
          have : 2 ^ k = 1 <<< k := by rw [Nat.shiftLeft_eq, Nat.one_mul]
          rw [this, popcount_shiftLeft, popcount_one]
        rw [hpc_mask, hpc_d, Nat.mul_one] at h1
        exact h1
      have hlt_pop : popcount x1 < m := by omega
      obtain ⟨ks_rest, p, hd_rest, hp_no⟩ := ih (popcount x1) hlt_pop x1 rfl
      exact ⟨k :: ks_rest, p, SRewriteDeriv.cons hst hd_rest, hp_no⟩
    · exact ⟨[], x, SRewriteDeriv.nil x, hno⟩

/-! ### 4.3 The Crown Jewel: Complete Pure-Binary Characterization of `r`-Zeckendorf Normalization -/

/-- **THE UNIVERSAL `r`-BONACCI PURE-BINARY CARRY-BRIDGE THEOREM (ALL `r ≥ 2`, ALL `x, p, d : Nat`):**
    Canonical `r`-Zeckendorf normalization is COMPLETELY CHARACTERIZED in pure base-2 binary
    carry arithmetic (with ZERO reference to Fibonacci / `r`-bonacci weights!):
    `(noROnes r p ∧ evalRecNat (rBonacciWeight r) p = evalRecNat (rBonacciWeight r) x ∧ p = x + d)`
    ↔ `(noROnes r p ∧ p = x + d ∧ carryInMask x d = (2^(r+1) - 2) * d)`. -/
theorem rbonacci_pure_binary_characterization {r : Nat} (hr : r ≥ 2) (x p d : Nat) :
    (noROnes r p ∧ evalRecNat (rBonacciWeight r) p = evalRecNat (rBonacciWeight r) x ∧ p = x + d) ↔
    (noROnes r p ∧ p = x + d ∧ carryInMask x d = (2 ^ (r + 1) - 2) * d) := by
  have hv := rBonacciCert_isValid hr
  have hdb := rBonacciCert_isDiffBasis hr
  have hmS := rBonacciCert_mS r
  constructor
  · rintro ⟨hp_no, heval, hpxd⟩
    obtain ⟨ks, p', hd', hp'_no⟩ := rbonacci_normalization_exists hr x
    have hlaws := diff_basis_implies_all_laws hdb hd'
    have hrec_int := hlaws.2.2.2.2.2.2.2 (fun k => (rBonacciWeight r k : Int)) (rBonacciWeight_obeysRecInt hr)
    rw [evalRecInt_ofNat, evalRecInt_ofNat] at hrec_int
    have heval' : evalRecNat (rBonacciWeight r) p' = evalRecNat (rBonacciWeight r) x := by omega
    have hpeq : p = p' := rbonacci_uniqueness hr hp_no hp'_no (heval.trans heval'.symm)
    have hp'_add : p' = x + sumPow2 ks := by
      have h := hlaws.2.2.1; rw [hmS, Nat.one_mul] at h; exact h
    have hdeq : d = sumPow2 ks := by omega
    have hcarry : carryInMask x (sumPow2 ks) = (2 ^ (r + 1) - 2) * sumPow2 ks := by
      have h := hlaws.2.2.2.1; rw [hmS, Nat.one_mul] at h; exact h
    rw [← hdeq] at hcarry
    exact ⟨hp_no, hpxd, hcarry⟩
  · rintro ⟨hp_no, hpxd, hcarry⟩
    -- Automatic `r`-spacing from `carryInMask x d = (2^(r+1) - 2) * d` alone!
    have hsp : isRSpaced r d := automatic_r_spacing hr d x hcarry
    have hacc : TransducerAccepts (rBonacciCert r) x p d :=
      (master_carry_bridge_iff hv hsp).mpr (by rw [hmS, Nat.one_mul]; exact ⟨hpxd, hcarry⟩)
    have hsound := transducer_sound hv hacc
    have hrec_int := hsound.2.2.2.2.2.2 (fun k => (rBonacciWeight r k : Int)) (rBonacciWeight_obeysRecInt hr)
    rw [evalRecInt_ofNat, evalRecInt_ofNat] at hrec_int
    exact ⟨hp_no, by omega, hpxd⟩

/-- **COMPLETE SUITE OF COROLLARIES FOR CANONICAL `r`-BONACCI NORMALIZATION (ALL `r ≥ 2`):**
    For EVERY `r ≥ 2` and EVERY `x : Nat`, there exists a UNIQUE canonical `(p, d)` with
    `noROnes r p ∧ evalRecNat (rBonacciWeight r) p = evalRecNat (rBonacciWeight r) x ∧ p = x + d`,
    and it satisfies ALL SEVEN pure-silicon invariants simultaneously! -/
theorem rbonacci_master_invariants {r : Nat} (hr : r ≥ 2) (x : Nat) :
    ∃ p d,
      noROnes r p ∧
      evalRecNat (rBonacciWeight r) p = evalRecNat (rBonacciWeight r) x ∧
      p = x + d ∧
      isRSpaced r d ∧
      carryInMask x d = (2 ^ (r + 1) - 2) * d ∧
      p ^^^ x = clmul (2 ^ (r + 1) - 1) d ∧
      popcount x = popcount p + (r - 1) * popcount d ∧
      popcount (carryInMask x d) = r * popcount d ∧
      (∀ p' d', noROnes r p' → evalRecNat (rBonacciWeight r) p' = evalRecNat (rBonacciWeight r) x →
        p' = x + d' → p' = p ∧ d' = d) := by
  obtain ⟨ks, p, hd, hp_no⟩ := rbonacci_normalization_exists hr x
  have hlaws := diff_basis_implies_all_laws (rBonacciCert_isDiffBasis hr) hd
  have hmS := rBonacciCert_mS r
  let d := sumPow2 ks
  have hsp : isRSpaced r d := hlaws.2.1
  have hpxd : p = x + d := by have h := hlaws.2.2.1; rw [hmS, Nat.one_mul] at h; exact h
  have hcarry : carryInMask x d = (2 ^ (r + 1) - 2) * d := by
    have h := hlaws.2.2.2.1; rw [hmS, Nat.one_mul] at h; exact h
  have hclm : p ^^^ x = clmul (2 ^ (r + 1) - 1) d := by
    have h := hlaws.2.2.2.2.1
    have hpoly : (2 ^ r) ^^^ (2 ^ r - 1) = 2 ^ (r + 1) - 1 := by
      have hand : ((2 ^ r) &&& (2 ^ r - 1)) = 0 := by
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
        by_cases hi : r = i
        · subst hi; simp
        · simp [hi]
      rw [← add_eq_xor_of_and_zero hand, Nat.pow_succ]
      have : 2 ^ r ≥ 1 := Nat.one_le_two_pow; omega
    simpa [rBonacciCert, hpoly] using h
  have hpop : popcount x = popcount p + (r - 1) * popcount d := by
    have h := hlaws.2.2.2.2.2.1
    simpa [rBonacciCert, popcount_two_pow_sub_one] using h
  have hkummer : popcount (carryInMask x d) = r * popcount d := by
    have h := hlaws.2.2.2.2.2.2.1
    rw [hmS, Nat.one_mul] at h; exact h
  have heval : evalRecNat (rBonacciWeight r) p = evalRecNat (rBonacciWeight r) x := by
    have h := hlaws.2.2.2.2.2.2.2 (fun k => (rBonacciWeight r k : Int)) (rBonacciWeight_obeysRecInt hr)
    rw [evalRecInt_ofNat, evalRecInt_ofNat] at h; omega
  refine ⟨p, d, hp_no, heval, hpxd, hsp, hcarry, hclm, hpop, hkummer, ?_⟩
  intro p' d' hp'_no heval' hp'xd'
  have hpeq := rbonacci_uniqueness hr hp'_no hp_no (heval'.trans heval.symm)
  exact ⟨hpeq, by omega⟩

/-! ### 4.4 Classical Zeckendorf (`r = 2`, Fibbinary) Master & Disjoint-Support Addition Corollaries -/

theorem isFibbinary_iff_noROnes2 (x : Nat) : isFibbinary x ↔ noROnes 2 x := by
  unfold isFibbinary noROnes
  constructor
  · intro h i
    have hbi := congrArg (fun n => n.testBit (i + 1)) h
    rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at hbi
    simp only [show 1 ≤ i + 1 by omega, decide_true, Nat.add_sub_cancel, Bool.true_and] at hbi
    cases h1 : x.testBit (i + 1)
    · exact ⟨1, by omega, h1⟩
    · rw [h1, Bool.true_and] at hbi
      exact ⟨0, by omega, by simpa using hbi⟩
  · intro h
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit]
    cases k with
    | zero => simp
    | succ i =>
      simp only [show 1 ≤ i + 1 by omega, decide_true, Nat.add_sub_cancel, Bool.true_and]
      obtain ⟨j, hj2, hjf⟩ := h i
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl <;> simp_all

theorem isFibbinary_iff_isRSpaced2 (d : Nat) : isFibbinary d ↔ isRSpaced 2 d := by
  rw [isFibbinary_iff_noROnes2]
  unfold noROnes isRSpaced
  constructor
  · intro h i j hj1 hj2 hdi
    have : j = 1 := by omega
    subst this
    obtain ⟨t, ht2, htf⟩ := h i
    have : t = 0 ∨ t = 1 := by omega
    rcases this with rfl | rfl
    · simp [hdi] at htf
    · exact htf
  · intro h i
    cases h0 : d.testBit i
    · exact ⟨0, by omega, by simpa using h0⟩
    · exact ⟨1, by omega, h i 1 (by omega) (by omega) h0⟩

/-- **CLASSICAL ZECKENDORF (`r = 2`) PURE-BINARY CARRY-BRIDGE MASTER THEOREM:**
    For EVERY `x : Nat`, there exists a UNIQUE fibbinary `p` and fibbinary carry-defect `d`
    with `evalFib p = evalFib x`, characterized purely by `isFibbinary p ∧ p = x + d ∧ carryInMask x d = 6 * d`,
    and obeying:
    - `isFibbinary d` (the difference `Φ(x) - x` is ALWAYS fibbinary!),
    - `carryInMask x d = 6 * d` (exact binary carry-in mask = `6 d`),
    - `p ^^^ x = clmul 7 d` (exact `F_2[t]` carryless multiplication by `7 = t^2 + t + 1`),
    - `popcount x = popcount p + popcount d` (exact popcount defect),
    - `popcount (carryInMask x d) = 2 * popcount d` (exact Kummer carry-count = `2 · s_2(d)`). -/
theorem zeckendorf_r2_master_theorem (x : Nat) :
    ∃ p d,
      isFibbinary p ∧
      isFibbinary d ∧
      evalRecNat (rBonacciWeight 2) p = evalRecNat (rBonacciWeight 2) x ∧
      p = x + d ∧
      carryInMask x d = 6 * d ∧
      p ^^^ x = clmul 7 d ∧
      popcount x = popcount p + popcount d ∧
      popcount (carryInMask x d) = 2 * popcount d ∧
      (∀ p' d', isFibbinary p' → p' = x + d' → carryInMask x d' = 6 * d' → p' = p ∧ d' = d) := by
  obtain ⟨p, d, hp_no, heval, hpxd, hsp, hcarry, hclm, hpop, hkummer, huniq⟩ :=
    rbonacci_master_invariants (by omega : 2 ≥ 2) x
  refine ⟨p, d, (isFibbinary_iff_noROnes2 p).mpr hp_no, (isFibbinary_iff_isRSpaced2 d).mpr hsp,
          heval, hpxd, hcarry, hclm, by simpa using hpop, hkummer, ?_⟩
  intro p' d' hp'_fib hp'xd' hcarry'
  have hp'_no := (isFibbinary_iff_noROnes2 p').mp hp'_fib
  have hchar := (rbonacci_pure_binary_characterization (by omega : 2 ≥ 2) x p' d').mpr ⟨hp'_no, hp'xd', hcarry'⟩
  exact huniq p' d' hp'_no hchar.2.1 hp'xd'

/-- **DISJOINT-SUPPORT ZECKENDORF ADDITION COROLLARY:**
    Whenever two bitmasks `a, b : Nat` have zero binary carries (`(a &&& b) = 0`),
    their canonical Zeckendorf sum `p = Φ_2(a + b)` satisfies `evalFib p = evalFib a + evalFib b`,
    `p = (a + b) + d` with `d` fibbinary, `carryInMask (a + b) d = 6 * d`,
    `popcount (a + b) = popcount p + popcount d`, and `popcount a + popcount b = popcount p + popcount d`! -/
theorem zeckendorf_disjoint_addition (a b : Nat) (hdisj : (a &&& b) = 0) :
    ∃ p d,
      isFibbinary p ∧
      isFibbinary d ∧
      evalRecNat (rBonacciWeight 2) p =
        evalRecNat (rBonacciWeight 2) a + evalRecNat (rBonacciWeight 2) b ∧
      p = (a + b) + d ∧
      carryInMask (a + b) d = 6 * d ∧
      p ^^^ (a + b) = clmul 7 d ∧
      popcount a + popcount b = popcount p + popcount d ∧
      popcount (carryInMask (a + b) d) = 2 * popcount d := by
  obtain ⟨p, d, hp_fib, hd_fib, heval, hadd, hcarry, hclm, hpop, hkummer, _⟩ :=
    zeckendorf_r2_master_theorem (a + b)
  -- Show `evalRecNat G (a + b) = evalRecNat G a + evalRecNat G b` when `(a &&& b) = 0`!
  have heval_add : evalRecNat (rBonacciWeight 2) (a + b) =
      evalRecNat (rBonacciWeight 2) a + evalRecNat (rBonacciWeight 2) b := by
    obtain ⟨Na, hNa⟩ := exists_lt_two_pow a
    obtain ⟨Nb, hNb⟩ := exists_lt_two_pow b
    let N := max Na Nb + 1
    have haN : a < 2 ^ N := Nat.lt_of_lt_of_le hNa (Nat.pow_le_pow_right (by omega) (by omega))
    have hbN : b < 2 ^ N := Nat.lt_of_lt_of_le hNb (Nat.pow_le_pow_right (by omega) (by omega))
    have habN : a + b < 2 ^ N := by
      have ha' : a < 2 ^ (max Na Nb) := Nat.lt_of_lt_of_le hNa (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
      have hb' : b < 2 ^ (max Na Nb) := Nat.lt_of_lt_of_le hNb (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
      dsimp only [N]; rw [Nat.pow_succ]; omega
    rw [evalRecNat_eq_sumNat _ (a + b) N habN,
        evalRecNat_eq_sumNat _ a N haN,
        evalRecNat_eq_sumNat _ b N hbN, ← sumNat_add]
    apply sumNat_congr; intro i _
    rw [add_eq_xor_of_and_zero hdisj, Nat.testBit_xor]
    have h0 := congrArg (fun n => n.testBit i) hdisj
    rw [Nat.testBit_and, Nat.zero_testBit] at h0
    cases h1 : a.testBit i <;> cases h2 : b.testBit i <;>
      simp only [h1, h2, b2n_true, b2n_false, Bool.false_xor, Bool.true_xor,
                 Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and] at h0 ⊢ <;>
      first | omega | cases h0
  have hpop_ab : popcount a + popcount b = popcount (a + b) := by
    have hk := popcount_add_carry a b
    have hkm : carryInMask a b = 0 := by
      unfold carryInMask; rw [add_eq_xor_of_and_zero hdisj]
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases b.testBit i <;> rfl
    rw [hkm, popcount_zero, Nat.add_zero] at hk; exact hk
  refine ⟨p, d, hp_fib, hd_fib, by rw [heval, heval_add], hadd, hcarry, hclm, by omega, hkummer⟩

/-! ## Section 5: Kernel-Checked Certificates, Non-Vacuity Witnesses & Sharpness Counterexamples -/

/-! ### 5.1 Decidable Finite Difference-Basis Certificates (`decide` → Infinite Theorems) -/

theorem certFib2_ok : certFib2.isDiffBasis = true := by decide
theorem certTrib3_ok : certTrib3.isDiffBasis = true := by decide
theorem certTet4_ok : certTet4.isDiffBasis = true := by decide
theorem certDB4A_ok : certDB4A.isDiffBasis = true := by decide
theorem certDB4B_ok : certDB4B.isDiffBasis = true := by decide
theorem certDB5A_ok : certDB5A.isDiffBasis = true := by decide
theorem certDB6A_ok : certDB6A.isDiffBasis = true := by decide
theorem certNar3_not_diffBasis : certNar3.isValid = true ∧ certNar3.isDiffBasis = false := by decide

/-- Infinite theorem instantiated automatically from `certDB6A_ok` (`decide`) via the Carry-Bridge Engine:
    for the sparse difference-basis recurrence `G_{k+6} = G_{k+5} + G_{k+3} + G_{k+1} + G_k` (`m_S = 21`),
    EVERY rewrite derivation `x →* p` obeys `carryInMask x (21 * d) = 126 * d`, `p ^^^ x = clmul 107 d`,
    `popcount x = popcount p + 3 * popcount d`, and `popcount (carryInMask x (21 * d)) = 6 * popcount d`! -/
theorem sparse_r6_diff_basis_infinite_law {ks : List Nat} {x p : Nat}
    (hd : SRewriteDeriv certDB6A ks x p) :
    let d := sumPow2 ks
    isRSpaced 6 d ∧
    p = x + 21 * d ∧
    carryInMask x (21 * d) = 126 * d ∧
    p ^^^ x = clmul 107 d ∧
    popcount x = popcount p + 3 * popcount d ∧
    popcount (carryInMask x (21 * d)) = 6 * popcount d := by
  have h := diff_basis_implies_all_laws certDB6A_ok hd
  refine ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_, h.2.2.2.2.2.2.1⟩
  have hpc : popcount certDB6A.maskS - 1 = 3 := by
    have h43 : popcount 43 = 4 := by
      rw [popcount_eq_sumNat 43 6 (by decide)]; decide
    simp [certDB6A, h43]
  simpa [hpc] using h.2.2.2.2.2.1

/-! ### 5.2 Kernel-Checked Non-Vacuity Witnesses -/

/-- Non-vacuity witness 1: concrete non-trivial Zeckendorf (`r=2`) cascade `x = 47 (0b101111) → p = 68 (0b1000100)`,
    carry mask `d = 21 (0b10101)` accepted by the 3-state Carry-Bridge Transducer! -/
theorem witness_nonvacuity_zeckendorf_47 :
    TransducerAccepts certFib2 47 68 21 := by
  exact ⟨7, by decide, by decide, by decide, by decide⟩

/-- Non-vacuity witness 2: concrete Tribonacci (`r=3`) cascade `x = 127 (0b1111111) → p = 145 (0b10010001)`,
    3-spaced carry mask `d = 18 (0b10010)` accepted by the 4-state Carry-Bridge Transducer! -/
theorem witness_nonvacuity_tribonacci_127 :
    TransducerAccepts certTrib3 127 145 18 := by
  exact ⟨8, by decide, by decide, by decide, by decide⟩

/-- Non-vacuity witness 3: non-`r`-bonacci sparse difference basis `certDB6A` (`r=6, S={0,1,3,5}, m_S=21`)
    has a genuine non-trivial 2-step derivation `x = 0b101011101011 = 2795 → 4139 → p = 4160` (`d = 65 = 2^6 + 1`)! -/
theorem witness_nonvacuity_sparse_r6 :
    SRewriteDeriv certDB6A [6, 0] 2795 4160 := by
  refine SRewriteDeriv.cons (w1 := 4139) ?_ (SRewriteDeriv.cons (w1 := 4160) ?_ (SRewriteDeriv.nil 4160))
  · refine ⟨by decide, ?_, by decide⟩
    intro j hj hmj
    simp only [certDB6A] at hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hmj <;> decide
  · refine ⟨by decide, ?_, by decide⟩
    intro j hj hmj
    simp only [certDB6A] at hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> revert hmj <;> decide

/-! ### 5.3 Kernel-Checked Sharpness & Boundary Counterexamples -/

/-- **SHARPNESS 1 (Automatic `r`-Spacing Breaks Outside `m_S = 1`):**
    Even for a genuine difference basis (`certDB4B`, `r = 4, S = {0,2,3}, m_S = 3`),
    the carry-eigenvalue equation `carryInMask x (3 * d) = 30 * d` does NOT automatically force
    `d` to be 4-spaced: `x = 225`, `d = 15 = 0b1111` satisfies `carryInMask 225 45 = 450 = 30 * 15`,
    yet `¬ isRSpaced 4 15`! -/
theorem sharpness_automatic_spacing_fails_for_mS_gt_1 :
    certDB4B.isDiffBasis = true ∧
    carryInMask 225 (certDB4B.mS * 15) = (2 ^ (certDB4B.r + 1) - 2) * 15 ∧
    ¬ isRSpaced 4 15 := by
  refine ⟨by decide, by decide, ?_⟩
  intro hsp
  have h0 : (15 : Nat).testBit 0 = true := by decide
  have h1 : (15 : Nat).testBit 1 = true := by decide
  have hf := hsp 0 1 (by omega) (by omega) h0
  simp [h1] at hf

/-- **SHARPNESS 2 (Carry-Bridge Law Breaks Outside Difference Bases — Narayana's Cows):**
    For `certNar3` (`r = 3, S = {0, 2}, m_S = 3`, NOT a difference basis),
    there is an explicit valid 2-step derivation `[0, 1]` from `x = 7 (0b111) → 10 (0b1010) → p = 16 (0b10000)`
    with `d = 3 (0b11)` violating BOTH `3`-spacing AND `carryInMask 7 9 = 30 ≠ 42 = 14 * 3`! -/
theorem sharpness_narayana_violates_carry_bridge :
    SRewriteDeriv certNar3 [0, 1] 7 16 ∧
    sumPow2 [0, 1] = 3 ∧
    ¬ isRSpaced 3 3 ∧
    carryInMask 7 (certNar3.mS * 3) ≠ (2 ^ (certNar3.r + 1) - 2) * 3 := by
  refine ⟨?_, by decide, ?_, by decide⟩
  · refine SRewriteDeriv.cons (w1 := 10) ?_ (SRewriteDeriv.cons (w1 := 16) ?_ (SRewriteDeriv.nil 16))
    · refine ⟨by decide, ?_, by decide⟩
      intro j hj hmj
      simp only [certNar3] at hj
      have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl <;> revert hmj <;> decide
    · refine ⟨by decide, ?_, by decide⟩
      intro j hj hmj
      simp only [certNar3] at hj
      have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl <;> revert hmj <;> decide
  · intro hsp
    have h0 : (3 : Nat).testBit 0 = true := by decide
    have h1 : (3 : Nat).testBit 1 = true := by decide
    have hf := hsp 0 1 (by omega) (by omega) h0
    simp [h1] at hf

/-- **SHARPNESS 3 (Difference-Basis Carry-Bridge Holds Even Under Non-Confluence!):**
    For `certDB4A` (`r = 4, S = {0, 1, 3}, m_S = 5`, a genuine difference basis),
    starting from `x = 47 (0b101111)`, firing `k = 2` reaches `67` while firing `k = 0` reaches `52`
    (`67 ≠ 52`: non-confluent!), YET BOTH derivations satisfy `carryInMask x (5 * d) = 30 * d`! -/
theorem sharpness_non_confluence_still_obeys_carry_bridge :
    certDB4A.isDiffBasis = true ∧
    SRewriteDeriv certDB4A [2] 47 67 ∧
    SRewriteDeriv certDB4A [0] 47 52 ∧
    (67 : Nat) ≠ 52 ∧
    carryInMask 47 (certDB4A.mS * sumPow2 [2]) = 30 * sumPow2 [2] ∧
    carryInMask 47 (certDB4A.mS * sumPow2 [0]) = 30 * sumPow2 [0] := by
  have hd1 : SRewriteDeriv certDB4A [2] 47 67 := by
    refine SRewriteDeriv.cons (w1 := 67) ?_ (SRewriteDeriv.nil 67)
    refine ⟨by decide, ?_, by decide⟩
    intro j hj hmj
    simp only [certDB4A] at hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> revert hmj <;> decide
  have hd2 : SRewriteDeriv certDB4A [0] 47 52 := by
    refine SRewriteDeriv.cons (w1 := 52) ?_ (SRewriteDeriv.nil 52)
    refine ⟨by decide, ?_, by decide⟩
    intro j hj hmj
    simp only [certDB4A] at hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> revert hmj <;> decide
  exact ⟨certDB4A_ok, hd1, hd2, by decide,
         (diff_basis_implies_all_laws certDB4A_ok hd1).2.2.2.1,
         (diff_basis_implies_all_laws certDB4A_ok hd2).2.2.2.1⟩

end CarryBridge
