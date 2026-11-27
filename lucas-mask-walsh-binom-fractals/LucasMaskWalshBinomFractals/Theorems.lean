import LucasMaskWalshBinomFractals.Defs

namespace LucasMaskEngine
theorem popcount_pos_of_ne_zero {j : Nat} (hj : j ≠ 0) : 1 ≤ popcount j := by
  induction j using nat_strong_ind with
  | step j ih =>
    rw [popcount_pos_eq j hj]
    by_cases hp : j % 2 = 0
    · have := ih (j / 2) (by omega) (by omega); omega
    · omega

theorem v2NatAux_ge (fuel r : Nat) (h : r ≤ fuel) :
    v2NatAux (fuel + 1) r = v2NatAux fuel r := by
  induction fuel generalizing r with
  | zero =>
    have hr : r = 0 := by omega
    subst hr; rfl
  | succ f ih =>
    unfold v2NatAux
    by_cases hr : r = 0
    · simp [hr]
    · by_cases hp : r % 2 = 0
      · simp only [hr, hp, ↓reduceIte]
        rw [ih (r / 2) (by omega)]
      · simp [hr, hp]

theorem v2NatAux_eq_of_ge {f1 f2 r : Nat} (h1 : r ≤ f1) (h2 : r ≤ f2) :
    v2NatAux f1 r = v2NatAux f2 r := by
  have hgen : ∀ d f, r ≤ f → v2NatAux (f + d) r = v2NatAux f r := by
    intro d; induction d with
    | zero => intro f _; rfl
    | succ d ih =>
      intro f hf
      have : f + (d + 1) = (f + d) + 1 := by omega
      rw [this, v2NatAux_ge (f + d) r (by omega), ih f hf]
  have e1 := hgen (f1 - r) r (Nat.le_refl r)
  have e2 := hgen (f2 - r) r (Nat.le_refl r)
  rw [Nat.add_sub_of_le h1] at e1
  rw [Nat.add_sub_of_le h2] at e2
  rw [e1, e2]

theorem v2Nat_two_mul (m : Nat) (hm : m ≠ 0) : v2Nat (2 * m) = 1 + v2Nat m := by
  unfold v2Nat
  have h1 : 2 * m = (2 * m - 1) + 1 := by omega
  conv => lhs; rw [h1]; unfold v2NatAux
  have hne : (2 * m - 1) + 1 ≠ 0 := by omega
  have hpar : ((2 * m - 1) + 1) % 2 = 0 := by omega
  have hdiv : ((2 * m - 1) + 1) / 2 = m := by omega
  simp only [hne, hpar, hdiv, ↓reduceIte]
  rw [v2NatAux_eq_of_ge (f1 := 2 * m - 1) (f2 := m) (by omega) (Nat.le_refl m)]

theorem v2Nat_odd (m : Nat) : v2Nat (2 * m + 1) = 0 := by
  unfold v2Nat
  unfold v2NatAux
  simp

theorem submask_refl (n : Nat) : Submask n n := by
  rw [submask_iff_testBit]; intro _ h; exact h

theorem submask_trans {a b c : Nat} (hab : Submask a b) (hbc : Submask b c) :
    Submask a c := by
  rw [submask_iff_testBit] at *
  intro i ha; exact hbc i (hab i ha)

theorem submask_and_left (a b : Nat) : Submask (a &&& b) a := by
  rw [submask_iff_testBit]
  intro i h
  rw [Nat.testBit_and] at h
  exact (Bool.and_eq_true _ _ |>.mp h).1

theorem submask_and_right (a b : Nat) : Submask (a &&& b) b := by
  rw [submask_iff_testBit]
  intro i h
  rw [Nat.testBit_and] at h
  exact (Bool.and_eq_true _ _ |>.mp h).2

theorem endpointMask_submask (n : Nat) : Submask (endpointMask n) n :=
  submask_and_left n ((n <<< 1) ^^^ (n >>> 1))

theorem testBit_endpointMask_zero (n : Nat) :
    (endpointMask n).testBit 0 = (n.testBit 0 && n.testBit 1) := by
  unfold endpointMask
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  simp

theorem testBit_endpointMask_succ (n j : Nat) :
    (endpointMask n).testBit (j + 1) =
      (n.testBit (j + 1) && (xor (n.testBit j) (n.testBit (j + 2)))) := by
  unfold endpointMask
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have h1 : 1 + (j + 1) = j + 2 := by omega
  simp [h1]

theorem endpointMask_two_mul (m : Nat) : endpointMask (2 * m) = 2 * endpointMask m := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [testBit_endpointMask_zero, testBit_two_mul_zero, testBit_two_mul_zero]
    rfl
  | succ j =>
    rw [testBit_endpointMask_succ, testBit_two_mul_succ, testBit_two_mul_succ, testBit_two_mul_succ]
    cases j with
    | zero =>
      rw [testBit_two_mul_zero, testBit_endpointMask_zero]
      simp
    | succ r =>
      rw [testBit_two_mul_succ, testBit_endpointMask_succ]

theorem endpointMask_two_mul_add_one_zero (m : Nat) :
    (endpointMask (2 * m + 1)).testBit 0 = m.testBit 0 := by
  rw [testBit_endpointMask_zero, testBit_two_mul_add_one_zero, testBit_two_mul_add_one_succ]
  rfl

theorem endpointMask_two_mul_add_one_one (m : Nat) :
    (endpointMask (2 * m + 1)).testBit 1 = (m.testBit 0 && !(m.testBit 1)) := by
  rw [testBit_endpointMask_succ, testBit_two_mul_add_one_zero, testBit_two_mul_add_one_succ,
    testBit_two_mul_add_one_succ]
  cases m.testBit 0 <;> cases m.testBit 1 <;> rfl

theorem endpointMask_two_mul_add_one_ge2 (m j : Nat) :
    (endpointMask (2 * m + 1)).testBit (j + 2) = (endpointMask m).testBit (j + 1) := by
  rw [testBit_endpointMask_succ, testBit_endpointMask_succ,
    testBit_two_mul_add_one_succ, testBit_two_mul_add_one_succ, testBit_two_mul_add_one_succ]

/-- `endpointMask n = 0` iff `n` has no adjacent `1`-bits (`n &&& (n >>> 1) = 0`). -/
theorem endpointMask_eq_zero_iff (n : Nat) :
    endpointMask n = 0 ↔ n &&& (n >>> 1) = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.zero_testBit]
    suffices ∀ k, (n.testBit k && n.testBit (k + 1)) = false by
      simpa [Nat.add_comm] using this i
    intro k
    induction k with
    | zero =>
      have h0 := congrArg (fun x => x.testBit 0) h
      rw [testBit_endpointMask_zero, Nat.zero_testBit] at h0
      exact h0
    | succ j ih =>
      have hj := congrArg (fun x => x.testBit (j + 1)) h
      rw [testBit_endpointMask_succ, Nat.zero_testBit] at hj
      cases hbj : n.testBit j <;> cases hbj1 : n.testBit (j + 1) <;> cases hbj2 : n.testBit (j + 2) <;> simp_all
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    have hnext : ∀ k, (n.testBit k && n.testBit (k + 1)) = false := by
      intro k
      have hk := congrArg (fun x => x.testBit k) h
      rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.zero_testBit] at hk
      simpa [Nat.add_comm] using hk
    cases i with
    | zero =>
      rw [testBit_endpointMask_zero]
      exact hnext 0
    | succ j =>
      rw [testBit_endpointMask_succ]
      have h1 := hnext j
      have h2 := hnext (j + 1)
      cases hbj : n.testBit j <;> cases hbj1 : n.testBit (j + 1) <;> cases hbj2 : n.testBit (j + 2) <;> simp_all

/-! ## Section 1: Divisibility Helpers & Recursive Submask Sums -/

theorem dvd_sub_of_dvd {d a b : Int} (ha : d ∣ a) (hb : d ∣ b) : d ∣ (a - b) := by
  obtain ⟨qa, rfl⟩ := ha
  obtain ⟨qb, rfl⟩ := hb
  exact ⟨qa - qb, by rw [Int.mul_sub]⟩

theorem dvd_neg_of_dvd {d a : Int} (ha : d ∣ a) : d ∣ (-a) := by
  obtain ⟨q, rfl⟩ := ha
  exact ⟨-q, by rw [Int.mul_neg]⟩

theorem dvd_mul_right_of_dvd {d a : Int} (b : Int) (ha : d ∣ a) : d ∣ (a * b) := by
  obtain ⟨q, rfl⟩ := ha
  exact ⟨q * b, by rw [Int.mul_assoc]⟩

theorem dvd_mul_left_of_dvd {d b : Int} (a : Int) (hb : d ∣ b) : d ∣ (a * b) := by
  rw [Int.mul_comm]; exact dvd_mul_right_of_dvd a hb

theorem dvd_two_pow_zero (x : Int) : (2 : Int) ^ 0 ∣ x :=
  ⟨x, by simp⟩

theorem beq_two_mul_add_one_eq (a b : Nat) : (2 * a + 1 == 2 * b + 1) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : 2 * a + 1 ≠ 2 * b + 1 := by omega
    simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr hne]

theorem beq_two_mul_zero (a : Nat) : (2 * a == 0) = (a == 0) := by
  simpa using beq_two_mul_eq a 0

theorem not_dvd_two_pow_succ_of_congr {e : Nat} {x : Int}
    (h : (2 : Int) ^ (e + 1) ∣ (x - (2 : Int) ^ e)) :
    (2 : Int) ^ e ∣ x ∧ ¬ ((2 : Int) ^ (e + 1) ∣ x) := by
  obtain ⟨q, hq⟩ := h
  have hpow : (2 : Int) ^ (e + 1) = (2 : Int) ^ e * 2 := by rw [Int.pow_succ]
  have hx : x = (2 : Int) ^ e * (1 + 2 * q) := by
    rw [Int.mul_add, Int.mul_one, ← Int.mul_assoc, ← hpow]
    omega
  constructor
  · exact ⟨1 + 2 * q, hx⟩
  · intro ⟨r, hr⟩
    have hpos : (0 : Int) < (2 : Int) ^ e := by
      clear hq hx hr hpow
      induction e with
      | zero => decide
      | succ k ih => rw [Int.pow_succ]; omega
    have hmul : (2 : Int) ^ e * (1 + 2 * q) = (2 : Int) ^ e * (2 * r) := by
      rw [← hx, hr, hpow, Int.mul_assoc]
    have hcancel : 1 + 2 * q = 2 * r := Int.eq_of_mul_eq_mul_left (by omega) hmul
    omega

theorem sumRange_zero_fn (n : Nat) : sumRange n (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumRange, ih, Int.add_zero]

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih => simp only [sumRange, ih]; omega

theorem sumRange_neg (n : Nat) (f : Nat → Int) :
    sumRange n (fun i => - f i) = - sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih => simp only [sumRange, ih]; omega

theorem sumRange_dvd {d : Int} {n : Nat} {f : Nat → Int}
    (h : ∀ i, i < n → d ∣ f i) : d ∣ sumRange n f := by
  induction n with
  | zero => exact ⟨0, by simp [sumRange]⟩
  | succ k ih =>
    simp only [sumRange]
    exact dvd_add_of_dvd (ih (fun i hi => h i (by omega))) (h k (by omega))

theorem sumRange_split_first (n : Nat) (f : Nat → Int) :
    sumRange (n + 1) f = f 0 + sumRange n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    change sumRange (k + 1) f + f (k + 1) = f 0 + (sumRange k (fun i => f (i + 1)) + f (k + 1))
    rw [ih]
    omega

theorem sumSubmasks_zero_fn (j : Nat) : sumSubmasks j (fun _ => (0 : Int)) = 0 := by
  rw [sumSubmasks_eq_sumLucasFiltered]
  unfold sumLucasFiltered
  rw [sumRange_congr (g := fun _ => (0 : Int)) (fun k _ => by split <;> rfl)]
  exact sumRange_zero_fn (j + 1)

theorem sumSubmasks_sub (j : Nat) (f g : Nat → Int) :
    sumSubmasks j (fun k => f k - g k) = sumSubmasks j f - sumSubmasks j g := by
  rw [sumSubmasks_eq_sumLucasFiltered, sumSubmasks_eq_sumLucasFiltered, sumSubmasks_eq_sumLucasFiltered]
  unfold sumLucasFiltered
  rw [← sumRange_sub]
  apply sumRange_congr
  intro k _; dsimp only; split <;> omega

theorem sumSubmasks_neg (j : Nat) (f : Nat → Int) :
    sumSubmasks j (fun k => - f k) = - sumSubmasks j f := by
  rw [sumSubmasks_eq_sumLucasFiltered, sumSubmasks_eq_sumLucasFiltered]
  unfold sumLucasFiltered
  rw [← sumRange_neg]
  apply sumRange_congr
  intro k _; dsimp only; split <;> omega

theorem sumSubmasks_sumRange (j m : Nat) (g : Nat → Nat → Int) :
    sumSubmasks j (fun k => sumRange m (fun t => g t k)) =
    sumRange m (fun t => sumSubmasks j (fun k => g t k)) := by
  induction m with
  | zero => exact sumSubmasks_zero_fn j
  | succ r ih =>
    simp only [sumRange]
    rw [sumSubmasks_add, ih]

/-! ## Section 2: Boolean Mobius & Walsh-Hadamard Operators on the Lucas Cube -/

theorem and_odd_two_mul (a b : Nat) : (2 * a + 1) &&& (2 * b) = 2 * (a &&& b) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => rw [Nat.testBit_and, testBit_two_mul_add_one_zero, testBit_two_mul_zero, testBit_two_mul_zero]; rfl
  | succ j => rw [Nat.testBit_and, testBit_two_mul_add_one_succ, testBit_two_mul_succ, testBit_two_mul_succ, Nat.testBit_and]

theorem and_two_mul_odd (a b : Nat) : (2 * a) &&& (2 * b + 1) = 2 * (a &&& b) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => rw [Nat.testBit_and, testBit_two_mul_zero, testBit_two_mul_add_one_zero, testBit_two_mul_zero]; rfl
  | succ j => rw [Nat.testBit_and, testBit_two_mul_succ, testBit_two_mul_add_one_succ, testBit_two_mul_succ, Nat.testBit_and]

theorem and_odd_odd (a b : Nat) : (2 * a + 1) &&& (2 * b + 1) = 2 * (a &&& b) + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero => rw [Nat.testBit_and, testBit_two_mul_add_one_zero, testBit_two_mul_add_one_zero, testBit_two_mul_add_one_zero]; rfl
  | succ j => rw [Nat.testBit_and, testBit_two_mul_add_one_succ, testBit_two_mul_add_one_succ, testBit_two_mul_add_one_succ, Nat.testBit_and]

theorem mobius_zero_fn (j : Nat) : mobius (fun _ => (0 : Int)) j = 0 := by
  unfold mobius
  rw [sumSubmasks_congr (g := fun _ => (0 : Int)) (fun k _ => by simp)]
  exact sumSubmasks_zero_fn j

theorem mobius_congr {j : Nat} {f g : Nat → Int}
    (h : ∀ k, Submask k j → f k = g k) : mobius f j = mobius g j := by
  unfold mobius
  apply sumSubmasks_congr
  intro k hk; rw [h k hk]

theorem mobius_sub (f g : Nat → Int) (j : Nat) :
    mobius (fun k => f k - g k) j = mobius f j - mobius g j := by
  unfold mobius
  rw [← sumSubmasks_sub]
  apply sumSubmasks_congr
  intro k _; rw [Int.mul_sub]

theorem mobius_sumRange (m j : Nat) (g : Nat → Nat → Int) :
    mobius (fun k => sumRange m (fun t => g t k)) j =
    sumRange m (fun t => mobius (fun k => g t k) j) := by
  unfold mobius
  rw [← sumSubmasks_sumRange]
  apply sumSubmasks_congr
  intro k _
  rw [sumRange_mul_left]

/-- Exact Boolean Mobius Inversion on the Lucas cube: `∑_{j <=_2 k} mobius f j = f k`. -/
theorem sumSubmasks_mobius (f : Nat → Int) (k : Nat) :
    sumSubmasks k (mobius f) = f k := by
  induction k using nat_strong_ind generalizing f with
  | step k ih =>
    by_cases hk : k = 0
    · subst hk; rw [sumSubmasks_zero, mobius_zero]
    · by_cases hp : k % 2 = 0
      · have h2 : k = 2 * (k / 2) := by omega
        rw [h2, sumSubmasks_two_mul]
        have hstep : sumSubmasks (k / 2) (fun j => mobius f (2 * j)) =
            sumSubmasks (k / 2) (mobius (fun r => f (2 * r))) := by
          apply sumSubmasks_congr; intro j _; exact mobius_two_mul f j
        rw [hstep, ih (k / 2) (by omega)]
      · have h2 : k = 2 * (k / 2) + 1 := by omega
        rw [h2, sumSubmasks_two_mul_add_one]
        have hstep : sumSubmasks (k / 2) (fun j => mobius f (2 * j) + mobius f (2 * j + 1)) =
            sumSubmasks (k / 2) (mobius (fun r => f (2 * r + 1))) := by
          apply sumSubmasks_congr
          intro j _
          rw [mobius_two_mul, mobius_two_mul_add_one, ← mobius_add]
          apply mobius_congr; intro r _; omega
        rw [hstep, ih (k / 2) (by omega)]

theorem walsh_zero (f : Nat → Int) : walsh 0 0 f = f 0 := by
  unfold walsh; rw [sumSubmasks_zero]; simp [popcount_zero]

theorem walsh_zero_mask (n : Nat) (f : Nat → Int) :
    walsh n 0 f = sumSubmasks n f := by
  unfold walsh
  apply sumSubmasks_congr
  intro k _
  simp [popcount_zero]

theorem walsh_two_mul (n m : Nat) (f : Nat → Int) :
    walsh (2 * n) (2 * m) f = walsh n m (fun k => f (2 * k)) := by
  unfold walsh
  rw [sumSubmasks_two_mul]
  apply sumSubmasks_congr
  intro k _
  rw [and_two_mul_two_mul, popcount_two_mul]

theorem walsh_two_mul_add_one_even (n m : Nat) (f : Nat → Int) :
    walsh (2 * n + 1) (2 * m) f =
      2 * walsh n m (fun k => f (2 * k)) + walsh n m (fun k => f (2 * k + 1) - f (2 * k)) := by
  unfold walsh
  rw [sumSubmasks_two_mul_add_one, ← sumSubmasks_mul_left, ← sumSubmasks_add]
  apply sumSubmasks_congr
  intro k _
  rw [and_two_mul_two_mul, and_odd_two_mul, popcount_two_mul]
  by_cases hp : popcount (k &&& m) % 2 = 0
  · simp [hp]; omega
  · simp [hp]; omega

theorem walsh_two_mul_add_one_odd (n m : Nat) (f : Nat → Int) :
    walsh (2 * n + 1) (2 * m + 1) f = - walsh n m (fun k => f (2 * k + 1) - f (2 * k)) := by
  unfold walsh
  rw [sumSubmasks_two_mul_add_one, ← sumSubmasks_neg]
  apply sumSubmasks_congr
  intro k _
  rw [and_two_mul_odd, and_odd_odd, popcount_two_mul, popcount_two_mul_add_one]
  by_cases hp : popcount (k &&& m) % 2 = 0
  · have hp1 : (popcount (k &&& m) + 1) % 2 ≠ 0 := by omega
    simp [hp, hp1]; omega
  · have hp1 : (popcount (k &&& m) + 1) % 2 = 0 := by omega
    simp [hp, hp1]; omega

/-! ## Section 3: Stage 1 — The 2-State Bit-Slice Binomial Engine -/

theorem binomZ_succ (n : Nat) (k : Int) :
    binomZ (n + 1) k = binomZ n k + binomZ n (k - 1) := rfl

theorem binomZ_neg (n : Nat) (k : Int) (hk : k < 0) : binomZ n k = 0 := by
  induction n generalizing k with
  | zero =>
    unfold binomZ
    have hne : k ≠ 0 := by omega
    simp [hne]
  | succ m ih =>
    rw [binomZ_succ, ih k hk, ih (k - 1) (by omega)]
    rfl

theorem binomZ_gt (n : Nat) (k : Int) (hk : (n : Int) < k) : binomZ n k = 0 := by
  induction n generalizing k with
  | zero =>
    unfold binomZ
    have hne : k ≠ 0 := by omega
    simp [hne]
  | succ m ih =>
    rw [binomZ_succ, ih k (by omega), ih (k - 1) (by omega)]
    rfl

theorem binomZ_zero_right (n : Nat) : binomZ n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [binomZ_succ, ih, binomZ_neg m (0 - 1) (by omega)]
    rfl

theorem binomZ_one_right (n : Nat) : binomZ n 1 = (n : Int) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [binomZ_succ, ih]
    have h0 : (1 : Int) - 1 = 0 := rfl
    rw [h0, binomZ_zero_right]
    omega

theorem binomZ_eq_binomNat (n k : Nat) : binomZ n (k : Int) = (binomNat n k : Int) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ r =>
      unfold binomZ binomNat
      have hne : ((r + 1 : Nat) : Int) ≠ 0 := by omega
      simp only [hne, ↓reduceIte]; rfl
  | succ m ih =>
    cases k with
    | zero =>
      change binomZ (m + 1) 0 = (binomNat (m + 1) 0 : Int)
      rw [binomZ_zero_right]; rfl
    | succ r =>
      rw [binomZ_succ]
      unfold binomNat
      have hsub : ((r + 1 : Nat) : Int) - 1 = (r : Int) := by omega
      rw [hsub, ih (r + 1), ih r]
      simp

theorem binomZEven_pascal (a : Nat) (b : Int) :
    binomZEven a b + binomZEven a (b - 2) = binomZEven (a + 1) b := by
  unfold binomZEven
  have hmod : (b - 2) % 2 = b % 2 := by omega
  rw [hmod]
  by_cases h : b % 2 = 0
  · simp only [h, ↓reduceIte]
    have hdiv : (b - 2) / 2 = b / 2 - 1 := by omega
    rw [hdiv]; rfl
  · simp [h]

theorem binomZ_two_mul_succ (m : Nat) (k : Int) :
    binomZ (2 * (m + 1)) k =
      binomZ (2 * m) k + 2 * binomZ (2 * m) (k - 1) + binomZ (2 * m) (k - 2) := by
  have h : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  rw [h, binomZ_succ, binomZ_succ, binomZ_succ]
  have h2 : k - 1 - 1 = k - 2 := by omega
  rw [h2]; omega

/-- Unified Bit-Slice Binomial Expansion:
    `C(2m, k) = ∑_{t=0}^{m} 2^t * C(m, t) * binomZEven(m - t, k - t)`. -/
theorem binomZ_two_mul (m : Nat) (k : Int) :
    binomZ (2 * m) k =
      sumRange (m + 1) (fun t => (2 : Int) ^ t * binomZ m t * binomZEven (m - t) (k - t)) := by
  induction m generalizing k with
  | zero =>
    simp only [Nat.mul_zero, sumRange, Int.zero_add, Int.pow_zero, Nat.sub_zero]
    unfold binomZEven binomZ
    by_cases hk : k = 0
    · subst hk; simp
    · by_cases hmod : k % 2 = 0
      · have hdiv : k / 2 ≠ 0 := by omega
        simp [hk, hmod, hdiv]
      · simp [hk, hmod]
  | succ m ih =>
    rw [binomZ_two_mul_succ, ih k, ih (k - 1), ih (k - 2)]
    have h13 :
        sumRange (m + 1) (fun t => (2 : Int) ^ t * binomZ m t * binomZEven (m - t) (k - t)) +
        sumRange (m + 1) (fun t => (2 : Int) ^ t * binomZ m t * binomZEven (m - t) (k - 2 - t)) =
        sumRange (m + 1) (fun t => (2 : Int) ^ t * binomZ m t * binomZEven (m + 1 - t) (k - t)) := by
      rw [← sumRange_add]
      apply sumRange_congr
      intro t ht
      have hsub : k - 2 - (t : Int) = (k - (t : Int)) - 2 := by omega
      have hmn : m + 1 - t = (m - t) + 1 := by omega
      rw [hsub, hmn, ← Int.mul_add, binomZEven_pascal]
    have h2 :
        2 * sumRange (m + 1) (fun t => (2 : Int) ^ t * binomZ m t * binomZEven (m - t) (k - 1 - t)) =
        sumRange (m + 1) (fun t => (2 : Int) ^ (t + 1) * binomZ m t * binomZEven (m - t) (k - ((t + 1 : Nat) : Int))) := by
      rw [← sumRange_mul_left]
      apply sumRange_congr
      intro t _
      have hk1 : k - 1 - (t : Int) = k - ((t + 1 : Nat) : Int) := by omega
      rw [hk1, Int.pow_succ, ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm (2 : Int) ((2 : Int) ^ t)]
    have hreord :
        sumRange (m + 1) (fun t => (2 : Int) ^ t * binomZ m t * binomZEven (m - t) (k - t)) +
        2 * sumRange (m + 1) (fun t => (2 : Int) ^ t * binomZ m t * binomZEven (m - t) (k - 1 - t)) +
        sumRange (m + 1) (fun t => (2 : Int) ^ t * binomZ m t * binomZEven (m - t) (k - 2 - t)) =
        (sumRange (m + 1) (fun t => (2 : Int) ^ t * binomZ m t * binomZEven (m - t) (k - t)) +
         sumRange (m + 1) (fun t => (2 : Int) ^ t * binomZ m t * binomZEven (m - t) (k - 2 - t))) +
        2 * sumRange (m + 1) (fun t => (2 : Int) ^ t * binomZ m t * binomZEven (m - t) (k - 1 - t)) := by
      omega
    rw [hreord, h13, h2]
    rw [sumRange_split_first (m + 1)]
    rw [sumRange_split_first m]
    have h0 : binomZ (m + 1) ((0 : Nat) : Int) = binomZ m ((0 : Nat) : Int) := by
      change binomZ (m + 1) 0 = binomZ m 0
      rw [binomZ_zero_right, binomZ_zero_right]
    rw [h0]
    have hlast :
        sumRange (m + 1) (fun t => (2 : Int) ^ (t + 1) * binomZ m t * binomZEven (m - t) (k - ((t + 1 : Nat) : Int))) =
        sumRange m (fun t => (2 : Int) ^ (t + 1) * binomZ m t * binomZEven (m - t) (k - ((t + 1 : Nat) : Int))) +
        (2 : Int) ^ (m + 1) * binomZ m m * binomZEven (m - m) (k - ((m + 1 : Nat) : Int)) := rfl
    rw [hlast]
    have hrhs_last :
        sumRange (m + 1) (fun i => (2 : Int) ^ (i + 1) * binomZ (m + 1) ((i + 1 : Nat) : Int) *
          binomZEven (m + 1 - (i + 1)) (k - ((i + 1 : Nat) : Int))) =
        sumRange m (fun i => (2 : Int) ^ (i + 1) * binomZ (m + 1) ((i + 1 : Nat) : Int) *
          binomZEven (m + 1 - (i + 1)) (k - ((i + 1 : Nat) : Int))) +
        (2 : Int) ^ (m + 1) * binomZ (m + 1) ((m + 1 : Nat) : Int) *
          binomZEven (m + 1 - (m + 1)) (k - ((m + 1 : Nat) : Int)) := rfl
    rw [hrhs_last]
    have hdiag : binomZ (m + 1) ((m + 1 : Nat) : Int) = binomZ m (m : Int) := by
      rw [binomZ_succ, binomZ_gt m ((m + 1 : Nat) : Int) (by omega)]
      have hsub : ((m + 1 : Nat) : Int) - 1 = (m : Int) := by omega
      rw [hsub, Int.zero_add]
    have hsub0 : m + 1 - (m + 1) = m - m := by omega
    rw [hdiag, hsub0]
    have hmid :
        sumRange m (fun i => (2 : Int) ^ (i + 1) * binomZ m ((i + 1 : Nat) : Int) *
          binomZEven (m + 1 - (i + 1)) (k - ((i + 1 : Nat) : Int))) +
        sumRange m (fun t => (2 : Int) ^ (t + 1) * binomZ m t *
          binomZEven (m - t) (k - ((t + 1 : Nat) : Int))) =
        sumRange m (fun i => (2 : Int) ^ (i + 1) * binomZ (m + 1) ((i + 1 : Nat) : Int) *
          binomZEven (m + 1 - (i + 1)) (k - ((i + 1 : Nat) : Int))) := by
      rw [← sumRange_add]
      apply sumRange_congr
      intro i _
      have hs1 : m + 1 - (i + 1) = m - i := by omega
      have hpasc : binomZ (m + 1) ((i + 1 : Nat) : Int) =
          binomZ m ((i + 1 : Nat) : Int) + binomZ m (i : Int) := by
        rw [binomZ_succ]
        have hsub : ((i + 1 : Nat) : Int) - 1 = (i : Int) := by omega
        rw [hsub]
      rw [hs1, hpasc, Int.mul_add, Int.add_mul]
    omega

theorem delta_two_mul_two_mul_even (m h : Nat) (d : Int) :
    Delta (2 * m) (2 * h) (2 * d) =
      sumRange (m + 1) (fun t =>
        if t % 2 = 0 then
          (2 : Int) ^ t * binomZ m t * Delta (m - t) h (d + ((t / 2 : Nat) : Int))
        else 0) := by
  unfold Delta
  rw [mobius_two_mul]
  have heq : (fun (k : Nat) => binomZ (2 * m) (((2 * k : Nat) : Int) - 2 * d)) =
      (fun (k : Nat) => sumRange (m + 1) (fun t =>
        if t % 2 = 0 then
          (2 : Int) ^ t * binomZ m t * binomZ (m - t) ((k : Int) - (d + ((t / 2 : Nat) : Int)))
        else 0)) := by
    funext k
    rw [binomZ_two_mul]
    apply sumRange_congr
    intro t _
    unfold binomZEven
    have hpar : (((2 * k : Nat) : Int) - 2 * d - (t : Int)) % 2 = 0 ↔ t % 2 = 0 := by omega
    by_cases ht : t % 2 = 0
    · have ht' := hpar.mpr ht
      have hdiv : (((2 * k : Nat) : Int) - 2 * d - (t : Int)) / 2 =
          (k : Int) - (d + ((t / 2 : Nat) : Int)) := by omega
      simp only [ht, ht', ↓reduceIte, hdiv]
    · have ht' : ¬ ((((2 * k : Nat) : Int) - 2 * d - (t : Int)) % 2 = 0) := fun h => ht (hpar.mp h)
      simp only [ht, ht', ↓reduceIte, Int.mul_zero]
  rw [heq, mobius_sumRange]
  apply sumRange_congr
  intro t _
  by_cases ht : t % 2 = 0
  · simp only [ht, ↓reduceIte]
    rw [mobius_mul_left]
  · simp only [ht, ↓reduceIte]
    exact mobius_zero_fn h

theorem delta_two_mul_two_mul_odd (m h : Nat) (d : Int) :
    Delta (2 * m) (2 * h) (2 * d + 1) =
      sumRange (m + 1) (fun t =>
        if t % 2 = 1 then
          (2 : Int) ^ t * binomZ m t * Delta (m - t) h (d + ((t / 2 : Nat) : Int) + 1)
        else 0) := by
  unfold Delta
  rw [mobius_two_mul]
  have heq : (fun (k : Nat) => binomZ (2 * m) (((2 * k : Nat) : Int) - (2 * d + 1))) =
      (fun (k : Nat) => sumRange (m + 1) (fun t =>
        if t % 2 = 1 then
          (2 : Int) ^ t * binomZ m t * binomZ (m - t) ((k : Int) - (d + ((t / 2 : Nat) : Int) + 1))
        else 0)) := by
    funext k
    rw [binomZ_two_mul]
    apply sumRange_congr
    intro t _
    unfold binomZEven
    have hpar : (((2 * k : Nat) : Int) - (2 * d + 1) - (t : Int)) % 2 = 0 ↔ t % 2 = 1 := by omega
    by_cases ht : t % 2 = 1
    · have ht' := hpar.mpr ht
      have hdiv : (((2 * k : Nat) : Int) - (2 * d + 1) - (t : Int)) / 2 =
          (k : Int) - (d + ((t / 2 : Nat) : Int) + 1) := by omega
      simp only [ht, ht', ↓reduceIte, hdiv]
    · have ht' : ¬ ((((2 * k : Nat) : Int) - (2 * d + 1) - (t : Int)) % 2 = 0) := fun h => ht (hpar.mp h)
      simp only [ht, ht', ↓reduceIte, Int.mul_zero]
  rw [heq, mobius_sumRange]
  apply sumRange_congr
  intro t _
  by_cases ht : t % 2 = 1
  · simp only [ht, ↓reduceIte]
    rw [mobius_mul_left]
  · simp only [ht, ↓reduceIte]
    exact mobius_zero_fn h

theorem delta_odd_even (m h : Nat) (c : Int) :
    Delta (2 * m + 1) (2 * h) c = Delta (2 * m) (2 * h) c + Delta (2 * m) (2 * h) (c + 1) := by
  unfold Delta
  rw [← mobius_add]
  apply mobius_congr
  intro k _
  rw [binomZ_succ]
  have hsub : (k : Int) - c - 1 = (k : Int) - (c + 1) := by omega
  rw [hsub]

theorem delta_even_odd (m h : Nat) (c : Int) :
    Delta (2 * m) (2 * h + 1) c = Delta (2 * m) (2 * h) (c - 1) - Delta (2 * m) (2 * h) c := by
  unfold Delta
  rw [mobius_two_mul_add_one, mobius_two_mul, mobius_two_mul, ← mobius_sub]
  apply mobius_congr
  intro k _
  have h1 : ((2 * k + 1 : Nat) : Int) - c = ((2 * k : Nat) : Int) - (c - 1) := by omega
  rw [h1]

/-- Key carry-coupling identity `(1 - y)(1 + y)^a = (1 + y)^(a+1) - 2y(1 + y)^a`
    at the level of binomial coefficients. -/
theorem binomZ_diff_carry (a : Nat) (b : Int) :
    binomZ a b - binomZ a (b - 1) = binomZ (a + 1) b - 2 * binomZ a (b - 1) := by
  rw [binomZ_succ]; omega

theorem delta_odd_odd_even (m h : Nat) (d : Int) :
    Delta (2 * m + 1) (2 * h + 1) (2 * d) =
      sumRange (m + 1) (fun t =>
        if t % 2 = 1 then
          (2 : Int) ^ t * binomZ m t *
            (Delta (m - t + 1) h (d + ((t / 2 : Nat) : Int)) -
             2 * Delta (m - t) h (d + ((t / 2 : Nat) : Int) + 1))
        else 0) := by
  unfold Delta
  rw [mobius_two_mul_add_one]
  have heq : (fun (k : Nat) => binomZ (2 * m + 1) (((2 * k + 1 : Nat) : Int) - 2 * d) -
      binomZ (2 * m + 1) (((2 * k : Nat) : Int) - 2 * d)) =
      (fun (k : Nat) => sumRange (m + 1) (fun t =>
        if t % 2 = 1 then
          (2 : Int) ^ t * binomZ m t *
            (binomZ (m - t + 1) ((k : Int) - (d + ((t / 2 : Nat) : Int))) -
             2 * binomZ (m - t) ((k : Int) - (d + ((t / 2 : Nat) : Int) + 1)))
        else 0)) := by
    funext k
    have hcancel : binomZ (2 * m + 1) (((2 * k + 1 : Nat) : Int) - 2 * d) -
        binomZ (2 * m + 1) (((2 * k : Nat) : Int) - 2 * d) =
        binomZ (2 * m) (((2 * k + 1 : Nat) : Int) - 2 * d) -
        binomZ (2 * m) (((2 * k : Nat) : Int) - 2 * d - 1) := by
      rw [binomZ_succ, binomZ_succ]
      have h1 : (((2 * k + 1 : Nat) : Int) - 2 * d) - 1 = ((2 * k : Nat) : Int) - 2 * d := by omega
      rw [h1]; omega
    rw [hcancel, binomZ_two_mul, binomZ_two_mul, ← sumRange_sub]
    apply sumRange_congr
    intro t _
    rw [← Int.mul_sub]
    unfold binomZEven
    have hpar1 : (((2 * k + 1 : Nat) : Int) - 2 * d - (t : Int)) % 2 = 0 ↔ t % 2 = 1 := by omega
    have hpar2 : (((2 * k : Nat) : Int) - 2 * d - 1 - (t : Int)) % 2 = 0 ↔ t % 2 = 1 := by omega
    by_cases ht : t % 2 = 1
    · have ht1 := hpar1.mpr ht
      have ht2 := hpar2.mpr ht
      have hd1 : (((2 * k + 1 : Nat) : Int) - 2 * d - (t : Int)) / 2 =
          (k : Int) - (d + ((t / 2 : Nat) : Int)) := by omega
      have hd2 : (((2 * k : Nat) : Int) - 2 * d - 1 - (t : Int)) / 2 =
          ((k : Int) - (d + ((t / 2 : Nat) : Int))) - 1 := by omega
      have hd3 : ((k : Int) - (d + ((t / 2 : Nat) : Int))) - 1 =
          (k : Int) - (d + ((t / 2 : Nat) : Int) + 1) := by omega
      simp only [ht, ht1, ht2, ↓reduceIte, hd1, hd2]
      rw [binomZ_diff_carry, hd3]
    · have ht1 : ¬ ((((2 * k + 1 : Nat) : Int) - 2 * d - (t : Int)) % 2 = 0) := fun h => ht (hpar1.mp h)
      have ht2 : ¬ ((((2 * k : Nat) : Int) - 2 * d - 1 - (t : Int)) % 2 = 0) := fun h => ht (hpar2.mp h)
      simp only [ht, ht1, ht2, ↓reduceIte, Int.sub_self, Int.mul_zero]
  rw [heq, mobius_sumRange]
  apply sumRange_congr
  intro t _
  by_cases ht : t % 2 = 1
  · simp only [ht, ↓reduceIte]
    rw [mobius_mul_left, mobius_sub, mobius_mul_left]
  · simp only [ht, ↓reduceIte]
    exact mobius_zero_fn h

theorem delta_odd_odd_odd (m h : Nat) (d : Int) :
    Delta (2 * m + 1) (2 * h + 1) (2 * d + 1) =
      sumRange (m + 1) (fun t =>
        if t % 2 = 0 then
          (2 : Int) ^ t * binomZ m t *
            (Delta (m - t + 1) h (d + ((t / 2 : Nat) : Int)) -
             2 * Delta (m - t) h (d + ((t / 2 : Nat) : Int) + 1))
        else 0) := by
  unfold Delta
  rw [mobius_two_mul_add_one]
  have heq : (fun (k : Nat) => binomZ (2 * m + 1) (((2 * k + 1 : Nat) : Int) - (2 * d + 1)) -
      binomZ (2 * m + 1) (((2 * k : Nat) : Int) - (2 * d + 1))) =
      (fun (k : Nat) => sumRange (m + 1) (fun t =>
        if t % 2 = 0 then
          (2 : Int) ^ t * binomZ m t *
            (binomZ (m - t + 1) ((k : Int) - (d + ((t / 2 : Nat) : Int))) -
             2 * binomZ (m - t) ((k : Int) - (d + ((t / 2 : Nat) : Int) + 1)))
        else 0)) := by
    funext k
    have hcancel : binomZ (2 * m + 1) (((2 * k + 1 : Nat) : Int) - (2 * d + 1)) -
        binomZ (2 * m + 1) (((2 * k : Nat) : Int) - (2 * d + 1)) =
        binomZ (2 * m) (((2 * k + 1 : Nat) : Int) - (2 * d + 1)) -
        binomZ (2 * m) (((2 * k : Nat) : Int) - (2 * d + 1) - 1) := by
      rw [binomZ_succ, binomZ_succ]
      have h1 : (((2 * k + 1 : Nat) : Int) - (2 * d + 1)) - 1 = ((2 * k : Nat) : Int) - (2 * d + 1) := by omega
      rw [h1]; omega
    rw [hcancel, binomZ_two_mul, binomZ_two_mul, ← sumRange_sub]
    apply sumRange_congr
    intro t _
    rw [← Int.mul_sub]
    unfold binomZEven
    have hpar1 : (((2 * k + 1 : Nat) : Int) - (2 * d + 1) - (t : Int)) % 2 = 0 ↔ t % 2 = 0 := by omega
    have hpar2 : (((2 * k : Nat) : Int) - (2 * d + 1) - 1 - (t : Int)) % 2 = 0 ↔ t % 2 = 0 := by omega
    by_cases ht : t % 2 = 0
    · have ht1 := hpar1.mpr ht
      have ht2 := hpar2.mpr ht
      have hd1 : (((2 * k + 1 : Nat) : Int) - (2 * d + 1) - (t : Int)) / 2 =
          (k : Int) - (d + ((t / 2 : Nat) : Int)) := by omega
      have hd2 : (((2 * k : Nat) : Int) - (2 * d + 1) - 1 - (t : Int)) / 2 =
          ((k : Int) - (d + ((t / 2 : Nat) : Int))) - 1 := by omega
      have hd3 : ((k : Int) - (d + ((t / 2 : Nat) : Int))) - 1 =
          (k : Int) - (d + ((t / 2 : Nat) : Int) + 1) := by omega
      simp only [ht, ht1, ht2, ↓reduceIte, hd1, hd2]
      rw [binomZ_diff_carry, hd3]
    · have ht1 : ¬ ((((2 * k + 1 : Nat) : Int) - (2 * d + 1) - (t : Int)) % 2 = 0) := fun h => ht (hpar1.mp h)
      have ht2 : ¬ ((((2 * k : Nat) : Int) - (2 * d + 1) - 1 - (t : Int)) % 2 = 0) := fun h => ht (hpar2.mp h)
      simp only [ht, ht1, ht2, ↓reduceIte, Int.sub_self, Int.mul_zero]
  rw [heq, mobius_sumRange]
  apply sumRange_congr
  intro t _
  by_cases ht : t % 2 = 0
  · simp only [ht, ↓reduceIte]
    rw [mobius_mul_left, mobius_sub, mobius_mul_left]
  · simp only [ht, ↓reduceIte]
    exact mobius_zero_fn h

/-! ### Closed 2-State Universal Divisibility Theorem -/

/-- The 2-state closed bit-slice divisibility invariant:
    For every `N`, every submask `j <=_2 N`:
    - State 0: for all `c` with `2 * c <= N`, `2^(popcount j - c) | Delta (N - 2*c) j c`.
    - State 1: for all `c >= 1` with `2 * c <= N + 1`, `2^(popcount j - c) | Delta (N - 2*c + 1) j c`. -/
theorem delta_two_state_div (N : Nat) :
    (∀ j c : Nat, Submask j N → 2 * c ≤ N →
      (2 : Int) ^ (popcount j - c) ∣ Delta (N - 2 * c) j (c : Int)) ∧
    (∀ j c : Nat, Submask j N → 1 ≤ c → 2 * c ≤ N + 1 →
      (2 : Int) ^ (popcount j - c) ∣ Delta (N + 1 - 2 * c) j (c : Int)) := by
  induction N using nat_strong_ind with
  | step N ih =>
    by_cases hN0 : N = 0
    · subst hN0
      constructor
      · intro j c hj hc
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero (submask_le hj)
        subst hj0; rw [popcount_zero, show (0 : Nat) - c = 0 by omega]; exact dvd_two_pow_zero _
      · intro j c hj hc1 hc2; omega
    · by_cases hNpar : N % 2 = 0
      · let M := N / 2
        have hNM : N = 2 * M := by omega
        obtain ⟨ih0, ih1⟩ := ih M (by omega)
        have hState0 : ∀ j c : Nat, Submask j (2 * M) → 2 * c ≤ 2 * M →
            (2 : Int) ^ (popcount j - c) ∣ Delta (2 * M - 2 * c) j (c : Int) := by
          intro j c hj hc
          obtain ⟨hj0, hjM⟩ := (submask_two_mul_iff j M).mp hj
          let h := j / 2
          have hjh : j = 2 * h := by omega
          rw [hjh, popcount_two_mul]
          have hsub : 2 * M - 2 * c = 2 * (M - c) := by omega
          rw [hsub]
          by_cases hcpar : c % 2 = 0
          · let d := c / 2
            have hcd : (c : Int) = 2 * (d : Int) := by omega
            rw [hcd, delta_two_mul_two_mul_even]
            apply sumRange_dvd
            intro t ht
            by_cases htp : t % 2 = 0
            · simp only [htp, ↓reduceIte]
              have hle : 2 * (d + t / 2) ≤ M := by omega
              have hn' : M - c - t = M - 2 * (d + t / 2) := by omega
              have hc' : (d : Int) + ((t / 2 : Nat) : Int) = ((d + t / 2 : Nat) : Int) := by omega
              rw [hn', hc']
              have hdvd := ih0 h (d + t / 2) hjM hle
              have hmul : (2 : Int) ^ (t + (popcount h - (d + t / 2))) ∣
                  (2 : Int) ^ t * binomZ (M - c) t * Delta (M - 2 * (d + t / 2)) h ((d + t / 2 : Nat) : Int) := by
                rw [Int.mul_assoc, Int.mul_comm (binomZ (M - c) t), ← Int.mul_assoc]
                exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdvd)
              exact dvd_two_pow_mono (by omega) hmul
            · simp [htp]
          · let d := c / 2
            have hcd : (c : Int) = 2 * (d : Int) + 1 := by omega
            rw [hcd, delta_two_mul_two_mul_odd]
            apply sumRange_dvd
            intro t ht
            by_cases htp : t % 2 = 1
            · simp only [htp, ↓reduceIte]
              have hle : 2 * (d + t / 2 + 1) ≤ M := by omega
              have hn' : M - c - t = M - 2 * (d + t / 2 + 1) := by omega
              have hc' : (d : Int) + ((t / 2 : Nat) : Int) + 1 = ((d + t / 2 + 1 : Nat) : Int) := by omega
              rw [hn', hc']
              have hdvd := ih0 h (d + t / 2 + 1) hjM hle
              have hmul : (2 : Int) ^ (t + (popcount h - (d + t / 2 + 1))) ∣
                  (2 : Int) ^ t * binomZ (M - c) t * Delta (M - 2 * (d + t / 2 + 1)) h ((d + t / 2 + 1 : Nat) : Int) := by
                rw [Int.mul_assoc, Int.mul_comm (binomZ (M - c) t), ← Int.mul_assoc]
                exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdvd)
              exact dvd_two_pow_mono (by omega) hmul
            · simp [htp]
        have hState1 : ∀ j c : Nat, Submask j (2 * M) → 1 ≤ c → 2 * c ≤ 2 * M + 1 →
            (2 : Int) ^ (popcount j - c) ∣ Delta (2 * M + 1 - 2 * c) j (c : Int) := by
          intro j c hj hc1 hc2
          obtain ⟨hj0, hjM⟩ := (submask_two_mul_iff j M).mp hj
          let h := j / 2
          have hjh : j = 2 * h := by omega
          have hsub : 2 * M + 1 - 2 * c = 2 * (M - c) + 1 := by omega
          rw [hjh, hsub, delta_odd_even]
          apply dvd_add_of_dvd
          · have h1 := hState0 (2 * h) c (by rw [← hjh]; exact hj) (by omega)
            have hsub0 : 2 * M - 2 * c = 2 * (M - c) := by omega
            rw [hsub0] at h1; exact h1
          · rw [popcount_two_mul]
            by_cases hcpar : c % 2 = 0
            · let d := c / 2
              have hcd : (c : Int) + 1 = 2 * (d : Int) + 1 := by omega
              rw [hcd, delta_two_mul_two_mul_odd]
              apply sumRange_dvd
              intro t ht
              by_cases htp : t % 2 = 1
              · simp only [htp, ↓reduceIte]
                have hle : 2 * (d + t / 2 + 1) ≤ M + 1 := by omega
                have hn' : M - c - t = M + 1 - 2 * (d + t / 2 + 1) := by omega
                have hc' : (d : Int) + ((t / 2 : Nat) : Int) + 1 = ((d + t / 2 + 1 : Nat) : Int) := by omega
                rw [hn', hc']
                have hdvd := ih1 h (d + t / 2 + 1) hjM (by omega) hle
                have hmul : (2 : Int) ^ (t + (popcount h - (d + t / 2 + 1))) ∣
                    (2 : Int) ^ t * binomZ (M - c) t *
                      Delta (M + 1 - 2 * (d + t / 2 + 1)) h ((d + t / 2 + 1 : Nat) : Int) := by
                  rw [Int.mul_assoc, Int.mul_comm (binomZ (M - c) t), ← Int.mul_assoc]
                  exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdvd)
                exact dvd_two_pow_mono (by omega) hmul
              · simp [htp]
            · let d := c / 2
              have hcd : (c : Int) + 1 = 2 * ((d + 1 : Nat) : Int) := by omega
              rw [hcd, delta_two_mul_two_mul_even]
              apply sumRange_dvd
              intro t ht
              by_cases htp : t % 2 = 0
              · simp only [htp, ↓reduceIte]
                have hle : 2 * (d + 1 + t / 2) ≤ M + 1 := by omega
                have hn' : M - c - t = M + 1 - 2 * (d + 1 + t / 2) := by omega
                have hc' : ((d + 1 : Nat) : Int) + ((t / 2 : Nat) : Int) = ((d + 1 + t / 2 : Nat) : Int) := by omega
                rw [hn', hc']
                have hdvd := ih1 h (d + 1 + t / 2) hjM (by omega) hle
                have hmul : (2 : Int) ^ (t + (popcount h - (d + 1 + t / 2))) ∣
                    (2 : Int) ^ t * binomZ (M - c) t *
                      Delta (M + 1 - 2 * (d + 1 + t / 2)) h ((d + 1 + t / 2 : Nat) : Int) := by
                  rw [Int.mul_assoc, Int.mul_comm (binomZ (M - c) t), ← Int.mul_assoc]
                  exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdvd)
                exact dvd_two_pow_mono (by omega) hmul
              · simp [htp]
        rw [hNM]; exact ⟨hState0, hState1⟩
      · let M := N / 2
        have hNM : N = 2 * M + 1 := by omega
        obtain ⟨ih0, ih1⟩ := ih M (by omega)
        have hEven0 : ∀ h c : Nat, Submask h M → c ≤ M →
            (2 : Int) ^ (popcount h - c) ∣ Delta (2 * (M - c)) (2 * h) (c : Int) := by
          intro h c hhM hc
          by_cases hcpar : c % 2 = 0
          · let d := c / 2
            have hcd : (c : Int) = 2 * (d : Int) := by omega
            rw [hcd, delta_two_mul_two_mul_even]
            apply sumRange_dvd
            intro t ht
            by_cases htp : t % 2 = 0
            · simp only [htp, ↓reduceIte]
              have hle : 2 * (d + t / 2) ≤ M := by omega
              have hn' : M - c - t = M - 2 * (d + t / 2) := by omega
              have hc' : (d : Int) + ((t / 2 : Nat) : Int) = ((d + t / 2 : Nat) : Int) := by omega
              rw [hn', hc']
              have hdvd := ih0 h (d + t / 2) hhM hle
              have hmul : (2 : Int) ^ (t + (popcount h - (d + t / 2))) ∣
                  (2 : Int) ^ t * binomZ (M - c) t * Delta (M - 2 * (d + t / 2)) h ((d + t / 2 : Nat) : Int) := by
                rw [Int.mul_assoc, Int.mul_comm (binomZ (M - c) t), ← Int.mul_assoc]
                exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdvd)
              exact dvd_two_pow_mono (by omega) hmul
            · simp [htp]
          · let d := c / 2
            have hcd : (c : Int) = 2 * (d : Int) + 1 := by omega
            rw [hcd, delta_two_mul_two_mul_odd]
            apply sumRange_dvd
            intro t ht
            by_cases htp : t % 2 = 1
            · simp only [htp, ↓reduceIte]
              have hle : 2 * (d + t / 2 + 1) ≤ M := by omega
              have hn' : M - c - t = M - 2 * (d + t / 2 + 1) := by omega
              have hc' : (d : Int) + ((t / 2 : Nat) : Int) + 1 = ((d + t / 2 + 1 : Nat) : Int) := by omega
              rw [hn', hc']
              have hdvd := ih0 h (d + t / 2 + 1) hhM hle
              have hmul : (2 : Int) ^ (t + (popcount h - (d + t / 2 + 1))) ∣
                  (2 : Int) ^ t * binomZ (M - c) t * Delta (M - 2 * (d + t / 2 + 1)) h ((d + t / 2 + 1 : Nat) : Int) := by
                rw [Int.mul_assoc, Int.mul_comm (binomZ (M - c) t), ← Int.mul_assoc]
                exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdvd)
              exact dvd_two_pow_mono (by omega) hmul
            · simp [htp]
        have hCase4Strong : ∀ h c : Nat, Submask h M → 1 ≤ c → c ≤ M + 1 →
            (2 : Int) ^ (popcount h + 1 - c) ∣ Delta (2 * (M + 1 - c)) (2 * h) (c : Int) := by
          intro h c hhM hc1 hc2
          by_cases hcpar : c % 2 = 0
          · let d := c / 2
            have hcd : (c : Int) = 2 * (d : Int) := by omega
            rw [hcd, delta_two_mul_two_mul_even]
            apply sumRange_dvd
            intro t ht
            by_cases htp : t % 2 = 0
            · simp only [htp, ↓reduceIte]
              have hle : 2 * (d + t / 2) ≤ M + 1 := by omega
              have hn' : M + 1 - c - t = M + 1 - 2 * (d + t / 2) := by omega
              have hc' : (d : Int) + ((t / 2 : Nat) : Int) = ((d + t / 2 : Nat) : Int) := by omega
              rw [hn', hc']
              have hdvd := ih1 h (d + t / 2) hhM (by omega) hle
              have hmul : (2 : Int) ^ (t + (popcount h - (d + t / 2))) ∣
                  (2 : Int) ^ t * binomZ (M + 1 - c) t *
                    Delta (M + 1 - 2 * (d + t / 2)) h ((d + t / 2 : Nat) : Int) := by
                rw [Int.mul_assoc, Int.mul_comm (binomZ (M + 1 - c) t), ← Int.mul_assoc]
                exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdvd)
              exact dvd_two_pow_mono (by omega) hmul
            · simp [htp]
          · let d := c / 2
            have hcd : (c : Int) = 2 * (d : Int) + 1 := by omega
            rw [hcd, delta_two_mul_two_mul_odd]
            apply sumRange_dvd
            intro t ht
            by_cases htp : t % 2 = 1
            · simp only [htp, ↓reduceIte]
              have hle : 2 * (d + t / 2 + 1) ≤ M + 1 := by omega
              have hn' : M + 1 - c - t = M + 1 - 2 * (d + t / 2 + 1) := by omega
              have hc' : (d : Int) + ((t / 2 : Nat) : Int) + 1 = ((d + t / 2 + 1 : Nat) : Int) := by omega
              rw [hn', hc']
              have hdvd := ih1 h (d + t / 2 + 1) hhM (by omega) hle
              have hmul : (2 : Int) ^ (t + (popcount h - (d + t / 2 + 1))) ∣
                  (2 : Int) ^ t * binomZ (M + 1 - c) t *
                    Delta (M + 1 - 2 * (d + t / 2 + 1)) h ((d + t / 2 + 1 : Nat) : Int) := by
                rw [Int.mul_assoc, Int.mul_comm (binomZ (M + 1 - c) t), ← Int.mul_assoc]
                exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdvd)
              exact dvd_two_pow_mono (by omega) hmul
            · simp [htp]
        rw [hNM]
        constructor
        · intro j c hj hc
          have hjM : Submask (j / 2) M := (submask_two_mul_add_one_iff j M).mp hj
          let h := j / 2
          by_cases hjpar : j % 2 = 0
          · have hjh : j = 2 * h := by omega
            have hsub : 2 * M + 1 - 2 * c = 2 * (M - c) + 1 := by omega
            rw [hjh, popcount_two_mul, hsub, delta_odd_even]
            apply dvd_add_of_dvd
            · exact hEven0 h c hjM (by omega)
            · by_cases hcpar : c % 2 = 0
              · let d := c / 2
                have hcd : (c : Int) + 1 = 2 * (d : Int) + 1 := by omega
                rw [hcd, delta_two_mul_two_mul_odd]
                apply sumRange_dvd
                intro t ht
                by_cases htp : t % 2 = 1
                · simp only [htp, ↓reduceIte]
                  have hle : 2 * (d + t / 2 + 1) ≤ M + 1 := by omega
                  have hn' : M - c - t = M + 1 - 2 * (d + t / 2 + 1) := by omega
                  have hc' : (d : Int) + ((t / 2 : Nat) : Int) + 1 = ((d + t / 2 + 1 : Nat) : Int) := by omega
                  rw [hn', hc']
                  have hdvd := ih1 h (d + t / 2 + 1) hjM (by omega) hle
                  have hmul : (2 : Int) ^ (t + (popcount h - (d + t / 2 + 1))) ∣
                      (2 : Int) ^ t * binomZ (M - c) t *
                        Delta (M + 1 - 2 * (d + t / 2 + 1)) h ((d + t / 2 + 1 : Nat) : Int) := by
                    rw [Int.mul_assoc, Int.mul_comm (binomZ (M - c) t), ← Int.mul_assoc]
                    exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdvd)
                  exact dvd_two_pow_mono (by omega) hmul
                · simp [htp]
              · let d := c / 2
                have hcd : (c : Int) + 1 = 2 * ((d + 1 : Nat) : Int) := by omega
                rw [hcd, delta_two_mul_two_mul_even]
                apply sumRange_dvd
                intro t ht
                by_cases htp : t % 2 = 0
                · simp only [htp, ↓reduceIte]
                  have hle : 2 * (d + 1 + t / 2) ≤ M + 1 := by omega
                  have hn' : M - c - t = M + 1 - 2 * (d + 1 + t / 2) := by omega
                  have hc' : ((d + 1 : Nat) : Int) + ((t / 2 : Nat) : Int) = ((d + 1 + t / 2 : Nat) : Int) := by omega
                  rw [hn', hc']
                  have hdvd := ih1 h (d + 1 + t / 2) hjM (by omega) hle
                  have hmul : (2 : Int) ^ (t + (popcount h - (d + 1 + t / 2))) ∣
                      (2 : Int) ^ t * binomZ (M - c) t *
                        Delta (M + 1 - 2 * (d + 1 + t / 2)) h ((d + 1 + t / 2 : Nat) : Int) := by
                    rw [Int.mul_assoc, Int.mul_comm (binomZ (M - c) t), ← Int.mul_assoc]
                    exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdvd)
                  exact dvd_two_pow_mono (by omega) hmul
                · simp [htp]
          · have hjh : j = 2 * h + 1 := by omega
            have hsub : 2 * M + 1 - 2 * c = 2 * (M - c) + 1 := by omega
            rw [hjh, popcount_two_mul_add_one, hsub]
            by_cases hcpar : c % 2 = 0
            · let d := c / 2
              have hcd : (c : Int) = 2 * (d : Int) := by omega
              rw [hcd, delta_odd_odd_even]
              apply sumRange_dvd
              intro t ht
              by_cases htp : t % 2 = 1
              · simp only [htp, ↓reduceIte]
                have hle0 : 2 * (d + t / 2) ≤ M := by omega
                have hle1 : 2 * (d + t / 2 + 1) ≤ M + 1 := by omega
                have hn0 : M - c - t + 1 = M - 2 * (d + t / 2) := by omega
                have hn1 : M - c - t = M + 1 - 2 * (d + t / 2 + 1) := by omega
                have hc0 : (d : Int) + ((t / 2 : Nat) : Int) = ((d + t / 2 : Nat) : Int) := by omega
                have hc1 : (d : Int) + ((t / 2 : Nat) : Int) + 1 = ((d + t / 2 + 1 : Nat) : Int) := by omega
                rw [hn0, hn1, hc1, hc0]
                have hd0 := ih0 h (d + t / 2) hjM hle0
                have hd1 := dvd_two_mul_of_dvd (ih1 h (d + t / 2 + 1) hjM (by omega) hle1)
                have hdiff : (2 : Int) ^ (popcount h - (d + t / 2)) ∣
                    (Delta (M - 2 * (d + t / 2)) h ((d + t / 2 : Nat) : Int) -
                     2 * Delta (M + 1 - 2 * (d + t / 2 + 1)) h ((d + t / 2 + 1 : Nat) : Int)) :=
                  dvd_sub_of_dvd hd0 (dvd_two_pow_mono (by omega) hd1)
                have hmul : (2 : Int) ^ (t + (popcount h - (d + t / 2))) ∣
                    (2 : Int) ^ t * binomZ (M - c) t *
                      (Delta (M - 2 * (d + t / 2)) h ((d + t / 2 : Nat) : Int) -
                       2 * Delta (M + 1 - 2 * (d + t / 2 + 1)) h ((d + t / 2 + 1 : Nat) : Int)) := by
                  rw [Int.mul_assoc, Int.mul_comm (binomZ (M - c) t), ← Int.mul_assoc]
                  exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdiff)
                exact dvd_two_pow_mono (by omega) hmul
              · simp [htp]
            · let d := c / 2
              have hcd : (c : Int) = 2 * (d : Int) + 1 := by omega
              rw [hcd, delta_odd_odd_odd]
              apply sumRange_dvd
              intro t ht
              by_cases htp : t % 2 = 0
              · simp only [htp, ↓reduceIte]
                have hle0 : 2 * (d + t / 2) ≤ M := by omega
                have hle1 : 2 * (d + t / 2 + 1) ≤ M + 1 := by omega
                have hn0 : M - c - t + 1 = M - 2 * (d + t / 2) := by omega
                have hn1 : M - c - t = M + 1 - 2 * (d + t / 2 + 1) := by omega
                have hc0 : (d : Int) + ((t / 2 : Nat) : Int) = ((d + t / 2 : Nat) : Int) := by omega
                have hc1 : (d : Int) + ((t / 2 : Nat) : Int) + 1 = ((d + t / 2 + 1 : Nat) : Int) := by omega
                rw [hn0, hn1, hc1, hc0]
                have hd0 := ih0 h (d + t / 2) hjM hle0
                have hd1 := dvd_two_mul_of_dvd (ih1 h (d + t / 2 + 1) hjM (by omega) hle1)
                have hdiff : (2 : Int) ^ (popcount h - (d + t / 2)) ∣
                    (Delta (M - 2 * (d + t / 2)) h ((d + t / 2 : Nat) : Int) -
                     2 * Delta (M + 1 - 2 * (d + t / 2 + 1)) h ((d + t / 2 + 1 : Nat) : Int)) :=
                  dvd_sub_of_dvd hd0 (dvd_two_pow_mono (by omega) hd1)
                have hmul : (2 : Int) ^ (t + (popcount h - (d + t / 2))) ∣
                    (2 : Int) ^ t * binomZ (M - c) t *
                      (Delta (M - 2 * (d + t / 2)) h ((d + t / 2 : Nat) : Int) -
                       2 * Delta (M + 1 - 2 * (d + t / 2 + 1)) h ((d + t / 2 + 1 : Nat) : Int)) := by
                  rw [Int.mul_assoc, Int.mul_comm (binomZ (M - c) t), ← Int.mul_assoc]
                  exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hdiff)
                exact dvd_two_pow_mono (by omega) hmul
              · simp [htp]
        · intro j c hj hc1 hc2
          have hjM : Submask (j / 2) M := (submask_two_mul_add_one_iff j M).mp hj
          let h := j / 2
          have hsub : 2 * M + 1 + 1 - 2 * c = 2 * (M + 1 - c) := by omega
          rw [hsub]
          by_cases hjpar : j % 2 = 0
          · have hjh : j = 2 * h := by omega
            rw [hjh, popcount_two_mul]
            exact dvd_two_pow_mono (by omega) (hCase4Strong h c hjM hc1 (by omega))
          · have hjh : j = 2 * h + 1 := by omega
            rw [hjh, popcount_two_mul_add_one, delta_even_odd]
            apply dvd_sub_of_dvd
            · have hm1 : M + 1 - c = M - (c - 1) := by omega
              have hc1' : (c : Int) - 1 = ((c - 1 : Nat) : Int) := by omega
              rw [hm1, hc1']
              have hd := hEven0 h (c - 1) hjM (by omega)
              exact dvd_two_pow_mono (by omega) hd
            · exact hCase4Strong h c hjM hc1 (by omega)

/-! ### Exact Mod-2 Leading-Bit Transducer & Closed Form `E(N)` -/

theorem lowBitAux_ge (fuel N : Nat) (h : N ≤ fuel) :
    lowBitAux (fuel + 1) N = lowBitAux fuel N := by
  induction fuel generalizing N with
  | zero =>
    have hN : N = 0 := by omega
    subst hN; rfl
  | succ f ih =>
    unfold lowBitAux
    by_cases hN : N = 0
    · simp [hN]
    · by_cases hp : N % 2 = 0
      · simp only [hN, hp, ↓reduceIte]
        rw [ih (N / 2) (by omega)]
      · simp [hN, hp]

theorem lowBitAux_eq_of_ge {f1 f2 N : Nat} (h1 : N ≤ f1) (h2 : N ≤ f2) :
    lowBitAux f1 N = lowBitAux f2 N := by
  have hgen : ∀ d f, N ≤ f → lowBitAux (f + d) N = lowBitAux f N := by
    intro d; induction d with
    | zero => intro f _; rfl
    | succ d ih =>
      intro f hf
      have : f + (d + 1) = (f + d) + 1 := by omega
      rw [this, lowBitAux_ge (f + d) N (by omega), ih f hf]
  have e1 := hgen (f1 - N) N (Nat.le_refl N)
  have e2 := hgen (f2 - N) N (Nat.le_refl N)
  rw [Nat.add_sub_of_le h1] at e1
  rw [Nat.add_sub_of_le h2] at e2
  rw [e1, e2]

theorem lowBit_two_mul (M : Nat) (hM : M ≠ 0) : lowBit (2 * M) = 2 * lowBit M := by
  unfold lowBit
  have h1 : 2 * M = (2 * M - 1) + 1 := by omega
  conv => lhs; rw [h1]; unfold lowBitAux
  have hne : (2 * M - 1) + 1 ≠ 0 := by omega
  have hpar : ((2 * M - 1) + 1) % 2 = 0 := by omega
  have hdiv : ((2 * M - 1) + 1) / 2 = M := by omega
  simp only [hne, hpar, hdiv, ↓reduceIte]
  rw [lowBitAux_eq_of_ge (f1 := 2 * M - 1) (f2 := M) (by omega) (Nat.le_refl M)]

theorem lowBit_odd (M : Nat) : lowBit (2 * M + 1) = 1 := by
  unfold lowBit lowBitAux
  simp

theorem alphaCF_eq_true_iff (N j : Nat) :
    alphaCF N j = true ↔ Submask j (endpointMask N) := by
  unfold alphaCF Submask; simp

theorem alphaCF_two_mul (M h : Nat) :
    alphaCF (2 * M) (2 * h) = alphaCF M h := by
  unfold alphaCF
  rw [endpointMask_two_mul, and_two_mul_two_mul]
  exact beq_two_mul_eq (h &&& endpointMask M) h

theorem betaCF_two_mul (M h : Nat) :
    betaCF (2 * M) (2 * h) = betaCF M h := by
  by_cases hM : M = 0
  · subst hM; rfl
  · unfold betaCF
    have h2M : 2 * M ≠ 0 := by omega
    simp only [beq_iff_eq, hM, h2M, ↓reduceIte]
    rw [lowBit_two_mul M hM, endpointMask_two_mul, and_two_mul_two_mul, xor_two_mul_two_mul, and_two_mul_two_mul]
    have h1 : (2 * (h &&& lowBit M) != 0) = (h &&& lowBit M != 0) := by
      simp only [bne, beq_two_mul_zero]
    have h2 : (2 * ((h ^^^ lowBit M) &&& endpointMask M) == 2 * (h ^^^ lowBit M)) =
        ((h ^^^ lowBit M) &&& endpointMask M == h ^^^ lowBit M) :=
      beq_two_mul_eq ((h ^^^ lowBit M) &&& endpointMask M) (h ^^^ lowBit M)
    rw [h1, h2]

theorem betaCF_odd_even (M h : Nat) :
    betaCF (2 * M + 1) (2 * h) = false := by
  unfold betaCF
  have h1 : 2 * M + 1 ≠ 0 := by omega
  rw [lowBit_odd]
  have h2 : (2 * h) &&& 1 = 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases i with
    | zero => rw [testBit_two_mul_zero]; rfl
    | succ j =>
      have : (1 : Nat).testBit (j + 1) = false := by rw [Nat.testBit_succ]; simp
      simp [this]
  simp [h2]

theorem alphaCF_odd_even (M h : Nat) :
    alphaCF (2 * M + 1) (2 * h) = xor (alphaCF M h) (M.testBit 0 && betaCF M h) := by
  cases hM0 : M.testBit 0
  · simp only [Bool.false_and, Bool.xor_false]
    apply Bool.eq_iff_iff.mpr
    rw [alphaCF_eq_true_iff, alphaCF_eq_true_iff, submask_iff_testBit, submask_iff_testBit]
    constructor
    · intro H i hi
      have h1 : (2 * h).testBit (i + 1) = true := by rw [testBit_two_mul_succ]; exact hi
      have h2 := H (i + 1) h1
      cases i with
      | zero =>
        rw [endpointMask_two_mul_add_one_one] at h2
        simp [hM0] at h2
      | succ j =>
        rw [endpointMask_two_mul_add_one_ge2] at h2
        exact h2
    · intro H i hi
      cases i with
      | zero => rw [testBit_two_mul_zero] at hi; contradiction
      | succ i' =>
        rw [testBit_two_mul_succ] at hi
        have h1 := H i' hi
        cases i' with
        | zero =>
          rw [testBit_endpointMask_zero] at h1
          simp [hM0] at h1
        | succ j =>
          rw [endpointMask_two_mul_add_one_ge2]
          exact h1
  · have hMne : M ≠ 0 := by intro hz; subst hz; simp at hM0
    have hModd : M % 2 = 1 := by rw [Nat.testBit_zero] at hM0; simpa using hM0
    have hL : lowBit M = 1 := by
      have : M = 2 * (M / 2) + 1 := by omega
      rw [this, lowBit_odd]
    simp only [Bool.true_and]
    cases hh0 : h.testBit 0
    · have hband : h &&& lowBit M = 0 := by
        rw [hL]
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_and, Nat.zero_testBit]
        cases i with
        | zero => simp [hh0]
        | succ j =>
          have : (1 : Nat).testBit (j + 1) = false := by rw [Nat.testBit_succ]; simp
          simp [this]
      have hbeta : betaCF M h = false := by
        unfold betaCF; simp [hMne, hband]
      rw [hbeta, Bool.xor_false]
      apply Bool.eq_iff_iff.mpr
      rw [alphaCF_eq_true_iff, alphaCF_eq_true_iff, submask_iff_testBit, submask_iff_testBit]
      constructor
      · intro H i hi
        have h1 : (2 * h).testBit (i + 1) = true := by rw [testBit_two_mul_succ]; exact hi
        have h2 := H (i + 1) h1
        cases i with
        | zero => rw [hh0] at hi; contradiction
        | succ j => rw [endpointMask_two_mul_add_one_ge2] at h2; exact h2
      · intro H i hi
        cases i with
        | zero => rw [testBit_two_mul_zero] at hi; contradiction
        | succ i' =>
          rw [testBit_two_mul_succ] at hi
          cases i' with
          | zero => rw [hh0] at hi; contradiction
          | succ j =>
            rw [endpointMask_two_mul_add_one_ge2]
            exact H (j + 1) hi
    · have hband : h &&& lowBit M = 1 := by
        rw [hL]
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_and]
        cases i with
        | zero => simp [hh0]
        | succ j =>
          have : (1 : Nat).testBit (j + 1) = false := by rw [Nat.testBit_succ]; simp
          simp [this]
      have hbeta_iff : betaCF M h = true ↔ ∀ j, h.testBit (j + 1) = true → (endpointMask M).testBit (j + 1) = true := by
        unfold betaCF
        have h1ne0 : (1 != 0) = true := rfl
        simp only [beq_iff_eq, hMne, ↓reduceIte, hband, h1ne0, Bool.true_and]
        rw [hL]
        change Submask (h ^^^ 1) (endpointMask M) ↔ _
        rw [submask_iff_testBit]
        constructor
        · intro H j hj
          have hx : (h ^^^ 1).testBit (j + 1) = true := by
            rw [Nat.testBit_xor, hj]
            have : (1 : Nat).testBit (j + 1) = false := by rw [Nat.testBit_succ]; simp
            simp [this]
          exact H (j + 1) hx
        · intro H i hi
          cases i with
          | zero =>
            rw [Nat.testBit_xor, hh0] at hi; simp at hi
          | succ j =>
            rw [Nat.testBit_xor] at hi
            have : (1 : Nat).testBit (j + 1) = false := by rw [Nat.testBit_succ]; simp
            rw [this, Bool.xor_false] at hi
            exact H j hi
      have hEM0 : (endpointMask M).testBit 0 = M.testBit 1 := by
        rw [testBit_endpointMask_zero, hM0]; rfl
      have halphaM_iff : alphaCF M h = true ↔
          (M.testBit 1 = true ∧ ∀ j, h.testBit (j + 1) = true → (endpointMask M).testBit (j + 1) = true) := by
        rw [alphaCF_eq_true_iff, submask_iff_testBit]
        constructor
        · intro H
          exact ⟨by rw [← hEM0]; exact H 0 hh0, fun j hj => H (j + 1) hj⟩
        · rintro ⟨h1, hrest⟩ i hi
          cases i with
          | zero => rw [hEM0]; exact h1
          | succ j => exact hrest j hi
      have halphaNew_iff : alphaCF (2 * M + 1) (2 * h) = true ↔
          (M.testBit 1 = false ∧ ∀ j, h.testBit (j + 1) = true → (endpointMask M).testBit (j + 1) = true) := by
        rw [alphaCF_eq_true_iff, submask_iff_testBit]
        constructor
        · intro H
          constructor
          · have h1 := H 1 (by rw [testBit_two_mul_succ]; exact hh0)
            rw [endpointMask_two_mul_add_one_one, hM0] at h1
            cases hm1 : M.testBit 1 <;> simp_all
          · intro j hj
            have h1 := H (j + 2) (by rw [testBit_two_mul_succ]; exact hj)
            rw [endpointMask_two_mul_add_one_ge2] at h1
            exact h1
        · rintro ⟨h1, hrest⟩ i hi
          cases i with
          | zero => rw [testBit_two_mul_zero] at hi; contradiction
          | succ i' =>
            rw [testBit_two_mul_succ] at hi
            cases i' with
            | zero => rw [endpointMask_two_mul_add_one_one, hM0, h1]; rfl
            | succ j => rw [endpointMask_two_mul_add_one_ge2]; exact hrest j hi
      cases hb : betaCF M h
      · have hnb : ¬ (∀ j, h.testBit (j + 1) = true → (endpointMask M).testBit (j + 1) = true) := by
          intro H; exact Bool.false_ne_true (hb ▸ hbeta_iff.mpr H)
        have haM : alphaCF M h = false := by
          cases h' : alphaCF M h
          · rfl
          · exfalso; exact hnb (halphaM_iff.mp h').2
        have haNew : alphaCF (2 * M + 1) (2 * h) = false := by
          cases h' : alphaCF (2 * M + 1) (2 * h)
          · rfl
          · exfalso; exact hnb (halphaNew_iff.mp h').2
        rw [haNew, haM]; rfl
      · have hrest := hbeta_iff.mp hb
        cases hm1 : M.testBit 1
        · have haM : alphaCF M h = false := by
            cases h' : alphaCF M h
            · rfl
            · have := (halphaM_iff.mp h').1; rw [hm1] at this; contradiction
          have haNew : alphaCF (2 * M + 1) (2 * h) = true := halphaNew_iff.mpr ⟨hm1, hrest⟩
          rw [haNew, haM]; rfl
        · have haM : alphaCF M h = true := halphaM_iff.mpr ⟨hm1, hrest⟩
          have haNew : alphaCF (2 * M + 1) (2 * h) = false := by
            cases h' : alphaCF (2 * M + 1) (2 * h)
            · rfl
            · have := (halphaNew_iff.mp h').1; rw [hm1] at this; contradiction
          rw [haNew, haM]; rfl

theorem alphaCF_odd_odd (M h : Nat) :
    alphaCF (2 * M + 1) (2 * h + 1) = (M.testBit 0 && xor (alphaCF M h) (betaCF M h)) := by
  cases hM0 : M.testBit 0
  · simp only [Bool.false_and]
    cases h' : alphaCF (2 * M + 1) (2 * h + 1)
    · rfl
    · exfalso
      have hsub := alphaCF_eq_true_iff (2 * M + 1) (2 * h + 1) |>.mp h'
      have hb0 := (submask_iff_testBit.mp hsub) 0 (testBit_two_mul_add_one_zero h)
      rw [endpointMask_two_mul_add_one_zero, hM0] at hb0
      contradiction
  · simp only [Bool.true_and]
    have heq : alphaCF (2 * M + 1) (2 * h + 1) = alphaCF (2 * M + 1) (2 * h) := by
      apply Bool.eq_iff_iff.mpr
      rw [alphaCF_eq_true_iff, alphaCF_eq_true_iff, submask_iff_testBit, submask_iff_testBit]
      constructor
      · intro H i hi
        cases i with
        | zero => rw [testBit_two_mul_zero] at hi; contradiction
        | succ j =>
          rw [testBit_two_mul_succ] at hi
          exact H (j + 1) (by rw [testBit_two_mul_add_one_succ]; exact hi)
      · intro H i hi
        cases i with
        | zero => rw [endpointMask_two_mul_add_one_zero]; exact hM0
        | succ j =>
          rw [testBit_two_mul_add_one_succ] at hi
          exact H (j + 1) (by rw [testBit_two_mul_succ]; exact hi)
    rw [heq, alphaCF_odd_even, hM0, Bool.true_and]

theorem betaCF_odd_odd (M h : Nat) :
    betaCF (2 * M + 1) (2 * h + 1) = alphaCF (2 * M + 1) (2 * h) := by
  unfold betaCF alphaCF
  have h1 : 2 * M + 1 ≠ 0 := by omega
  rw [lowBit_odd]
  have hand : (2 * h + 1) &&& 1 = 1 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and]
    cases i with
    | zero => rw [testBit_two_mul_add_one_zero]; rfl
    | succ j =>
      have : (1 : Nat).testBit (j + 1) = false := by rw [Nat.testBit_succ]; simp
      simp [this]
  have hxor : (2 * h + 1) ^^^ 1 = 2 * h := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_xor]
    cases i with
    | zero => rw [testBit_two_mul_add_one_zero, testBit_two_mul_zero]; rfl
    | succ j =>
      rw [testBit_two_mul_add_one_succ, testBit_two_mul_succ]
      have : (1 : Nat).testBit (j + 1) = false := by rw [Nat.testBit_succ]; simp
      simp [this]
  simp [hand, hxor]

theorem dvd_two_bool_xor (a b : Bool) :
    (2 : Int) ∣ (boolToInt a + boolToInt b - boolToInt (xor a b)) := by
  cases a <;> cases b <;> decide

theorem dvd_two_bool_xor_sub (a b : Bool) :
    (2 : Int) ∣ (boolToInt a - boolToInt b - boolToInt (xor a b)) := by
  cases a <;> cases b <;> decide

theorem dvd_two_mul_bool (M : Nat) (b : Bool) :
    (2 : Int) ∣ ((M : Int) * boolToInt b - boolToInt (M.testBit 0 && b)) := by
  cases hb : b
  · simp [boolToInt]
  · simp only [boolToInt, ↓reduceIte, Int.mul_one, Bool.and_true]
    rw [Nat.testBit_zero]
    by_cases hp : M % 2 = 0
    · refine ⟨(M / 2 : Nat), ?_⟩
      simp [hp]; omega
    · have hp1 : M % 2 = 1 := by omega
      refine ⟨(M / 2 : Nat), ?_⟩
      simp [hp1]; omega

/-- Helper: `Delta n 0 1 = 0`. -/
theorem delta_zero_shift_one (n : Nat) : Delta n 0 1 = 0 := by
  unfold Delta; rw [mobius_zero]; exact binomZ_neg n (-1) (by omega)

/-- Stage 1 Master Theorem:
    For EVERY `N : Nat` and EVERY submask `j <=_2 N`:
    1. `Delta N j 0 ≡ 2^(popcount j) * [j <=_2 E(N)]  (mod 2^(popcount j + 1))`
    2. For `j ≠ 0` (hence `N >= 1`),
       `Delta (N - 1) j 1 ≡ 2^(popcount j - 1) * betaCF(N, j)  (mod 2^(popcount j))`. -/
theorem delta_exact_mod2 (N : Nat) :
    (∀ j : Nat, Submask j N →
      (2 : Int) ^ (popcount j + 1) ∣
        (Delta N j 0 - (2 : Int) ^ (popcount j) * boolToInt (alphaCF N j))) ∧
    (∀ j : Nat, Submask j N → j ≠ 0 →
      (2 : Int) ^ (popcount j) ∣
        (Delta (N - 1) j 1 - (2 : Int) ^ (popcount j - 1) * boolToInt (betaCF N j))) := by
  induction N using nat_strong_ind with
  | step N ih =>
    by_cases hN0 : N = 0
    · subst hN0
      constructor
      · intro j hj
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero (submask_le hj)
        subst hj0
        have hval : Delta 0 0 0 = 1 := by unfold Delta; rw [mobius_zero]; rfl
        have ha : alphaCF 0 0 = true := rfl
        rw [hval, ha, popcount_zero]; decide
      · intro j hj hjne
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero (submask_le hj)
        exact absurd hj0 hjne
    · by_cases hNpar : N % 2 = 0
      · let M := N / 2
        have hNM : N = 2 * M := by omega
        obtain ⟨ihA, ihB⟩ := ih M (by omega)
        obtain ⟨div0, div1⟩ := delta_two_state_div M
        rw [hNM]
        constructor
        · intro j hj
          obtain ⟨hj0, hjM⟩ := (submask_two_mul_iff j M).mp hj
          let h := j / 2
          have hjh : j = 2 * h := by omega
          rw [hjh, popcount_two_mul, alphaCF_two_mul]
          have h0 : (0 : Int) = 2 * (0 : Int) := rfl
          rw [h0, delta_two_mul_two_mul_even, sumRange_split_first M]
          have ht0 : (if (0 : Nat) % 2 = 0 then (2 : Int) ^ 0 * binomZ M ((0 : Nat) : Int) * Delta (M - 0) h (0 + ((0 / 2 : Nat) : Int)) else 0) =
              Delta M h 0 := by simp [binomZ_zero_right]
          rw [ht0]
          have hreord : Delta M h 0 +
              sumRange M (fun i => if (i + 1) % 2 = 0 then (2 : Int) ^ (i + 1) * binomZ M ((i + 1 : Nat) : Int) *
                Delta (M - (i + 1)) h (0 + (((i + 1) / 2 : Nat) : Int)) else 0) -
              (2 : Int) ^ popcount h * boolToInt (alphaCF M h) =
              (Delta M h 0 - (2 : Int) ^ popcount h * boolToInt (alphaCF M h)) +
              sumRange M (fun i => if (i + 1) % 2 = 0 then (2 : Int) ^ (i + 1) * binomZ M ((i + 1 : Nat) : Int) *
                Delta (M - (i + 1)) h (0 + (((i + 1) / 2 : Nat) : Int)) else 0) := by omega
          rw [hreord]
          apply dvd_add_of_dvd (ihA h hjM)
          apply sumRange_dvd
          intro i hi
          by_cases hip : (i + 1) % 2 = 0
          · simp only [hip, ↓reduceIte]
            let u := (i + 1) / 2
            have hle : 2 * u ≤ M := by omega
            have hn' : M - (i + 1) = M - 2 * u := by omega
            have hc' : (0 : Int) + (u : Int) = (u : Int) := by omega
            rw [hn', hc']
            have hd := div0 h u hjM hle
            have hmul : (2 : Int) ^ ((i + 1) + (popcount h - u)) ∣
                (2 : Int) ^ (i + 1) * binomZ M ((i + 1 : Nat) : Int) * Delta (M - 2 * u) h (u : Int) := by
              rw [Int.mul_assoc, Int.mul_comm (binomZ M ((i + 1 : Nat) : Int)), ← Int.mul_assoc]
              exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left (i + 1) _ hd)
            exact dvd_two_pow_mono (by omega) hmul
          · simp only [hip, ↓reduceIte]; exact ⟨0, by simp⟩
        · intro j hj hjne
          obtain ⟨hj0, hjM⟩ := (submask_two_mul_iff j M).mp hj
          let h := j / 2
          have hjh : j = 2 * h := by omega
          have hne : h ≠ 0 := by omega
          have hM1 : 2 * M - 1 = 2 * (M - 1) + 1 := by omega
          rw [hjh, popcount_two_mul, betaCF_two_mul, hM1, delta_odd_even]
          have hterm1 : (2 : Int) ^ popcount h ∣ Delta (2 * (M - 1)) (2 * h) 1 := by
            have h1eq : (1 : Int) = 2 * (0 : Int) + 1 := rfl
            rw [h1eq, delta_two_mul_two_mul_odd]
            apply sumRange_dvd
            intro t ht
            by_cases htp : t % 2 = 1
            · simp only [htp, ↓reduceIte]
              let u := t / 2 + 1
              have hle : 2 * u ≤ M := by omega
              have hn' : M - 1 - t = M - 2 * u := by omega
              have hc' : (0 : Int) + ((t / 2 : Nat) : Int) + 1 = (u : Int) := by omega
              rw [hn', hc']
              have hd := div0 h u hjM hle
              have hmul : (2 : Int) ^ (t + (popcount h - u)) ∣
                  (2 : Int) ^ t * binomZ (M - 1) t * Delta (M - 2 * u) h (u : Int) := by
                rw [Int.mul_assoc, Int.mul_comm (binomZ (M - 1) t), ← Int.mul_assoc]
                exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left t _ hd)
              exact dvd_two_pow_mono (by omega) hmul
            · simp [htp]
          have hterm2 : (2 : Int) ^ popcount h ∣
              (Delta (2 * (M - 1)) (2 * h) (1 + 1) - (2 : Int) ^ (popcount h - 1) * boolToInt (betaCF M h)) := by
            have h2eq : (1 : Int) + 1 = 2 * (1 : Int) := rfl
            rw [h2eq, delta_two_mul_two_mul_even, sumRange_split_first (M - 1)]
            have ht0 : (if (0 : Nat) % 2 = 0 then (2 : Int) ^ 0 * binomZ (M - 1) ((0 : Nat) : Int) * Delta (M - 1 - 0) h (1 + ((0 / 2 : Nat) : Int)) else 0) =
                Delta (M - 1) h 1 := by simp [binomZ_zero_right]
            rw [ht0]
            have hreord : Delta (M - 1) h 1 +
                sumRange (M - 1) (fun i => if (i + 1) % 2 = 0 then (2 : Int) ^ (i + 1) * binomZ (M - 1) ((i + 1 : Nat) : Int) *
                  Delta (M - 1 - (i + 1)) h (1 + (((i + 1) / 2 : Nat) : Int)) else 0) -
                (2 : Int) ^ (popcount h - 1) * boolToInt (betaCF M h) =
                (Delta (M - 1) h 1 - (2 : Int) ^ (popcount h - 1) * boolToInt (betaCF M h)) +
                sumRange (M - 1) (fun i => if (i + 1) % 2 = 0 then (2 : Int) ^ (i + 1) * binomZ (M - 1) ((i + 1 : Nat) : Int) *
                  Delta (M - 1 - (i + 1)) h (1 + (((i + 1) / 2 : Nat) : Int)) else 0) := by omega
            rw [hreord]
            apply dvd_add_of_dvd (ihB h hjM hne)
            apply sumRange_dvd
            intro i hi
            by_cases hip : (i + 1) % 2 = 0
            · simp only [hip, ↓reduceIte]
              let u := 1 + (i + 1) / 2
              have hle : 2 * u ≤ M + 1 := by omega
              have hn' : M - 1 - (i + 1) = M + 1 - 2 * u := by omega
              have hc' : (1 : Int) + (((i + 1) / 2 : Nat) : Int) = (u : Int) := by omega
              rw [hn', hc']
              have hd := div1 h u hjM (by omega) hle
              have hmul : (2 : Int) ^ ((i + 1) + (popcount h - u)) ∣
                  (2 : Int) ^ (i + 1) * binomZ (M - 1) ((i + 1 : Nat) : Int) * Delta (M + 1 - 2 * u) h (u : Int) := by
                rw [Int.mul_assoc, Int.mul_comm (binomZ (M - 1) ((i + 1 : Nat) : Int)), ← Int.mul_assoc]
                exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left (i + 1) _ hd)
              exact dvd_two_pow_mono (by omega) hmul
            · simp only [hip, ↓reduceIte]; exact ⟨0, by simp⟩
          have hreord2 : Delta (2 * (M - 1)) (2 * h) 1 + Delta (2 * (M - 1)) (2 * h) (1 + 1) -
              (2 : Int) ^ (popcount h - 1) * boolToInt (betaCF M h) =
              Delta (2 * (M - 1)) (2 * h) 1 +
              (Delta (2 * (M - 1)) (2 * h) (1 + 1) - (2 : Int) ^ (popcount h - 1) * boolToInt (betaCF M h)) := by omega
          rw [hreord2]
          exact dvd_add_of_dvd hterm1 hterm2
      · let M := N / 2
        have hNM : N = 2 * M + 1 := by omega
        obtain ⟨ihA, ihB⟩ := ih M (by omega)
        obtain ⟨div0, div1⟩ := delta_two_state_div M
        have hD2M0 : ∀ h : Nat, Submask h M →
            (2 : Int) ^ (popcount h + 1) ∣
              (Delta (2 * M) (2 * h) 0 - (2 : Int) ^ popcount h * boolToInt (alphaCF M h)) := by
          intro h hhM
          have h0 : (0 : Int) = 2 * (0 : Int) := rfl
          rw [h0, delta_two_mul_two_mul_even, sumRange_split_first M]
          have ht0 : (if (0 : Nat) % 2 = 0 then (2 : Int) ^ 0 * binomZ M ((0 : Nat) : Int) * Delta (M - 0) h (0 + ((0 / 2 : Nat) : Int)) else 0) =
              Delta M h 0 := by simp [binomZ_zero_right]
          rw [ht0]
          have hreord : Delta M h 0 +
              sumRange M (fun i => if (i + 1) % 2 = 0 then (2 : Int) ^ (i + 1) * binomZ M ((i + 1 : Nat) : Int) *
                Delta (M - (i + 1)) h (0 + (((i + 1) / 2 : Nat) : Int)) else 0) -
              (2 : Int) ^ popcount h * boolToInt (alphaCF M h) =
              (Delta M h 0 - (2 : Int) ^ popcount h * boolToInt (alphaCF M h)) +
              sumRange M (fun i => if (i + 1) % 2 = 0 then (2 : Int) ^ (i + 1) * binomZ M ((i + 1 : Nat) : Int) *
                Delta (M - (i + 1)) h (0 + (((i + 1) / 2 : Nat) : Int)) else 0) := by omega
          rw [hreord]
          apply dvd_add_of_dvd (ihA h hhM)
          apply sumRange_dvd
          intro i hi
          by_cases hip : (i + 1) % 2 = 0
          · simp only [hip, ↓reduceIte]
            let u := (i + 1) / 2
            have hle : 2 * u ≤ M := by omega
            have hn' : M - (i + 1) = M - 2 * u := by omega
            have hc' : (0 : Int) + (u : Int) = (u : Int) := by omega
            rw [hn', hc']
            have hd := div0 h u hhM hle
            have hmul : (2 : Int) ^ ((i + 1) + (popcount h - u)) ∣
                (2 : Int) ^ (i + 1) * binomZ M ((i + 1 : Nat) : Int) * Delta (M - 2 * u) h (u : Int) := by
              rw [Int.mul_assoc, Int.mul_comm (binomZ M ((i + 1 : Nat) : Int)), ← Int.mul_assoc]
              exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left (i + 1) _ hd)
            exact dvd_two_pow_mono (by omega) hmul
          · simp only [hip, ↓reduceIte]; exact ⟨0, by simp⟩
        have hD2M1 : ∀ h : Nat, Submask h M →
            (2 : Int) ^ (popcount h + 1) ∣
              (Delta (2 * M) (2 * h) 1 - (2 : Int) ^ popcount h * boolToInt (M.testBit 0 && betaCF M h)) := by
          intro h hhM
          by_cases hh0 : h = 0
          · subst hh0
            rw [Nat.mul_zero, delta_zero_shift_one, popcount_zero]
            have hb0 : betaCF M 0 = false := by
              unfold betaCF; by_cases hM : M = 0 <;> simp [hM]
            rw [hb0]; simp [boolToInt]
          · have hMpos : 1 ≤ M := by
              have := submask_le hhM; omega
            have hpc_pos : 1 ≤ popcount h := popcount_pos_of_ne_zero hh0
            have h1eq : (1 : Int) = 2 * (0 : Int) + 1 := rfl
            rw [h1eq, delta_two_mul_two_mul_odd]
            have hMsp : M + 1 = (M - 1 + 1) + 1 := by omega
            rw [hMsp, sumRange_split_first, sumRange_split_first]
            have ht0 : (if (0 : Nat) % 2 = 1 then (2 : Int) ^ 0 * binomZ M ((0 : Nat) : Int) * Delta (M - 0) h (0 + ((0 / 2 : Nat) : Int) + 1) else 0) = 0 := by simp
            have ht1 : (if (0 + 1 : Nat) % 2 = 1 then (2 : Int) ^ (0 + 1) * binomZ M ((0 + 1 : Nat) : Int) * Delta (M - (0 + 1)) h (0 + (((0 + 1) / 2 : Nat) : Int) + 1) else 0) =
                2 * (M : Int) * Delta (M - 1) h 1 := by
              simp [binomZ_one_right]
            rw [ht0, ht1, Int.zero_add]
            have htail : (2 : Int) ^ (popcount h + 1) ∣
                sumRange (M - 1) (fun i =>
                  if (i + 2) % 2 = 1 then
                    (2 : Int) ^ (i + 2) * binomZ M ((i + 2 : Nat) : Int) * Delta (M - (i + 2)) h (0 + (((i + 2) / 2 : Nat) : Int) + 1)
                  else 0) := by
              apply sumRange_dvd
              intro i hi
              by_cases hip : (i + 2) % 2 = 1
              · simp only [hip, ↓reduceIte]
                let u := (i + 2) / 2 + 1
                have hle : 2 * u ≤ M + 1 := by omega
                have hn' : M - (i + 2) = M + 1 - 2 * u := by omega
                have hc' : (0 : Int) + (((i + 2) / 2 : Nat) : Int) + 1 = (u : Int) := by omega
                rw [hn', hc']
                have hd := div1 h u hhM (by omega) hle
                have hmul : (2 : Int) ^ ((i + 2) + (popcount h - u)) ∣
                    (2 : Int) ^ (i + 2) * binomZ M ((i + 2 : Nat) : Int) * Delta (M + 1 - 2 * u) h (u : Int) := by
                  rw [Int.mul_assoc, Int.mul_comm (binomZ M ((i + 2 : Nat) : Int)), ← Int.mul_assoc]
                  exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left (i + 2) _ hd)
                exact dvd_two_pow_mono (by omega) hmul
              · simp only [hip, ↓reduceIte]; exact ⟨0, by simp⟩
            have hmain : (2 : Int) ^ (popcount h + 1) ∣
                (2 * (M : Int) * Delta (M - 1) h 1 - (2 : Int) ^ popcount h * boolToInt (M.testBit 0 && betaCF M h)) := by
              have hstep1 := dvd_mul_left_of_dvd (M : Int) (dvd_two_mul_of_dvd (ihB h hhM hh0))
              have hstep2 := dvd_two_pow_mul_left (popcount h) 1 (dvd_two_mul_bool M (betaCF M h))
              have hpow : (2 : Int) * (2 : Int) ^ (popcount h - 1) = (2 : Int) ^ popcount h := by
                have h1 : popcount h = (popcount h - 1) + 1 := by omega
                conv => rhs; rw [h1, Int.pow_succ]
                rw [Int.mul_comm]
              have hcomb : 2 * (M : Int) * Delta (M - 1) h 1 - (2 : Int) ^ popcount h * boolToInt (M.testBit 0 && betaCF M h) =
                  (M : Int) * (2 * (Delta (M - 1) h 1 - (2 : Int) ^ (popcount h - 1) * boolToInt (betaCF M h))) +
                  (2 : Int) ^ popcount h * ((M : Int) * boolToInt (betaCF M h) - boolToInt (M.testBit 0 && betaCF M h)) := by
                rw [Int.mul_sub, Int.mul_sub, Int.mul_sub]
                have he1 : (M : Int) * (2 * ((2 : Int) ^ (popcount h - 1) * boolToInt (betaCF M h))) =
                    (2 : Int) ^ popcount h * ((M : Int) * boolToInt (betaCF M h)) := by
                  rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm (M : Int) 2, Int.mul_assoc 2,
                    Int.mul_comm (M : Int) ((2 : Int) ^ (popcount h - 1)), ← Int.mul_assoc 2, hpow,
                    Int.mul_assoc]
                have he2 : (M : Int) * (2 * Delta (M - 1) h 1) = 2 * (M : Int) * Delta (M - 1) h 1 := by
                  rw [← Int.mul_assoc, Int.mul_comm (M : Int) 2]
                rw [he1, he2]; omega
              rw [hcomb]
              exact dvd_add_of_dvd hstep1 (by simpa [Nat.add_comm] using hstep2)
            have hreord : 2 * (M : Int) * Delta (M - 1) h 1 +
                sumRange (M - 1) (fun i =>
                  if (i + 2) % 2 = 1 then
                    (2 : Int) ^ (i + 2) * binomZ M ((i + 2 : Nat) : Int) * Delta (M - (i + 2)) h (0 + (((i + 2) / 2 : Nat) : Int) + 1)
                  else 0) -
                (2 : Int) ^ popcount h * boolToInt (M.testBit 0 && betaCF M h) =
                (2 * (M : Int) * Delta (M - 1) h 1 - (2 : Int) ^ popcount h * boolToInt (M.testBit 0 && betaCF M h)) +
                sumRange (M - 1) (fun i =>
                  if (i + 2) % 2 = 1 then
                    (2 : Int) ^ (i + 2) * binomZ M ((i + 2 : Nat) : Int) * Delta (M - (i + 2)) h (0 + (((i + 2) / 2 : Nat) : Int) + 1)
                  else 0) := by omega
            rw [hreord]
            exact dvd_add_of_dvd hmain htail
        have hAlphaOddEven : ∀ h : Nat, Submask h M →
            (2 : Int) ^ (popcount h + 1) ∣
              (Delta (2 * M + 1) (2 * h) 0 - (2 : Int) ^ popcount h * boolToInt (alphaCF (2 * M + 1) (2 * h))) := by
          intro h hhM
          rw [delta_odd_even, alphaCF_odd_even]
          have hx := dvd_two_pow_mul_left (popcount h) 1 (dvd_two_bool_xor (alphaCF M h) (M.testBit 0 && betaCF M h))
          have hsum := dvd_add_of_dvd (hD2M0 h hhM) (hD2M1 h hhM)
          have h01 : (0 : Int) + 1 = 1 := rfl
          have hcomb : Delta (2 * M) (2 * h) 0 + Delta (2 * M) (2 * h) (0 + 1) -
              (2 : Int) ^ popcount h * boolToInt (xor (alphaCF M h) (M.testBit 0 && betaCF M h)) =
              ((Delta (2 * M) (2 * h) 0 - (2 : Int) ^ popcount h * boolToInt (alphaCF M h)) +
               (Delta (2 * M) (2 * h) 1 - (2 : Int) ^ popcount h * boolToInt (M.testBit 0 && betaCF M h))) +
              (2 : Int) ^ popcount h * (boolToInt (alphaCF M h) + boolToInt (M.testBit 0 && betaCF M h) -
                boolToInt (xor (alphaCF M h) (M.testBit 0 && betaCF M h))) := by
            rw [h01, Int.mul_sub, Int.mul_add]; omega
          rw [hcomb]
          exact dvd_add_of_dvd hsum (by simpa [Nat.add_comm] using hx)
        rw [hNM]
        constructor
        · intro j hj
          have hjM : Submask (j / 2) M := (submask_two_mul_add_one_iff j M).mp hj
          let h := j / 2
          by_cases hjpar : j % 2 = 0
          · have hjh : j = 2 * h := by omega
            rw [hjh, popcount_two_mul]
            exact hAlphaOddEven h hjM
          · have hjh : j = 2 * h + 1 := by omega
            rw [hjh, popcount_two_mul_add_one, alphaCF_odd_odd]
            have h0 : (0 : Int) = 2 * (0 : Int) := rfl
            rw [h0, delta_odd_odd_even]
            by_cases hM0 : M = 0
            · have hh0 : h = 0 := by have := submask_le hjM; omega
              rw [hh0, hM0]
              simp [sumRange, popcount_zero, boolToInt]
            · have hMsp : M + 1 = (M - 1 + 1) + 1 := by omega
              rw [hMsp, sumRange_split_first, sumRange_split_first]
              have ht0 : (if (0 : Nat) % 2 = 1 then (2 : Int) ^ 0 * binomZ M ((0 : Nat) : Int) *
                  (Delta (M - 0 + 1) h (0 + ((0 / 2 : Nat) : Int)) - 2 * Delta (M - 0) h (0 + ((0 / 2 : Nat) : Int) + 1)) else 0) = 0 := by simp
              have ht1 : (if (0 + 1 : Nat) % 2 = 1 then (2 : Int) ^ (0 + 1) * binomZ M ((0 + 1 : Nat) : Int) *
                  (Delta (M - (0 + 1) + 1) h (0 + (((0 + 1) / 2 : Nat) : Int)) - 2 * Delta (M - (0 + 1)) h (0 + (((0 + 1) / 2 : Nat) : Int) + 1)) else 0) =
                  2 * (M : Int) * (Delta M h 0 - 2 * Delta (M - 1) h 1) := by
                have hM1 : M - 1 + 1 = M := by omega
                simp [binomZ_one_right, hM1]
              rw [ht0, ht1, Int.zero_add]
              have htail : (2 : Int) ^ (popcount h + 1 + 1) ∣
                  sumRange (M - 1) (fun i =>
                    if (i + 2) % 2 = 1 then
                      (2 : Int) ^ (i + 2) * binomZ M ((i + 2 : Nat) : Int) *
                        (Delta (M - (i + 2) + 1) h (0 + (((i + 2) / 2 : Nat) : Int)) -
                         2 * Delta (M - (i + 2)) h (0 + (((i + 2) / 2 : Nat) : Int) + 1))
                    else 0) := by
                apply sumRange_dvd
                intro i hi
                by_cases hip : (i + 2) % 2 = 1
                · simp only [hip, ↓reduceIte]
                  let u := (i + 2) / 2
                  have hle0 : 2 * u ≤ M := by omega
                  have hle1 : 2 * (u + 1) ≤ M + 1 := by omega
                  have hn0 : M - (i + 2) + 1 = M - 2 * u := by omega
                  have hn1 : M - (i + 2) = M + 1 - 2 * (u + 1) := by omega
                  have hc0 : (0 : Int) + (u : Int) = (u : Int) := by omega
                  have hc1 : (0 : Int) + (u : Int) + 1 = ((u + 1 : Nat) : Int) := by omega
                  rw [hn0, hn1, hc1, hc0]
                  have hd0 := div0 h u hjM hle0
                  have hd1 := dvd_two_mul_of_dvd (div1 h (u + 1) hjM (by omega) hle1)
                  have hdiff : (2 : Int) ^ (popcount h - u) ∣
                      (Delta (M - 2 * u) h (u : Int) - 2 * Delta (M + 1 - 2 * (u + 1)) h ((u + 1 : Nat) : Int)) :=
                    dvd_sub_of_dvd hd0 (dvd_two_pow_mono (by omega) hd1)
                  have hmul : (2 : Int) ^ ((i + 2) + (popcount h - u)) ∣
                      (2 : Int) ^ (i + 2) * binomZ M ((i + 2 : Nat) : Int) *
                        (Delta (M - 2 * u) h (u : Int) - 2 * Delta (M + 1 - 2 * (u + 1)) h ((u + 1 : Nat) : Int)) := by
                    rw [Int.mul_assoc, Int.mul_comm (binomZ M ((i + 2 : Nat) : Int)), ← Int.mul_assoc]
                    exact dvd_mul_right_of_dvd _ (dvd_two_pow_mul_left (i + 2) _ hdiff)
                  exact dvd_two_pow_mono (by omega) hmul
                · simp only [hip, ↓reduceIte]; exact ⟨0, by simp⟩
              have hinner : (2 : Int) ^ (popcount h + 1) ∣
                  ((Delta M h 0 - 2 * Delta (M - 1) h 1) -
                    (2 : Int) ^ popcount h * boolToInt (xor (alphaCF M h) (betaCF M h))) := by
                by_cases hh0 : h = 0
                · rw [hh0, delta_zero_shift_one, Int.mul_zero, Int.sub_zero]
                  have hb0 : betaCF M 0 = false := by unfold betaCF; simp [hM0]
                  rw [hb0, Bool.xor_false]
                  exact ihA 0 (by rw [← hh0]; exact hjM)
                · have hpc_pos : 1 ≤ popcount h := popcount_pos_of_ne_zero hh0
                  have hB2 := dvd_two_mul_of_dvd (ihB h hjM hh0)
                  have hpow : (2 : Int) * (2 : Int) ^ (popcount h - 1) = (2 : Int) ^ popcount h := by
                    have h1 : popcount h = (popcount h - 1) + 1 := by omega
                    conv => rhs; rw [h1, Int.pow_succ]
                    rw [Int.mul_comm]
                  have hB2' : (2 : Int) ^ (popcount h + 1) ∣
                      (2 * Delta (M - 1) h 1 - (2 : Int) ^ popcount h * boolToInt (betaCF M h)) := by
                    have heq : 2 * (Delta (M - 1) h 1 - (2 : Int) ^ (popcount h - 1) * boolToInt (betaCF M h)) =
                        2 * Delta (M - 1) h 1 - (2 : Int) ^ popcount h * boolToInt (betaCF M h) := by
                      rw [Int.mul_sub, ← Int.mul_assoc, hpow]
                    rw [← heq]; exact hB2
                  have hsubAB := dvd_sub_of_dvd (ihA h hjM) hB2'
                  have hx := dvd_two_pow_mul_left (popcount h) 1 (dvd_two_bool_xor_sub (alphaCF M h) (betaCF M h))
                  have hcomb : (Delta M h 0 - 2 * Delta (M - 1) h 1) -
                      (2 : Int) ^ popcount h * boolToInt (xor (alphaCF M h) (betaCF M h)) =
                      ((Delta M h 0 - (2 : Int) ^ popcount h * boolToInt (alphaCF M h)) -
                       (2 * Delta (M - 1) h 1 - (2 : Int) ^ popcount h * boolToInt (betaCF M h))) +
                      (2 : Int) ^ popcount h * (boolToInt (alphaCF M h) - boolToInt (betaCF M h) -
                        boolToInt (xor (alphaCF M h) (betaCF M h))) := by
                    rw [Int.mul_sub, Int.mul_sub]; omega
                  rw [hcomb]
                  exact dvd_add_of_dvd hsubAB (by simpa [Nat.add_comm] using hx)
              have hmain : (2 : Int) ^ (popcount h + 1 + 1) ∣
                  (2 * (M : Int) * (Delta M h 0 - 2 * Delta (M - 1) h 1) -
                    (2 : Int) ^ (popcount h + 1) * boolToInt (M.testBit 0 && xor (alphaCF M h) (betaCF M h))) := by
                have hstep1 := dvd_mul_left_of_dvd (M : Int) (dvd_two_mul_of_dvd hinner)
                have hstep2 := dvd_two_pow_mul_left (popcount h + 1) 1 (dvd_two_mul_bool M (xor (alphaCF M h) (betaCF M h)))
                have hpow : (2 : Int) * (2 : Int) ^ popcount h = (2 : Int) ^ (popcount h + 1) := by
                  rw [Int.pow_succ, Int.mul_comm]
                have hcomb : 2 * (M : Int) * (Delta M h 0 - 2 * Delta (M - 1) h 1) -
                    (2 : Int) ^ (popcount h + 1) * boolToInt (M.testBit 0 && xor (alphaCF M h) (betaCF M h)) =
                    (M : Int) * (2 * ((Delta M h 0 - 2 * Delta (M - 1) h 1) -
                      (2 : Int) ^ popcount h * boolToInt (xor (alphaCF M h) (betaCF M h)))) +
                    (2 : Int) ^ (popcount h + 1) * ((M : Int) * boolToInt (xor (alphaCF M h) (betaCF M h)) -
                      boolToInt (M.testBit 0 && xor (alphaCF M h) (betaCF M h))) := by
                  have he1 : (M : Int) * (2 * ((2 : Int) ^ popcount h * boolToInt (xor (alphaCF M h) (betaCF M h)))) =
                      (2 : Int) ^ (popcount h + 1) * ((M : Int) * boolToInt (xor (alphaCF M h) (betaCF M h))) := by
                    rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm (M : Int) 2, Int.mul_assoc 2,
                      Int.mul_comm (M : Int) ((2 : Int) ^ popcount h), ← Int.mul_assoc 2, hpow,
                      Int.mul_assoc]
                  have he2 : (M : Int) * (2 * (Delta M h 0 - 2 * Delta (M - 1) h 1)) =
                      2 * (M : Int) * (Delta M h 0 - 2 * Delta (M - 1) h 1) := by
                    rw [← Int.mul_assoc, Int.mul_comm (M : Int) 2]
                  rw [Int.mul_sub (2 : Int), Int.mul_sub (M : Int),
                    Int.mul_sub ((2 : Int) ^ (popcount h + 1)), he1, he2]; omega
                rw [hcomb]
                exact dvd_add_of_dvd hstep1 (by simpa [Nat.add_comm] using hstep2)
              have hreord : 2 * (M : Int) * (Delta M h 0 - 2 * Delta (M - 1) h 1) +
                  sumRange (M - 1) (fun i =>
                    if (i + 2) % 2 = 1 then
                      (2 : Int) ^ (i + 2) * binomZ M ((i + 2 : Nat) : Int) *
                        (Delta (M - (i + 2) + 1) h (0 + (((i + 2) / 2 : Nat) : Int)) -
                         2 * Delta (M - (i + 2)) h (0 + (((i + 2) / 2 : Nat) : Int) + 1))
                    else 0) -
                  (2 : Int) ^ (popcount h + 1) * boolToInt (M.testBit 0 && xor (alphaCF M h) (betaCF M h)) =
                  (2 * (M : Int) * (Delta M h 0 - 2 * Delta (M - 1) h 1) -
                    (2 : Int) ^ (popcount h + 1) * boolToInt (M.testBit 0 && xor (alphaCF M h) (betaCF M h))) +
                  sumRange (M - 1) (fun i =>
                    if (i + 2) % 2 = 1 then
                      (2 : Int) ^ (i + 2) * binomZ M ((i + 2 : Nat) : Int) *
                        (Delta (M - (i + 2) + 1) h (0 + (((i + 2) / 2 : Nat) : Int)) -
                         2 * Delta (M - (i + 2)) h (0 + (((i + 2) / 2 : Nat) : Int) + 1))
                    else 0) := by omega
              rw [hreord]
              exact dvd_add_of_dvd hmain htail
        · intro j hj hjne
          have hjM : Submask (j / 2) M := (submask_two_mul_add_one_iff j M).mp hj
          let h := j / 2
          have hsub : 2 * M + 1 - 1 = 2 * M := by omega
          rw [hsub]
          by_cases hjpar : j % 2 = 0
          · have hjh : j = 2 * h := by omega
            rw [hjh, popcount_two_mul, betaCF_odd_even]
            simp only [boolToInt, Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.sub_zero]
            have h1 := hD2M1 h hjM
            have h1' := dvd_two_pow_mono (a := popcount h) (b := popcount h + 1) (by omega) h1
            have h2 : (2 : Int) ^ popcount h ∣ (2 : Int) ^ popcount h * boolToInt (M.testBit 0 && betaCF M h) :=
              ⟨_, rfl⟩
            have hsum := dvd_add_of_dvd h1' h2
            simpa [Int.sub_add_cancel] using hsum
          · have hjh : j = 2 * h + 1 := by omega
            rw [hjh, popcount_two_mul_add_one, betaCF_odd_odd, alphaCF_odd_even, delta_even_odd]
            have hsub0 : (popcount h + 1) - 1 = popcount h := by omega
            have hsub1 : (1 : Int) - 1 = 0 := rfl
            rw [hsub0, hsub1]
            have hdiff := dvd_sub_of_dvd (hD2M0 h hjM) (hD2M1 h hjM)
            have hx := dvd_two_pow_mul_left (popcount h) 1 (dvd_two_bool_xor_sub (alphaCF M h) (M.testBit 0 && betaCF M h))
            have hcomb : (Delta (2 * M) (2 * h) 0 - Delta (2 * M) (2 * h) 1) -
                (2 : Int) ^ popcount h * boolToInt (xor (alphaCF M h) (M.testBit 0 && betaCF M h)) =
                ((Delta (2 * M) (2 * h) 0 - (2 : Int) ^ popcount h * boolToInt (alphaCF M h)) -
                 (Delta (2 * M) (2 * h) 1 - (2 : Int) ^ popcount h * boolToInt (M.testBit 0 && betaCF M h))) +
                (2 : Int) ^ popcount h * (boolToInt (alphaCF M h) - boolToInt (M.testBit 0 && betaCF M h) -
                  boolToInt (xor (alphaCF M h) (M.testBit 0 && betaCF M h))) := by
              rw [Int.mul_sub, Int.mul_sub]; omega
            rw [hcomb]
            exact dvd_add_of_dvd hdiff (by simpa [Nat.add_comm] using hx)

/-! ## Section 4: Stage 2 — The Reusable 2-Adic Bit-Smoothness Algebra Engine -/

theorem bitUnit_to_bitExcess0 {n s : Nat} {f : Nat → Int}
    (h : BitUnit n s f) : BitExcess n 0 f := by
  intro j hj
  by_cases hj0 : j = 0
  · subst hj0; rw [popcount_zero]; exact dvd_two_pow_zero _
  · exact dvd_two_pow_mono (by omega) (h.2 j hj hj0)

theorem bitUnit_to_bitSmooth_zero {n s : Nat} {f : Nat → Int} (hs : 1 ≤ s)
    (h : BitUnit n s f) : BitSmooth n 0 f := by
  refine ⟨submask_zero n, fun j hj => ?_⟩
  by_cases hj0 : j = 0
  · subst hj0
    rw [mobius_zero, h.1, popcount_zero]
    decide
  · have hnd : ((j &&& 0) == j) = false := by
      simp only [Nat.and_zero, beq_eq_false_iff_ne]
      exact Ne.symm hj0
    rw [hnd]
    simp only [boolToInt, Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.sub_zero]
    exact dvd_two_pow_mono (by omega) (h.2 j hj hj0)

theorem bitSmooth_restrict {n n' E : Nat} {f : Nat → Int}
    (hnn' : Submask n n') (hf : BitSmooth n' E f) :
    BitSmooth n (E &&& n) f := by
  refine ⟨submask_and_right E n, fun j hj => ?_⟩
  have heq : ((j &&& (E &&& n)) == j) = ((j &&& E) == j) := by
    have h1 : j &&& (E &&& n) = j &&& E := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_and]
      cases hjbit : j.testBit i
      · simp
      · have hnbit := (submask_iff_testBit.mp hj) i hjbit
        simp [hnbit]
    rw [h1]
  rw [heq]
  exact hf.2 j (submask_trans hj hnn')

/-- **Stage 2 Law 3 (Higher Squaring Lift):**
    For all `s >= 1`, `BitUnit n s g -> BitUnit n (s + 1) (g^2)`. -/
theorem bitUnit_sq_lift {n s : Nat} {g : Nat → Int} (hs : 1 ≤ s)
    (hg : BitUnit n s g) :
    BitUnit n (s + 1) (fun k => g k * g k) := by
  refine ⟨by simp [hg.1], ?_⟩
  induction n using nat_strong_ind generalizing g with
  | step n ih =>
    intro j hj hjne
    by_cases hn : n = 0
    · subst hn; exact absurd (Nat.eq_zero_of_le_zero (submask_le hj)) hjne
    · by_cases hnp : n % 2 = 0
      · let m := n / 2
        have hnm : n = 2 * m := by omega
        rw [hnm] at hj hg
        obtain ⟨hj0, hjm⟩ := (submask_two_mul_iff j m).mp hj
        let h := j / 2
        have hjh : j = 2 * h := by omega
        have hne : h ≠ 0 := by omega
        rw [hjh, popcount_two_mul, mobius_two_mul]
        have hg0 : BitUnit m s (fun k => g (2 * k)) := by
          refine ⟨by simpa using hg.1, fun a ha hane => ?_⟩
          have h1 := hg.2 (2 * a) ((submask_two_mul_left_two_mul_right a m).mpr ha) (by omega)
          rwa [popcount_two_mul, mobius_two_mul] at h1
        exact ih m (by omega) hg0 h hjm hne
      · let m := n / 2
        have hnm : n = 2 * m + 1 := by omega
        rw [hnm] at hj hg
        have hjm : Submask (j / 2) m := (submask_two_mul_add_one_iff j m).mp hj
        let h := j / 2
        have hg0 : BitUnit m s (fun k => g (2 * k)) := by
          refine ⟨by simpa using hg.1, fun a ha hane => ?_⟩
          have h1 := hg.2 (2 * a) ((submask_two_mul_left_odd_right a m).mpr ha) (by omega)
          rwa [popcount_two_mul, mobius_two_mul] at h1
        by_cases hjp : j % 2 = 0
        · have hjh : j = 2 * h := by omega
          have hne : h ≠ 0 := by omega
          rw [hjh, popcount_two_mul, mobius_two_mul]
          exact ih m (by omega) hg0 h hjm hne
        · have hjh : j = 2 * h + 1 := by omega
          rw [hjh, popcount_two_mul_add_one, mobius_two_mul_add_one]
          have hfact : (fun k => g (2 * k + 1) * g (2 * k + 1) - g (2 * k) * g (2 * k)) =
              (fun k => (g (2 * k + 1) - g (2 * k)) * (2 * g (2 * k) + (g (2 * k + 1) - g (2 * k)))) := by
            funext k
            rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_sub, Int.mul_sub]
            have hc1 : g (2 * k + 1) * (2 * g (2 * k)) = 2 * (g (2 * k) * g (2 * k + 1)) := by
              rw [Int.mul_comm (g (2 * k + 1)), ← Int.mul_assoc, Int.mul_assoc 2]
            have hc2 : g (2 * k) * (2 * g (2 * k)) = 2 * (g (2 * k) * g (2 * k)) := by
              rw [Int.mul_comm (g (2 * k)), Int.mul_assoc]
            have hc3 : g (2 * k + 1) * g (2 * k) = g (2 * k) * g (2 * k + 1) := Int.mul_comm _ _
            omega
          rw [hfact]
          have hdg : BitExcess m (s + 1) (fun k => g (2 * k + 1) - g (2 * k)) := by
            intro a ha
            have h1 := hg.2 (2 * a + 1) ((submask_odd_left_odd_right a m).mpr ha) (by omega)
            rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at h1
            exact dvd_two_pow_mono (by omega) h1
          have h2g0 := bitExcess_scale_two (bitUnit_to_bitExcess0 hg0)
          have hsum := bitExcess_add h2g0 (bitExcess_mono (by omega) hdg)
          have hprod := bitExcess_mul hdg hsum h hjm
          exact dvd_two_pow_mono (by omega) hprod

/-- **Stage 2 Law 4 (Monoid Closure of `BitUnit n s`):**
    For all `s >= 1`, `BitUnit n s g` and `BitUnit n s h` imply `BitUnit n s (g * h)`. -/
theorem bitUnit_mul {n s : Nat} {g₁ g₂ : Nat → Int}
    (hg1 : BitUnit n s g₁) (hg2 : BitUnit n s g₂) :
    BitUnit n s (fun k => g₁ k * g₂ k) := by
  refine ⟨by simp [hg1.1, hg2.1], ?_⟩
  induction n using nat_strong_ind generalizing g₁ g₂ with
  | step n ih =>
    intro j hj hjne
    by_cases hn : n = 0
    · subst hn; exact absurd (Nat.eq_zero_of_le_zero (submask_le hj)) hjne
    · by_cases hnp : n % 2 = 0
      · let m := n / 2
        have hnm : n = 2 * m := by omega
        rw [hnm] at hj hg1 hg2
        obtain ⟨hj0, hjm⟩ := (submask_two_mul_iff j m).mp hj
        let h := j / 2
        have hjh : j = 2 * h := by omega
        have hne : h ≠ 0 := by omega
        rw [hjh, popcount_two_mul, mobius_two_mul]
        have h1 : BitUnit m s (fun k => g₁ (2 * k)) := by
          refine ⟨by simpa using hg1.1, fun a ha hane => ?_⟩
          have := hg1.2 (2 * a) ((submask_two_mul_left_two_mul_right a m).mpr ha) (by omega)
          rwa [popcount_two_mul, mobius_two_mul] at this
        have h2 : BitUnit m s (fun k => g₂ (2 * k)) := by
          refine ⟨by simpa using hg2.1, fun a ha hane => ?_⟩
          have := hg2.2 (2 * a) ((submask_two_mul_left_two_mul_right a m).mpr ha) (by omega)
          rwa [popcount_two_mul, mobius_two_mul] at this
        exact ih m (by omega) h1 h2 h hjm hne
      · let m := n / 2
        have hnm : n = 2 * m + 1 := by omega
        rw [hnm] at hj hg1 hg2
        have hjm : Submask (j / 2) m := (submask_two_mul_add_one_iff j m).mp hj
        let h := j / 2
        have h1 : BitUnit m s (fun k => g₁ (2 * k)) := by
          refine ⟨by simpa using hg1.1, fun a ha hane => ?_⟩
          have := hg1.2 (2 * a) ((submask_two_mul_left_odd_right a m).mpr ha) (by omega)
          rwa [popcount_two_mul, mobius_two_mul] at this
        have h2 : BitUnit m s (fun k => g₂ (2 * k)) := by
          refine ⟨by simpa using hg2.1, fun a ha hane => ?_⟩
          have := hg2.2 (2 * a) ((submask_two_mul_left_odd_right a m).mpr ha) (by omega)
          rwa [popcount_two_mul, mobius_two_mul] at this
        by_cases hjp : j % 2 = 0
        · have hjh : j = 2 * h := by omega
          have hne : h ≠ 0 := by omega
          rw [hjh, popcount_two_mul, mobius_two_mul]
          exact ih m (by omega) h1 h2 h hjm hne
        · have hjh : j = 2 * h + 1 := by omega
          rw [hjh, popcount_two_mul_add_one, mobius_two_mul_add_one]
          have hdecomp : (fun k => g₁ (2 * k + 1) * g₂ (2 * k + 1) - g₁ (2 * k) * g₂ (2 * k)) =
              (fun k => g₁ (2 * k) * (g₂ (2 * k + 1) - g₂ (2 * k)) +
                        (g₁ (2 * k + 1) - g₁ (2 * k)) * g₂ (2 * k) +
                        (g₁ (2 * k + 1) - g₁ (2 * k)) * (g₂ (2 * k + 1) - g₂ (2 * k))) := by
            funext k
            rw [Int.mul_sub, Int.sub_mul, Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
          rw [hdecomp, mobius_add, mobius_add]
          have hd1 : BitExcess m (s + 1) (fun k => g₁ (2 * k + 1) - g₁ (2 * k)) := by
            intro a ha
            have := hg1.2 (2 * a + 1) ((submask_odd_left_odd_right a m).mpr ha) (by omega)
            rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at this
            exact dvd_two_pow_mono (by omega) this
          have hd2 : BitExcess m (s + 1) (fun k => g₂ (2 * k + 1) - g₂ (2 * k)) := by
            intro a ha
            have := hg2.2 (2 * a + 1) ((submask_odd_left_odd_right a m).mpr ha) (by omega)
            rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at this
            exact dvd_two_pow_mono (by omega) this
          have hp1 := bitExcess_mul (bitUnit_to_bitExcess0 h1) hd2 h hjm
          have hp2 := bitExcess_mul hd1 (bitUnit_to_bitExcess0 h2) h hjm
          have hp3 := bitExcess_mul hd1 hd2 h hjm
          exact dvd_add_of_dvd
            (dvd_add_of_dvd (dvd_two_pow_mono (by omega) hp1) (dvd_two_pow_mono (by omega) hp2))
            (dvd_two_pow_mono (by omega) hp3)

theorem submask_xor {a b n : Nat} (ha : Submask a n) (hb : Submask b n) :
    Submask (a ^^^ b) n := by
  rw [submask_iff_testBit] at *
  intro i hi
  rw [Nat.testBit_xor] at hi
  cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all

/-- **Stage 2 Law 5 (XOR-Spike Homomorphism):**
    Pointwise product of two Rank-0 Bit-Smooth functions XORs their spike masks:
    `BitSmooth n E1 f` and `BitSmooth n E2 g` imply `BitSmooth n (E1 ^^^ E2) (f * g)`. -/
theorem bitSmooth_xor_mul {n E1 E2 : Nat} {f g : Nat → Int}
    (hf : BitSmooth n E1 f) (hg : BitSmooth n E2 g) :
    BitSmooth n (E1 ^^^ E2) (fun k => f k * g k) := by
  refine ⟨submask_xor hf.1 hg.1, ?_⟩
  induction n using nat_strong_ind generalizing E1 E2 f g with
  | step n ih =>
    intro j hj
    by_cases hn : n = 0
    · subst hn
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero (submask_le hj)
      subst hj0
      rw [mobius_zero, popcount_zero]
      have hf0 := hf.2 0 (submask_zero 0); rw [mobius_zero, popcount_zero] at hf0
      have hg0 := hg.2 0 (submask_zero 0); rw [mobius_zero, popcount_zero] at hg0
      simp only [Nat.zero_and, beq_self_eq_true, boolToInt, ↓reduceIte, Int.pow_zero, Int.mul_one,
        Nat.zero_add, Int.pow_one] at hf0 hg0 ⊢
      obtain ⟨qf, hqf⟩ := hf0
      obtain ⟨qg, hqg⟩ := hg0
      refine ⟨qf + qg + 2 * qf * qg, ?_⟩
      have hf' : f 0 = 1 + 2 * qf := by omega
      have hg' : g 0 = 1 + 2 * qg := by omega
      rw [hf', hg', Int.add_mul, Int.mul_add, Int.mul_add]
      have h1 : 2 * qf * (2 * qg) = 2 * (2 * qf * qg) := by
        rw [Int.mul_assoc 2 qf, Int.mul_comm qf (2 * qg), Int.mul_assoc 2 qg qf,
          Int.mul_comm qg qf, ← Int.mul_assoc 2 qf qg]
      omega
    · by_cases hnp : n % 2 = 0
      · let m := n / 2
        have hnm : n = 2 * m := by omega
        rw [hnm] at hj hf hg
        obtain ⟨hj0, hjm⟩ := (submask_two_mul_iff j m).mp hj
        obtain ⟨hE10, hE1m⟩ := (submask_two_mul_iff E1 m).mp hf.1
        obtain ⟨hE20, hE2m⟩ := (submask_two_mul_iff E2 m).mp hg.1
        let h := j / 2
        have hjh : j = 2 * h := by omega
        rw [hjh, popcount_two_mul, mobius_two_mul]
        have hf0 : BitSmooth m (E1 / 2) (fun k => f (2 * k)) := by
          refine ⟨hE1m, fun a ha => ?_⟩
          have h1 := hf.2 (2 * a) ((submask_two_mul_left_two_mul_right a m).mpr ha)
          rw [popcount_two_mul, mobius_two_mul] at h1
          have hE : E1 = 2 * (E1 / 2) := by omega
          have hm : ((2 * a &&& E1) == 2 * a) = ((a &&& (E1 / 2)) == a) := by
            conv => lhs; rw [hE, and_two_mul_two_mul]
            exact beq_two_mul_eq (a &&& (E1 / 2)) a
          rwa [hm] at h1
        have hg0 : BitSmooth m (E2 / 2) (fun k => g (2 * k)) := by
          refine ⟨hE2m, fun a ha => ?_⟩
          have h1 := hg.2 (2 * a) ((submask_two_mul_left_two_mul_right a m).mpr ha)
          rw [popcount_two_mul, mobius_two_mul] at h1
          have hE : E2 = 2 * (E2 / 2) := by omega
          have hm : ((2 * a &&& E2) == 2 * a) = ((a &&& (E2 / 2)) == a) := by
            conv => lhs; rw [hE, and_two_mul_two_mul]
            exact beq_two_mul_eq (a &&& (E2 / 2)) a
          rwa [hm] at h1
        have hxor : E1 ^^^ E2 = 2 * ((E1 / 2) ^^^ (E2 / 2)) := by
          have h1 : E1 = 2 * (E1 / 2) := by omega
          have h2 : E2 = 2 * (E2 / 2) := by omega
          conv => lhs; rw [h1, h2]
          exact xor_two_mul_two_mul (E1 / 2) (E2 / 2)
        have hmask : ((2 * h &&& (E1 ^^^ E2)) == 2 * h) = ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h) := by
          rw [hxor, and_two_mul_two_mul]; exact beq_two_mul_eq (h &&& ((E1 / 2) ^^^ (E2 / 2))) h
        rw [hmask]
        exact ih m (by omega) hf0 hg0 h hjm
      · let m := n / 2
        have hnm : n = 2 * m + 1 := by omega
        rw [hnm] at hj hf hg
        have hjm : Submask (j / 2) m := (submask_two_mul_add_one_iff j m).mp hj
        let h := j / 2
        have hf0 := bitSmooth_slice_even hf
        have hg0 := bitSmooth_slice_even hg
        have hxor_div : (E1 ^^^ E2) / 2 = (E1 / 2) ^^^ (E2 / 2) := by
          apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.testBit_xor]
          have hd : ∀ x, (x / 2).testBit i = x.testBit (i + 1) := fun x => (Nat.testBit_succ x i).symm
          rw [hd, hd, hd, Nat.testBit_xor]
        by_cases hjp : j % 2 = 0
        · have hjh : j = 2 * h := by omega
          rw [hjh, popcount_two_mul, mobius_two_mul]
          have hmask : ((2 * h &&& (E1 ^^^ E2)) == 2 * h) = ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h) := by
            apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
            change Submask (2 * h) (E1 ^^^ E2) ↔ Submask h ((E1 / 2) ^^^ (E2 / 2))
            rw [← hxor_div]
            by_cases hp : (E1 ^^^ E2) % 2 = 0
            · have h2 : E1 ^^^ E2 = 2 * ((E1 ^^^ E2) / 2) := by omega
              conv => lhs; rw [h2]
              exact submask_two_mul_left_two_mul_right h _
            · have h2 : E1 ^^^ E2 = 2 * ((E1 ^^^ E2) / 2) + 1 := by omega
              conv => lhs; rw [h2]
              exact submask_two_mul_left_odd_right h _
          rw [hmask]
          exact ih m (by omega) hf0 hg0 h hjm
        · have hjh : j = 2 * h + 1 := by omega
          rw [hjh, popcount_two_mul_add_one, mobius_two_mul_add_one]
          have hdecomp : (fun k => f (2 * k + 1) * g (2 * k + 1) - f (2 * k) * g (2 * k)) =
              (fun k => f (2 * k) * (g (2 * k + 1) - g (2 * k)) +
                        (f (2 * k + 1) - f (2 * k)) * g (2 * k) +
                        (f (2 * k + 1) - f (2 * k)) * (g (2 * k + 1) - g (2 * k))) := by
            funext k
            rw [Int.mul_sub, Int.sub_mul, Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
          rw [hdecomp, mobius_add, mobius_add]
          have hdf1 : BitExcess m 1 (fun k => f (2 * k + 1) - f (2 * k)) := by
            intro a ha
            have := bitSmooth_to_bitExcess0 hf (2 * a + 1) ((submask_odd_left_odd_right a m).mpr ha)
            rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at this
            exact dvd_two_pow_mono (by omega) this
          have hdg1 : BitExcess m 1 (fun k => g (2 * k + 1) - g (2 * k)) := by
            intro a ha
            have := bitSmooth_to_bitExcess0 hg (2 * a + 1) ((submask_odd_left_odd_right a m).mpr ha)
            rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at this
            exact dvd_two_pow_mono (by omega) this
          have hterm3 : (2 : Int) ^ (popcount h + 1 + 1) ∣
              mobius (fun k => (f (2 * k + 1) - f (2 * k)) * (g (2 * k + 1) - g (2 * k))) h :=
            dvd_two_pow_mono (by omega) (bitExcess_mul hdf1 hdg1 h hjm)
          have hscale_mul : ∀ {E_a E_b : Nat} {a b : Nat → Int},
              BitSmooth m E_a a →
              (Submask E_b m ∧ ∀ t, Submask t m →
                (2 : Int) ^ (popcount t + 2) ∣
                  (mobius b t - (2 : Int) ^ (popcount t + 1) * boolToInt ((t &&& E_b) == t))) →
              (2 : Int) ^ (popcount h + 1 + 1) ∣
                (mobius (fun k => a k * b k) h -
                  (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& (E_a ^^^ E_b)) == h)) := by
            intro E_a E_b a b ha hb
            have hb_even : ∀ k, Submask k m → 2 ∣ b k := by
              intro k hk
              rw [← sumSubmasks_mobius b k]
              rw [sumSubmasks_eq_sumLucasFiltered]
              unfold sumLucasFiltered
              apply sumRange_dvd
              intro t _
              by_cases htk : t &&& k = t
              · simp only [htk, ↓reduceIte]
                have htm := submask_trans htk hk
                have hd1 := dvd_two_pow_mono (a := 1) (b := popcount t + 2) (by omega) (hb.2 t htm)
                have hd2 : (2 : Int) ∣ (2 : Int) ^ (popcount t + 1) * boolToInt ((t &&& E_b) == t) :=
                  dvd_mul_right_of_dvd _ (dvd_two_pow_mono (a := 1) (b := popcount t + 1) (by omega) ⟨1, by simp⟩)
                have hsum := dvd_add_of_dvd hd1 hd2
                simpa [Int.sub_add_cancel] using hsum
              · simp [htk]
            let bHalf : Nat → Int := fun k => b k / 2
            have hb_eq : ∀ k, Submask k m → b k = 2 * bHalf k := by
              intro k hk
              obtain ⟨q, hq⟩ := hb_even k hk
              dsimp [bHalf]; omega
            have hbHalf_smooth : BitSmooth m E_b bHalf := by
              refine ⟨hb.1, fun t ht => ?_⟩
              have hmob : mobius b t = 2 * mobius bHalf t := by
                rw [← mobius_mul_left]
                exact mobius_congr (fun k hk => hb_eq k (submask_trans hk ht))
              have hdiv := hb.2 t ht
              rw [hmob] at hdiv
              obtain ⟨q, hq⟩ := hdiv
              refine ⟨q, ?_⟩
              have hp1 : (2 : Int) ^ (popcount t + 1) = 2 * (2 : Int) ^ popcount t := by
                rw [Int.pow_succ, Int.mul_comm]
              have hp2 : (2 : Int) ^ (popcount t + 2) = 2 * (2 : Int) ^ (popcount t + 1) := by
                rw [Int.pow_succ, Int.mul_comm]
              rw [hp1, hp2, Int.mul_assoc 2, Int.mul_assoc 2] at hq
              omega
            have hih := ih m (by omega) ha hbHalf_smooth h hjm
            have h2 := dvd_two_mul_of_dvd hih
            have hmob_ab : mobius (fun k => a k * b k) h = 2 * mobius (fun k => a k * bHalf k) h := by
              rw [← mobius_mul_left]
              apply mobius_congr
              intro k hk
              rw [hb_eq k (submask_trans hk hjm)]
              rw [← Int.mul_assoc, Int.mul_comm (a k) 2, Int.mul_assoc]
            rw [hmob_ab]
            have hp : 2 * ((2 : Int) ^ popcount h * boolToInt ((h &&& (E_a ^^^ E_b)) == h)) =
                (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& (E_a ^^^ E_b)) == h) := by
              rw [← Int.mul_assoc, Int.pow_succ, Int.mul_comm (2 : Int)]
            have heq : 2 * (mobius (fun k => a k * bHalf k) h -
                (2 : Int) ^ popcount h * boolToInt ((h &&& (E_a ^^^ E_b)) == h)) =
                2 * mobius (fun k => a k * bHalf k) h -
                (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& (E_a ^^^ E_b)) == h) := by
              rw [Int.mul_sub, hp]
            rwa [heq] at h2
          have hodd_slice : ∀ {E' : Nat} {u : Nat → Int}, E' % 2 = 1 → BitSmooth (2 * m + 1) E' u →
              (Submask (E' / 2) m ∧ ∀ t, Submask t m →
                (2 : Int) ^ (popcount t + 2) ∣
                  (mobius (fun k => u (2 * k + 1) - u (2 * k)) t -
                    (2 : Int) ^ (popcount t + 1) * boolToInt ((t &&& (E' / 2)) == t))) := by
            intro E' u hEp hu
            refine ⟨(submask_two_mul_add_one_iff E' m).mp hu.1, fun t ht => ?_⟩
            have h1 := hu.2 (2 * t + 1) ((submask_odd_left_odd_right t m).mpr ht)
            rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at h1
            have hE2 : E' = 2 * (E' / 2) + 1 := by omega
            have hmask : ((2 * t + 1 &&& E') == 2 * t + 1) = ((t &&& (E' / 2)) == t) := by
              apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
              change Submask (2 * t + 1) E' ↔ Submask t (E' / 2)
              conv => lhs; rw [hE2]
              exact submask_odd_left_odd_right t (E' / 2)
            rwa [hmask] at h1
          by_cases hE1p : E1 % 2 = 0 <;> by_cases hE2p : E2 % 2 = 0
          · have hxor_ev : (E1 ^^^ E2) % 2 = 0 := by
              have h1 : E1 = 2 * (E1 / 2) := by omega
              have h2 : E2 = 2 * (E2 / 2) := by omega
              rw [h1, h2, xor_two_mul_two_mul]; omega
            have hmask : ((2 * h + 1 &&& (E1 ^^^ E2)) == 2 * h + 1) = false := by
              simp only [beq_eq_false_iff_ne]
              change ¬ Submask (2 * h + 1) (E1 ^^^ E2)
              have h2 : E1 ^^^ E2 = 2 * ((E1 ^^^ E2) / 2) := by omega
              rw [h2, submask_two_mul_iff]; omega
            rw [hmask]; simp only [boolToInt, Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.sub_zero]
            have ht1 := bitExcess_mul (bitSmooth_to_bitExcess0 hf0) (bitSmooth_slice_diff_evenE hE2p hg) h hjm
            have ht2 := bitExcess_mul (bitSmooth_slice_diff_evenE hE1p hf) (bitSmooth_to_bitExcess0 hg0) h hjm
            exact dvd_add_of_dvd
              (dvd_add_of_dvd (dvd_two_pow_mono (by omega) ht1) (dvd_two_pow_mono (by omega) ht2))
              hterm3
          · have hE2o : E2 % 2 = 1 := by omega
            have hxor_odd : E1 ^^^ E2 = 2 * ((E1 / 2) ^^^ (E2 / 2)) + 1 := by
              have h1 : E1 = 2 * (E1 / 2) := by omega
              have h2 : E2 = 2 * (E2 / 2) + 1 := by omega
              conv => lhs; rw [h1, h2]
              rw [Nat.xor_comm, xor_odd_two_mul, Nat.xor_comm]
            have hmask : ((2 * h + 1 &&& (E1 ^^^ E2)) == 2 * h + 1) = ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h) := by
              apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
              change Submask (2 * h + 1) (E1 ^^^ E2) ↔ Submask h ((E1 / 2) ^^^ (E2 / 2))
              rw [hxor_odd]; exact submask_odd_left_odd_right h _
            rw [hmask]
            have ht1 := hscale_mul hf0 (hodd_slice hE2o hg)
            have ht2 := dvd_two_pow_mono (a := popcount h + 1 + 1) (b := popcount h + (2 + 0)) (by omega)
              (bitExcess_mul (bitSmooth_slice_diff_evenE hE1p hf) (bitSmooth_to_bitExcess0 hg0) h hjm)
            have hreord : mobius (fun k => f (2 * k) * (g (2 * k + 1) - g (2 * k))) h +
                mobius (fun k => (f (2 * k + 1) - f (2 * k)) * g (2 * k)) h +
                mobius (fun k => (f (2 * k + 1) - f (2 * k)) * (g (2 * k + 1) - g (2 * k))) h -
                (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h) =
                (mobius (fun k => f (2 * k) * (g (2 * k + 1) - g (2 * k))) h -
                  (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h)) +
                mobius (fun k => (f (2 * k + 1) - f (2 * k)) * g (2 * k)) h +
                mobius (fun k => (f (2 * k + 1) - f (2 * k)) * (g (2 * k + 1) - g (2 * k))) h := by omega
            rw [hreord]
            exact dvd_add_of_dvd (dvd_add_of_dvd ht1 ht2) hterm3
          · have hE1o : E1 % 2 = 1 := by omega
            have hxor_odd : E1 ^^^ E2 = 2 * ((E1 / 2) ^^^ (E2 / 2)) + 1 := by
              have h1 : E1 = 2 * (E1 / 2) + 1 := by omega
              have h2 : E2 = 2 * (E2 / 2) := by omega
              conv => lhs; rw [h1, h2]
              exact xor_odd_two_mul (E1 / 2) (E2 / 2)
            have hmask : ((2 * h + 1 &&& (E1 ^^^ E2)) == 2 * h + 1) = ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h) := by
              apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
              change Submask (2 * h + 1) (E1 ^^^ E2) ↔ Submask h ((E1 / 2) ^^^ (E2 / 2))
              rw [hxor_odd]; exact submask_odd_left_odd_right h _
            rw [hmask]
            have ht1 := dvd_two_pow_mono (a := popcount h + 1 + 1) (b := popcount h + (0 + 2)) (by omega)
              (bitExcess_mul (bitSmooth_to_bitExcess0 hf0) (bitSmooth_slice_diff_evenE hE2p hg) h hjm)
            have ht2_raw := hscale_mul hg0 (hodd_slice hE1o hf)
            have ht2 : (2 : Int) ^ (popcount h + 1 + 1) ∣
                (mobius (fun k => (f (2 * k + 1) - f (2 * k)) * g (2 * k)) h -
                  (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h)) := by
              have hcomm : mobius (fun k => (f (2 * k + 1) - f (2 * k)) * g (2 * k)) h =
                  mobius (fun k => g (2 * k) * (f (2 * k + 1) - f (2 * k))) h :=
                mobius_congr (fun k _ => Int.mul_comm _ _)
              rw [hcomm, Nat.xor_comm (E1 / 2)]
              exact ht2_raw
            have hreord : mobius (fun k => f (2 * k) * (g (2 * k + 1) - g (2 * k))) h +
                mobius (fun k => (f (2 * k + 1) - f (2 * k)) * g (2 * k)) h +
                mobius (fun k => (f (2 * k + 1) - f (2 * k)) * (g (2 * k + 1) - g (2 * k))) h -
                (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h) =
                mobius (fun k => f (2 * k) * (g (2 * k + 1) - g (2 * k))) h +
                (mobius (fun k => (f (2 * k + 1) - f (2 * k)) * g (2 * k)) h -
                  (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h)) +
                mobius (fun k => (f (2 * k + 1) - f (2 * k)) * (g (2 * k + 1) - g (2 * k))) h := by omega
            rw [hreord]
            exact dvd_add_of_dvd (dvd_add_of_dvd ht1 ht2) hterm3
          · have hE1o : E1 % 2 = 1 := by omega
            have hE2o : E2 % 2 = 1 := by omega
            have hxor_ev : E1 ^^^ E2 = 2 * ((E1 / 2) ^^^ (E2 / 2)) := by
              have h1 : E1 = 2 * (E1 / 2) + 1 := by omega
              have h2 : E2 = 2 * (E2 / 2) + 1 := by omega
              conv => lhs; rw [h1, h2]
              exact xor_odd_odd (E1 / 2) (E2 / 2)
            have hmask : ((2 * h + 1 &&& (E1 ^^^ E2)) == 2 * h + 1) = false := by
              simp only [beq_eq_false_iff_ne]
              change ¬ Submask (2 * h + 1) (E1 ^^^ E2)
              rw [hxor_ev, submask_two_mul_iff]; omega
            rw [hmask]; simp only [boolToInt, Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.sub_zero]
            have ht1 := hscale_mul hf0 (hodd_slice hE2o hg)
            have ht2_raw := hscale_mul hg0 (hodd_slice hE1o hf)
            have ht2 : (2 : Int) ^ (popcount h + 1 + 1) ∣
                (mobius (fun k => (f (2 * k + 1) - f (2 * k)) * g (2 * k)) h -
                  (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h)) := by
              have hcomm : mobius (fun k => (f (2 * k + 1) - f (2 * k)) * g (2 * k)) h =
                  mobius (fun k => g (2 * k) * (f (2 * k + 1) - f (2 * k))) h :=
                mobius_congr (fun k _ => Int.mul_comm _ _)
              rw [hcomm, Nat.xor_comm (E1 / 2)]
              exact ht2_raw
            have hadd12 := dvd_add_of_dvd ht1 ht2
            have h2b : (2 : Int) ^ (popcount h + 1 + 1) ∣
                ((2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h) +
                 (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h)) := by
              exact ⟨boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h), (two_pow_succ_mul_eq_add _ _).symm⟩
            have htot12 := dvd_add_of_dvd hadd12 h2b
            have hsimp : (mobius (fun k => f (2 * k) * (g (2 * k + 1) - g (2 * k))) h -
                (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h)) +
                (mobius (fun k => (f (2 * k + 1) - f (2 * k)) * g (2 * k)) h -
                (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h)) +
                ((2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h) +
                 (2 : Int) ^ (popcount h + 1) * boolToInt ((h &&& ((E1 / 2) ^^^ (E2 / 2))) == h)) =
                mobius (fun k => f (2 * k) * (g (2 * k + 1) - g (2 * k))) h +
                mobius (fun k => (f (2 * k + 1) - f (2 * k)) * g (2 * k)) h := by omega
            rw [hsimp] at htot12
            exact dvd_add_of_dvd htot12 hterm3

/-! ### Exponent Lifting Compiler -/

theorem bitUnit_pow {n s : Nat} {g : Nat → Int} (hg : BitUnit n s g) (m : Nat) :
    BitUnit n s (fun k => (g k) ^ m) := by
  induction m with
  | zero =>
    refine ⟨by simp, fun j hj hjne => ?_⟩
    have hconst : ∀ x, x ≠ 0 → mobius (fun _ => (1 : Int)) x = 0 := by
      intro x; induction x using nat_strong_ind with
      | step x ihx =>
        intro hx
        by_cases hp : x % 2 = 0
        · have hx2 : x = 2 * (x / 2) := by omega
          rw [hx2, mobius_two_mul]; exact ihx (x / 2) (by omega) (by omega)
        · have hx2 : x = 2 * (x / 2) + 1 := by omega
          rw [hx2, mobius_two_mul_add_one]
          simp only [Int.sub_self]
          exact mobius_zero_fn (x / 2)
    have hpow0 : (fun k => (g k) ^ 0) = (fun _ => (1 : Int)) := by funext k; simp
    rw [hpow0, hconst j hjne]
    exact ⟨0, by simp⟩
  | succ r ih =>
    have hpow : (fun k => (g k) ^ (r + 1)) = (fun k => (g k) ^ r * g k) := by
      funext k; rw [Int.pow_succ]
    rw [hpow]
    exact bitUnit_mul ih hg

/-- **Stage 2 Compiler (Odd Exponents):**
    If `f ∈ BitSmooth n E` with `f 0 = 1`, then for EVERY odd `r`, `f^r ∈ BitSmooth n E`. -/
theorem bitSmooth_pow_odd {n E r : Nat} {f : Nat → Int}
    (hf0 : f 0 = 1) (hf : BitSmooth n E f) (hr : r % 2 = 1) :
    BitSmooth n E (fun k => (f k) ^ r) := by
  let m := r / 2
  have hrm : r = 2 * m + 1 := by omega
  have hsq : BitUnit n 2 (fun k => f k * f k) := bitSmooth_sq_jump hf0 hf
  have hpowm : BitUnit n 2 (fun k => (f k * f k) ^ m) := bitUnit_pow hsq m
  have hsm0 : BitSmooth n 0 (fun k => (f k * f k) ^ m) := bitUnit_to_bitSmooth_zero (by omega) hpowm
  have hmul := bitSmooth_xor_mul hf hsm0
  have hxor0 : E ^^^ 0 = E := Nat.xor_zero E
  rw [hxor0] at hmul
  have heq : (fun k => f k * (f k * f k) ^ m) = (fun k => (f k) ^ r) := by
    funext k
    rw [hrm, Int.pow_succ, Int.mul_comm]
    congr 1
    have hpow_sq : ∀ (a : Int) (t : Nat), (a * a) ^ t = a ^ (2 * t) := by
      intro a t; induction t with
      | zero => simp
      | succ q ihq =>
        have h2 : 2 * (q + 1) = 2 * q + 2 := by omega
        rw [Int.pow_succ, ihq, h2, Int.pow_add, Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
    exact hpow_sq (f k) m
  rwa [heq] at hmul

/-- **Stage 2 Compiler (Even Exponents):**
    If `f ∈ BitSmooth n E` with `f 0 = 1`, then for EVERY positive even `r`,
    `f^r ∈ BitUnit n (v2Nat r + 1)`. -/
theorem bitSmooth_pow_even {n E r : Nat} {f : Nat → Int}
    (hf0 : f 0 = 1) (hf : BitSmooth n E f) (hrpos : r ≠ 0) (hreven : r % 2 = 0) :
    BitUnit n (v2Nat r + 1) (fun k => (f k) ^ r) := by
  induction r using nat_strong_ind with
  | step r ih =>
    let q := r / 2
    have hrq : r = 2 * q := by omega
    have hqne : q ≠ 0 := by omega
    rw [hrq, v2Nat_two_mul q hqne]
    have hpow2 : (fun k => (f k) ^ (2 * q)) = (fun k => (f k) ^ q * (f k) ^ q) := by
      funext k
      have : 2 * q = q + q := by omega
      rw [this, Int.pow_add]
    rw [hpow2]
    by_cases hqp : q % 2 = 0
    · have hih := ih q (by omega) hqne hqp
      have hsq := bitUnit_sq_lift (by omega) hih
      have hexp : v2Nat q + 1 + 1 = 1 + v2Nat q + 1 := by omega
      rwa [hexp] at hsq
    · have hqo : q % 2 = 1 := by omega
      have hfq : BitSmooth n E (fun k => (f k) ^ q) := bitSmooth_pow_odd hf0 hf hqo
      have hfq0 : (f 0) ^ q = 1 := by rw [hf0, Int.one_pow]
      have hsq := bitSmooth_sq_jump hfq0 hfq
      have hvq : v2Nat q = 0 := by
        have : q = 2 * (q / 2) + 1 := by omega
        rw [this, v2Nat_odd]
      rw [hvq]
      exact hsq

/-! ## Section 5: Stage 3 — The Bit-Slice Walsh Spectral Bridge -/

/-- Excess-`s` functions lift directly to `2^(popcount n + s)` divisibility of ALL Walsh coefficients. -/
theorem walsh_bitExcess {n s m : Nat} {f : Nat → Int}
    (hm : Submask m n) (hf : BitExcess n s f) :
    (2 : Int) ^ (popcount n + s) ∣ walsh n m f := by
  induction n using nat_strong_ind generalizing s m f with
  | step n ih =>
    by_cases hn : n = 0
    · subst hn
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero (submask_le hm)
      subst hm0
      rw [walsh_zero, popcount_zero]
      have := hf 0 (submask_zero 0)
      rwa [mobius_zero, popcount_zero] at this
    · by_cases hnp : n % 2 = 0
      · let n' := n / 2
        have hn2 : n = 2 * n' := by omega
        rw [hn2] at hm hf ⊢
        obtain ⟨hm0, hmn'⟩ := (submask_two_mul_iff m n').mp hm
        let m' := m / 2
        have hm2 : m = 2 * m' := by omega
        rw [hm2, popcount_two_mul, walsh_two_mul]
        have hf0 : BitExcess n' s (fun k => f (2 * k)) := by
          intro a ha
          have := hf (2 * a) ((submask_two_mul_left_two_mul_right a n').mpr ha)
          rwa [popcount_two_mul, mobius_two_mul] at this
        exact ih n' (by omega) hmn' hf0
      · let n' := n / 2
        have hn2 : n = 2 * n' + 1 := by omega
        rw [hn2] at hm hf ⊢
        have hmn' : Submask (m / 2) n' := (submask_two_mul_add_one_iff m n').mp hm
        let m' := m / 2
        have hf0 : BitExcess n' s (fun k => f (2 * k)) := by
          intro a ha
          have := hf (2 * a) ((submask_two_mul_left_odd_right a n').mpr ha)
          rwa [popcount_two_mul, mobius_two_mul] at this
        have hdf : BitExcess n' (s + 1) (fun k => f (2 * k + 1) - f (2 * k)) := by
          intro a ha
          have := hf (2 * a + 1) ((submask_odd_left_odd_right a n').mpr ha)
          rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at this
          exact dvd_two_pow_mono (by omega) this
        rw [popcount_two_mul_add_one]
        by_cases hmp : m % 2 = 0
        · have hm2 : m = 2 * m' := by omega
          rw [hm2, walsh_two_mul_add_one_even]
          have h1 := dvd_two_mul_of_dvd (ih n' (by omega) hmn' hf0)
          have h2 := ih n' (by omega) hmn' hdf
          exact dvd_add_of_dvd (dvd_two_pow_mono (by omega) h1) (dvd_two_pow_mono (by omega) h2)
        · have hm2 : m = 2 * m' + 1 := by omega
          rw [hm2, walsh_two_mul_add_one_odd]
          have h2 := ih n' (by omega) hmn' hdf
          exact dvd_neg_of_dvd (dvd_two_pow_mono (by omega) h2)

/-- **Stage 3 Bridge A (Unique Walsh Spike Theorem for `BitSmooth`):**
    For ANY `f ∈ BitSmooth n E` and ANY mask `m <=_2 n`:
    `walsh n m f ≡ (if m = E then 2^(popcount n) else 0)  (mod 2^(popcount n + 1))`. -/
theorem walsh_bitSmooth_spike {n E m : Nat} {f : Nat → Int}
    (hm : Submask m n) (hf : BitSmooth n E f) :
    (2 : Int) ^ (popcount n + 1) ∣
      (walsh n m f - (2 : Int) ^ (popcount n) * boolToInt (m == E)) := by
  induction n using nat_strong_ind generalizing E m f with
  | step n ih =>
    by_cases hn : n = 0
    · subst hn
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero (submask_le hm)
      have hE0 : E = 0 := Nat.eq_zero_of_le_zero (submask_le hf.1)
      subst hm0; subst hE0
      rw [walsh_zero, popcount_zero]
      have h0 := hf.2 0 (submask_zero 0)
      rw [mobius_zero, popcount_zero] at h0
      simpa using h0
    · by_cases hnp : n % 2 = 0
      · let n' := n / 2
        have hn2 : n = 2 * n' := by omega
        rw [hn2] at hm hf ⊢
        obtain ⟨hm0, hmn'⟩ := (submask_two_mul_iff m n').mp hm
        obtain ⟨hE0, hEn'⟩ := (submask_two_mul_iff E n').mp hf.1
        let m' := m / 2
        have hm2 : m = 2 * m' := by omega
        have hE2 : E = 2 * (E / 2) := by omega
        rw [hm2, popcount_two_mul, walsh_two_mul]
        have hf0 : BitSmooth n' (E / 2) (fun k => f (2 * k)) := by
          refine ⟨hEn', fun a ha => ?_⟩
          have h1 := hf.2 (2 * a) ((submask_two_mul_left_two_mul_right a n').mpr ha)
          rw [popcount_two_mul, mobius_two_mul] at h1
          have hmask : ((2 * a &&& E) == 2 * a) = ((a &&& (E / 2)) == a) := by
            conv => lhs; rw [hE2, and_two_mul_two_mul]
            exact beq_two_mul_eq (a &&& (E / 2)) a
          rwa [hmask] at h1
        have heq_b : (2 * m' == E) = (m' == E / 2) := by
          conv => lhs; rw [hE2]
          exact beq_two_mul_eq m' (E / 2)
        rw [heq_b]
        exact ih n' (by omega) hmn' hf0
      · let n' := n / 2
        have hn2 : n = 2 * n' + 1 := by omega
        rw [hn2] at hm hf ⊢
        have hmn' : Submask (m / 2) n' := (submask_two_mul_add_one_iff m n').mp hm
        let m' := m / 2
        have hf0 := bitSmooth_slice_even hf
        rw [popcount_two_mul_add_one]
        by_cases hEp : E % 2 = 0
        · have hE2 : E = 2 * (E / 2) := by omega
          have hdf2 := bitSmooth_slice_diff_evenE hEp hf
          have hwdf : (2 : Int) ^ (popcount n' + 1 + 1) ∣ walsh n' m' (fun k => f (2 * k + 1) - f (2 * k)) :=
            dvd_two_pow_mono (by omega) (walsh_bitExcess hmn' hdf2)
          by_cases hmp : m % 2 = 0
          · have hm2 : m = 2 * m' := by omega
            rw [hm2, walsh_two_mul_add_one_even]
            have heq_b : (2 * m' == E) = (m' == E / 2) := by
              conv => lhs; rw [hE2]
              exact beq_two_mul_eq m' (E / 2)
            rw [heq_b]
            have h1 := dvd_two_mul_of_dvd (ih n' (by omega) hmn' hf0)
            have hp : (2 : Int) * (2 : Int) ^ popcount n' = (2 : Int) ^ (popcount n' + 1) := by
              rw [Int.pow_succ, Int.mul_comm]
            have h1' : (2 : Int) ^ (popcount n' + 1 + 1) ∣
                (2 * walsh n' m' (fun k => f (2 * k)) -
                  (2 : Int) ^ (popcount n' + 1) * boolToInt (m' == E / 2)) := by
              have hsimp : 2 * (walsh n' m' (fun k => f (2 * k)) -
                  (2 : Int) ^ popcount n' * boolToInt (m' == E / 2)) =
                  2 * walsh n' m' (fun k => f (2 * k)) -
                  (2 : Int) ^ (popcount n' + 1) * boolToInt (m' == E / 2) := by
                rw [Int.mul_sub, ← Int.mul_assoc, hp]
              rwa [hsimp] at h1
            have hreord : 2 * walsh n' m' (fun k => f (2 * k)) + walsh n' m' (fun k => f (2 * k + 1) - f (2 * k)) -
                (2 : Int) ^ (popcount n' + 1) * boolToInt (m' == E / 2) =
                (2 * walsh n' m' (fun k => f (2 * k)) - (2 : Int) ^ (popcount n' + 1) * boolToInt (m' == E / 2)) +
                walsh n' m' (fun k => f (2 * k + 1) - f (2 * k)) := by omega
            rw [hreord]
            exact dvd_add_of_dvd h1' hwdf
          · have hm2 : m = 2 * m' + 1 := by omega
            rw [hm2, walsh_two_mul_add_one_odd]
            have hne : (2 * m' + 1 == E) = false := by
              simp only [beq_eq_false_iff_ne]; omega
            rw [hne]; simp only [boolToInt, Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.sub_zero]
            exact dvd_neg_of_dvd hwdf
        · have hEo : E % 2 = 1 := by omega
          have hE2 : E = 2 * (E / 2) + 1 := by omega
          have hdf_even : ∀ k, Submask k n' → 2 ∣ (f (2 * k + 1) - f (2 * k)) := by
            intro k hk
            rw [← sumSubmasks_mobius (fun r => f (2 * r + 1) - f (2 * r)) k]
            rw [sumSubmasks_eq_sumLucasFiltered]
            unfold sumLucasFiltered
            apply sumRange_dvd
            intro t _
            by_cases htk : t &&& k = t
            · simp only [htk, ↓reduceIte]
              have htn := submask_trans htk hk
              have h1 := bitSmooth_to_bitExcess0 hf (2 * t + 1) ((submask_odd_left_odd_right t n').mpr htn)
              rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at h1
              exact dvd_two_pow_mono (a := 1) (b := popcount t + 1) (by omega) h1
            · simp [htk]
          let dfHalf : Nat → Int := fun k => (f (2 * k + 1) - f (2 * k)) / 2
          have hdf_eq : ∀ k, Submask k n' → f (2 * k + 1) - f (2 * k) = 2 * dfHalf k := by
            intro k hk
            obtain ⟨q, hq⟩ := hdf_even k hk
            dsimp [dfHalf]; omega
          have hdfHalf_smooth : BitSmooth n' (E / 2) dfHalf := by
            refine ⟨(submask_two_mul_add_one_iff E n').mp hf.1, fun t ht => ?_⟩
            have hmob : mobius (fun k => f (2 * k + 1) - f (2 * k)) t = 2 * mobius dfHalf t := by
              rw [← mobius_mul_left]
              exact mobius_congr (fun k hk => hdf_eq k (submask_trans hk ht))
            have h1 := hf.2 (2 * t + 1) ((submask_odd_left_odd_right t n').mpr ht)
            rw [popcount_two_mul_add_one, mobius_two_mul_add_one, hmob] at h1
            have hmask : ((2 * t + 1 &&& E) == 2 * t + 1) = ((t &&& (E / 2)) == t) := by
              apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
              change Submask (2 * t + 1) E ↔ Submask t (E / 2)
              conv => lhs; rw [hE2]
              exact submask_odd_left_odd_right t (E / 2)
            rw [hmask] at h1
            obtain ⟨q, hq⟩ := h1
            refine ⟨q, ?_⟩
            have hp1 : (2 : Int) ^ (popcount t + 1) = 2 * (2 : Int) ^ popcount t := by
              rw [Int.pow_succ, Int.mul_comm]
            have hp2 : (2 : Int) ^ (popcount t + 1 + 1) = 2 * (2 : Int) ^ (popcount t + 1) := by
              rw [Int.pow_succ, Int.mul_comm]
            rw [hp1, hp2, Int.mul_assoc 2, Int.mul_assoc 2] at hq; omega
          have hwdf_eq : walsh n' m' (fun k => f (2 * k + 1) - f (2 * k)) = 2 * walsh n' m' dfHalf := by
            unfold walsh
            rw [← sumSubmasks_mul_left]
            apply sumSubmasks_congr
            intro k hk
            dsimp only; rw [hdf_eq k hk, ← Int.mul_assoc, Int.mul_comm _ 2, Int.mul_assoc]
          have hih0 := dvd_two_mul_of_dvd (ih n' (by omega) hmn' hf0)
          have hih1 := dvd_two_mul_of_dvd (ih n' (by omega) hmn' hdfHalf_smooth)
          have hp : (2 : Int) * (2 : Int) ^ popcount n' = (2 : Int) ^ (popcount n' + 1) := by
            rw [Int.pow_succ, Int.mul_comm]
          by_cases hmp : m % 2 = 0
          · have hm2 : m = 2 * m' := by omega
            rw [hm2, walsh_two_mul_add_one_even, hwdf_eq]
            have hne : (2 * m' == E) = false := by
              simp only [beq_eq_false_iff_ne]; omega
            rw [hne]; simp only [boolToInt, Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.sub_zero]
            have hadd := dvd_add_of_dvd hih0 hih1
            have h2b : (2 : Int) ^ (popcount n' + 1 + 1) ∣
                ((2 : Int) ^ (popcount n' + 1) * boolToInt (m' == E / 2) +
                 (2 : Int) ^ (popcount n' + 1) * boolToInt (m' == E / 2)) := by
              exact ⟨boolToInt (m' == E / 2), (two_pow_succ_mul_eq_add _ _).symm⟩
            have htot := dvd_add_of_dvd hadd h2b
            have hsimp : 2 * (walsh n' m' (fun k => f (2 * k)) - (2 : Int) ^ popcount n' * boolToInt (m' == E / 2)) +
                2 * (walsh n' m' dfHalf - (2 : Int) ^ popcount n' * boolToInt (m' == E / 2)) +
                ((2 : Int) ^ (popcount n' + 1) * boolToInt (m' == E / 2) +
                 (2 : Int) ^ (popcount n' + 1) * boolToInt (m' == E / 2)) =
                2 * walsh n' m' (fun k => f (2 * k)) + 2 * walsh n' m' dfHalf := by
              rw [Int.mul_sub, Int.mul_sub, ← Int.mul_assoc, hp]; omega
            rwa [hsimp] at htot
          · have hm2 : m = 2 * m' + 1 := by omega
            rw [hm2, walsh_two_mul_add_one_odd, hwdf_eq]
            have heq_b : (2 * m' + 1 == E) = (m' == E / 2) := by
              conv => lhs; rw [hE2]
              exact beq_two_mul_add_one_eq m' (E / 2)
            rw [heq_b]
            have hneg := dvd_neg_of_dvd hih1
            have h2b : (2 : Int) ^ (popcount n' + 1 + 1) ∣
                (2 * ((2 : Int) ^ (popcount n' + 1) * boolToInt (m' == E / 2))) := by
              refine ⟨boolToInt (m' == E / 2), ?_⟩
              rw [Int.pow_succ (2 : Int) (popcount n' + 1), Int.mul_comm ((2 : Int) ^ (popcount n' + 1)) 2,
                Int.mul_assoc 2]
            have htot := dvd_sub_of_dvd hneg h2b
            have hsimp : -(2 * (walsh n' m' dfHalf - (2 : Int) ^ popcount n' * boolToInt (m' == E / 2))) -
                2 * ((2 : Int) ^ (popcount n' + 1) * boolToInt (m' == E / 2)) =
                -(2 * walsh n' m' dfHalf) - (2 : Int) ^ (popcount n' + 1) * boolToInt (m' == E / 2) := by
              rw [Int.mul_sub, ← Int.mul_assoc, hp]; omega
            rwa [hsimp] at htot

/-- **Stage 3 Bridge B (Higher-Modulus Walsh Congruence for `BitUnit n s`):**
    For ANY `g ∈ BitUnit n s` (`s >= 1`) and ANY mask `m <=_2 n`:
    `walsh n m g ≡ (if m = 0 then 2^(popcount n) else 0)  (mod 2^(popcount n + s))`. -/
theorem walsh_bitUnit_congr {n s m : Nat} {g : Nat → Int} (_hs : 1 ≤ s)
    (hm : Submask m n) (hg : BitUnit n s g) :
    (2 : Int) ^ (popcount n + s) ∣
      (walsh n m g - (2 : Int) ^ (popcount n) * boolToInt (m == 0)) := by
  induction n using nat_strong_ind generalizing m g with
  | step n ih =>
    by_cases hn : n = 0
    · subst hn
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero (submask_le hm)
      subst hm0
      rw [walsh_zero, popcount_zero, hg.1]
      simp [boolToInt]
    · by_cases hnp : n % 2 = 0
      · let n' := n / 2
        have hn2 : n = 2 * n' := by omega
        rw [hn2] at hm hg ⊢
        obtain ⟨hm0, hmn'⟩ := (submask_two_mul_iff m n').mp hm
        let m' := m / 2
        have hm2 : m = 2 * m' := by omega
        rw [hm2, popcount_two_mul, walsh_two_mul]
        have hg0 : BitUnit n' s (fun k => g (2 * k)) := by
          refine ⟨by simpa using hg.1, fun a ha hane => ?_⟩
          have := hg.2 (2 * a) ((submask_two_mul_left_two_mul_right a n').mpr ha) (by omega)
          rwa [popcount_two_mul, mobius_two_mul] at this
        have heq0 : (2 * m' == 0) = (m' == 0) := beq_two_mul_zero m'
        rw [heq0]
        exact ih n' (by omega) hmn' hg0
      · let n' := n / 2
        have hn2 : n = 2 * n' + 1 := by omega
        rw [hn2] at hm hg ⊢
        have hmn' : Submask (m / 2) n' := (submask_two_mul_add_one_iff m n').mp hm
        let m' := m / 2
        have hg0 : BitUnit n' s (fun k => g (2 * k)) := by
          refine ⟨by simpa using hg.1, fun a ha hane => ?_⟩
          have := hg.2 (2 * a) ((submask_two_mul_left_odd_right a n').mpr ha) (by omega)
          rwa [popcount_two_mul, mobius_two_mul] at this
        have hdg : BitExcess n' (s + 1) (fun k => g (2 * k + 1) - g (2 * k)) := by
          intro a ha
          have := hg.2 (2 * a + 1) ((submask_odd_left_odd_right a n').mpr ha) (by omega)
          rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at this
          exact dvd_two_pow_mono (by omega) this
        have hwdg : (2 : Int) ^ (popcount n' + 1 + s) ∣
            walsh n' m' (fun k => g (2 * k + 1) - g (2 * k)) :=
          dvd_two_pow_mono (by omega) (walsh_bitExcess hmn' hdg)
        rw [popcount_two_mul_add_one]
        by_cases hmp : m % 2 = 0
        · have hm2 : m = 2 * m' := by omega
          rw [hm2, walsh_two_mul_add_one_even]
          have heq0 : (2 * m' == 0) = (m' == 0) := beq_two_mul_zero m'
          rw [heq0]
          have h1 := dvd_two_mul_of_dvd (ih n' (by omega) hmn' hg0)
          have hp : (2 : Int) * (2 : Int) ^ popcount n' = (2 : Int) ^ (popcount n' + 1) := by
            rw [Int.pow_succ, Int.mul_comm]
          have h1' : (2 : Int) ^ (popcount n' + 1 + s) ∣
              (2 * walsh n' m' (fun k => g (2 * k)) -
                (2 : Int) ^ (popcount n' + 1) * boolToInt (m' == 0)) := by
            have hsimp : 2 * (walsh n' m' (fun k => g (2 * k)) -
                (2 : Int) ^ popcount n' * boolToInt (m' == 0)) =
                2 * walsh n' m' (fun k => g (2 * k)) -
                (2 : Int) ^ (popcount n' + 1) * boolToInt (m' == 0) := by
              rw [Int.mul_sub, ← Int.mul_assoc, hp]
            rw [hsimp] at h1
            exact dvd_two_pow_mono (by omega) h1
          have hreord : 2 * walsh n' m' (fun k => g (2 * k)) + walsh n' m' (fun k => g (2 * k + 1) - g (2 * k)) -
              (2 : Int) ^ (popcount n' + 1) * boolToInt (m' == 0) =
              (2 * walsh n' m' (fun k => g (2 * k)) - (2 : Int) ^ (popcount n' + 1) * boolToInt (m' == 0)) +
              walsh n' m' (fun k => g (2 * k + 1) - g (2 * k)) := by omega
          rw [hreord]
          exact dvd_add_of_dvd h1' hwdg
        · have hm2 : m = 2 * m' + 1 := by omega
          rw [hm2, walsh_two_mul_add_one_odd]
          have hne : (2 * m' + 1 == 0) = false := by
            simp only [beq_eq_false_iff_ne]; omega
          rw [hne]; simp only [boolToInt, Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.sub_zero]
          exact dvd_neg_of_dvd hwdg

/-! ## Section 6: Connecting Stage 1 to Stages 2–3 — Five Sharp Infinite Theorems -/

/-- **Stage 1 -> Stage 2 Instantiation:**
    For EVERY `n : Nat`, `k ↦ C(n, k)` lies in `BitSmooth n (endpointMask n)`. -/
theorem binom_bitSmooth (n : Nat) :
    BitSmooth n (endpointMask n) (fun k => binomZ n (k : Int)) := by
  refine ⟨endpointMask_submask n, fun j hj => ?_⟩
  have h1 := (delta_exact_mod2 n).1 j hj
  unfold Delta alphaCF at h1
  simpa using h1

/-- **Main Theorem 1 (Walsh-Lucas Unique Spike Theorem for Odd Powers):**
    For ALL `n : Nat`, ALL odd `r : Nat`, and ALL masks `m <=_2 n`:
    `∑_{k <=_2 n} (-1)^popcount(k &&& m) * C(n, k)^r ≡ 2^(popcount n) * [m = E(n)]  (mod 2^(popcount n + 1))`. -/
theorem walsh_lucas_binom_odd_pow (n r m : Nat) (hr : r % 2 = 1) (hm : Submask m n) :
    (2 : Int) ^ (popcount n + 1) ∣
      (walsh n m (fun k => (binomZ n (k : Int)) ^ r) -
        (2 : Int) ^ (popcount n) * boolToInt (m == endpointMask n)) := by
  have hsm := bitSmooth_pow_odd (binomZ_zero_right n) (binom_bitSmooth n) hr
  exact walsh_bitSmooth_spike hm hsm

/-- **Main Theorem 2 (Sparse-Bit Exact Valuation Criterion for Odd Powers):**
    For ALL `n : Nat` and ALL odd `r : Nat`, let `S = ∑_{k <=_2 n} C(n, k)^r`.
    1. `2^(popcount n) | S` unconditionally.
    2. `2^(popcount n + 1) ∤ S` (i.e. `v_2(S) = popcount n`)
       **if and only if** `n` has no adjacent `1`-bits (`n &&& (n >>> 1) = 0`). -/
theorem lucas_binom_odd_pow_sparse_iff (n r : Nat) (hr : r % 2 = 1) :
    (2 : Int) ^ (popcount n) ∣ sumSubmasks n (fun k => (binomZ n (k : Int)) ^ r) ∧
    (¬ ((2 : Int) ^ (popcount n + 1) ∣ sumSubmasks n (fun k => (binomZ n (k : Int)) ^ r)) ↔
      n &&& (n >>> 1) = 0) := by
  have hw := walsh_lucas_binom_odd_pow n r 0 hr (submask_zero n)
  rw [walsh_zero_mask] at hw
  constructor
  · have h1 := dvd_two_pow_mono (a := popcount n) (b := popcount n + 1) (by omega) hw
    have h2 : (2 : Int) ^ popcount n ∣
        (2 : Int) ^ popcount n * boolToInt (0 == endpointMask n) := ⟨_, rfl⟩
    have hsum := dvd_add_of_dvd h1 h2
    simpa [Int.sub_add_cancel] using hsum
  · rw [← endpointMask_eq_zero_iff]
    by_cases hE : endpointMask n = 0
    · have hb : (0 == endpointMask n) = true := by simp [hE]
      rw [hb] at hw
      simp only [boolToInt, ↓reduceIte, Int.mul_one] at hw
      have hndvd := (not_dvd_two_pow_succ_of_congr hw).2
      simp [hE, hndvd]
    · have hb : (0 == endpointMask n) = false := by
        simp only [beq_eq_false_iff_ne]; exact Ne.symm hE
      rw [hb] at hw
      simp only [boolToInt, Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.sub_zero] at hw
      simp [hE, hw]

/-- **Main Theorem 3 (Walsh-Lucas Higher-Modulus Congruence for Even Powers):**
    For ALL `n : Nat`, ALL positive even `r : Nat` (`r ≠ 0`, `r % 2 = 0`), and ALL `m <=_2 n`:
    `∑_{k <=_2 n} (-1)^popcount(k &&& m) * C(n, k)^r ≡ 2^(popcount n) * [m = 0]  (mod 2^(popcount n + v2(r) + 1))`. -/
theorem walsh_lucas_binom_even_pow (n r m : Nat) (hrpos : r ≠ 0) (hreven : r % 2 = 0)
    (hm : Submask m n) :
    (2 : Int) ^ (popcount n + (v2Nat r + 1)) ∣
      (walsh n m (fun k => (binomZ n (k : Int)) ^ r) -
        (2 : Int) ^ (popcount n) * boolToInt (m == 0)) := by
  have hu := bitSmooth_pow_even (binomZ_zero_right n) (binom_bitSmooth n) hrpos hreven
  exact walsh_bitUnit_congr (by omega) hm hu

/-- **Main Theorem 3 Corollary (Exact Universal `v_2` Valuation for Even Powers):**
    For ALL `n : Nat` and ALL positive even `r : Nat`:
    `v_2(∑_{k <=_2 n} C(n, k)^r) = popcount n`, AND
    `∑_{k <=_2 n} C(n, k)^r ≡ 2^(popcount n)  (mod 2^(popcount n + v2(r) + 1))`. -/
theorem lucas_binom_even_pow_exact_v2 (n r : Nat) (hrpos : r ≠ 0) (hreven : r % 2 = 0) :
    (2 : Int) ^ (popcount n + (v2Nat r + 1)) ∣
      (sumSubmasks n (fun k => (binomZ n (k : Int)) ^ r) - (2 : Int) ^ (popcount n)) ∧
    (2 : Int) ^ (popcount n) ∣ sumSubmasks n (fun k => (binomZ n (k : Int)) ^ r) ∧
    ¬ ((2 : Int) ^ (popcount n + 1) ∣ sumSubmasks n (fun k => (binomZ n (k : Int)) ^ r)) := by
  have hw := walsh_lucas_binom_even_pow n r 0 hrpos hreven (submask_zero n)
  rw [walsh_zero_mask] at hw
  simp only [beq_self_eq_true, boolToInt, ↓reduceIte, Int.mul_one] at hw
  have h1 := dvd_two_pow_mono (a := popcount n + 1) (b := popcount n + (v2Nat r + 1)) (by omega) hw
  have ⟨hd, hnd⟩ := not_dvd_two_pow_succ_of_congr h1
  exact ⟨hw, hd, hnd⟩

/-- **Main Theorem 4 (Mixed-Product XOR-Spike Theorem):**
    For ALL `n, n1, n2 : Nat` with `n <=_2 n1` and `n <=_2 n2`, ALL odd `r1, r2`,
    and ALL `m <=_2 n`, the unique Walsh spike mask of `C(n1, k)^r1 * C(n2, k)^r2`
    on the Lucas cube of `n` is `(E(n1) ^^^ E(n2)) &&& n`. -/
theorem walsh_lucas_mixed_product (n n1 n2 r1 r2 m : Nat)
    (h1 : Submask n n1) (h2 : Submask n n2)
    (hr1 : r1 % 2 = 1) (hr2 : r2 % 2 = 1) (hm : Submask m n) :
    (2 : Int) ^ (popcount n + 1) ∣
      (walsh n m (fun k => (binomZ n1 (k : Int)) ^ r1 * (binomZ n2 (k : Int)) ^ r2) -
        (2 : Int) ^ (popcount n) * boolToInt (m == ((endpointMask n1 ^^^ endpointMask n2) &&& n))) := by
  have hf1 := bitSmooth_restrict h1 (bitSmooth_pow_odd (binomZ_zero_right n1) (binom_bitSmooth n1) hr1)
  have hf2 := bitSmooth_restrict h2 (bitSmooth_pow_odd (binomZ_zero_right n2) (binom_bitSmooth n2) hr2)
  have hprod := bitSmooth_xor_mul hf1 hf2
  have hdist : (endpointMask n1 &&& n) ^^^ (endpointMask n2 &&& n) =
      (endpointMask n1 ^^^ endpointMask n2) &&& n := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor]
    cases (endpointMask n1).testBit i <;> cases (endpointMask n2).testBit i <;> cases n.testBit i <;> rfl
  rw [hdist] at hprod
  exact walsh_bitSmooth_spike hm hprod

/-- **Bonus Theorem 5 (Pure-Silicon Lucas-Mask Mod-4 Theorem):**
    For ALL `n : Nat` and ALL `k <=_2 n`:
    `C(n, k) ≡ (-1)^popcount(k &&& endpointMask n)  (mod 4)`. -/
theorem lucas_binom_mod4 (n k : Nat) (hk : Submask k n) :
    (4 : Int) ∣ (binomZ n (k : Int) - (if popcount (k &&& endpointMask n) % 2 = 0 then 1 else -1)) := by
  have hsm := binom_bitSmooth n
  suffices hgen : ∀ (m E : Nat) (f : Nat → Int), f 0 = 1 → BitSmooth m E f →
      (4 : Int) ∣ (f m - (if popcount (m &&& E) % 2 = 0 then 1 else -1)) by
    have hres := bitSmooth_restrict hk hsm
    have h4 := hgen k (endpointMask n &&& k) (fun t => binomZ n (t : Int)) (binomZ_zero_right n) hres
    have hand : k &&& (endpointMask n &&& k) = k &&& endpointMask n := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_and]
      cases k.testBit i <;> cases (endpointMask n).testBit i <;> rfl
    rwa [hand] at h4
  intro m E f hf0 hf
  induction m using nat_strong_ind generalizing E f with
  | step m ih =>
    by_cases hm0 : m = 0
    · subst hm0
      rw [hf0, Nat.zero_and, popcount_zero]
      decide
    · by_cases hmp : m % 2 = 0
      · let m' := m / 2
        have hm2 : m = 2 * m' := by omega
        rw [hm2] at hf ⊢
        obtain ⟨hE0, hEm'⟩ := (submask_two_mul_iff E m').mp hf.1
        have hE2 : E = 2 * (E / 2) := by omega
        have hf' : BitSmooth m' (E / 2) (fun r => f (2 * r)) := by
          refine ⟨hEm', fun a ha => ?_⟩
          have h1 := hf.2 (2 * a) ((submask_two_mul_left_two_mul_right a m').mpr ha)
          rw [popcount_two_mul, mobius_two_mul] at h1
          have hmask : ((2 * a &&& E) == 2 * a) = ((a &&& (E / 2)) == a) := by
            conv => lhs; rw [hE2, and_two_mul_two_mul]
            exact beq_two_mul_eq (a &&& (E / 2)) a
          rwa [hmask] at h1
        have hand : (2 * m') &&& E = 2 * (m' &&& (E / 2)) := by
          conv => lhs; rw [hE2]
          exact and_two_mul_two_mul m' (E / 2)
        rw [hand, popcount_two_mul]
        exact ih m' (by omega) (E / 2) (fun r => f (2 * r)) (by simpa using hf0) hf'
      · let m' := m / 2
        have hm2 : m = 2 * m' + 1 := by omega
        rw [hm2] at hf ⊢
        have hf0' := bitSmooth_slice_even hf
        have hih := ih m' (by omega) (E / 2) (fun r => f (2 * r)) (by simpa using hf0) hf0'
        let df : Nat → Int := fun r => f (2 * r + 1) - f (2 * r)
        have hdiff_eq : f (2 * m' + 1) - f (2 * m') = sumSubmasks m' (mobius df) :=
          (sumSubmasks_mobius df m').symm
        have hsum_split : sumSubmasks m' (mobius df) - mobius df 0 =
            sumRange (m' + 1) (fun j => if j ≠ 0 ∧ j &&& m' = j then mobius df j else 0) := by
          rw [sumSubmasks_eq_sumLucasFiltered]
          unfold sumLucasFiltered
          rw [sumRange_split_first m', sumRange_split_first m']
          have h0 : (if (0 : Nat) &&& m' = 0 then mobius df 0 else 0) = mobius df 0 := by simp
          have h0' : (if (0 : Nat) ≠ 0 ∧ (0 : Nat) &&& m' = 0 then mobius df 0 else 0) = 0 := by simp
          rw [h0, h0', Int.zero_add]
          have htail : sumRange m' (fun i => if (i + 1) &&& m' = i + 1 then mobius df (i + 1) else 0) =
              sumRange m' (fun i => if (i + 1) ≠ 0 ∧ (i + 1) &&& m' = i + 1 then mobius df (i + 1) else 0) := by
            apply sumRange_congr; intro i _; simp
          rw [htail]; omega
        have htail_dvd : (4 : Int) ∣ (sumSubmasks m' (mobius df) - mobius df 0) := by
          rw [hsum_split]
          apply sumRange_dvd
          intro j _
          split
          · rename_i hj
            have h1 := bitSmooth_to_bitExcess0 hf (2 * j + 1) ((submask_odd_left_odd_right j m').mpr hj.2)
            rw [popcount_two_mul_add_one, mobius_two_mul_add_one] at h1
            have hpc := popcount_pos_of_ne_zero hj.1
            have h4 : (2 : Int) ^ 2 ∣ mobius df j := dvd_two_pow_mono (by omega) h1
            simpa using h4
          · exact ⟨0, by simp⟩
        have h0_dvd : (4 : Int) ∣ (mobius df 0 - 2 * boolToInt (E % 2 == 1)) := by
          have h1 := hf.2 1 ((submask_odd_left_odd_right 0 m').mpr (submask_zero m'))
          have h1eq : (1 : Nat) = 2 * 0 + 1 := rfl
          rw [h1eq, popcount_two_mul_add_one, popcount_zero, mobius_two_mul_add_one] at h1
          have hmask : ((2 * 0 + 1 &&& E) == 2 * 0 + 1) = (E % 2 == 1) := by
            have hand1 : 1 &&& E = E % 2 := by
              apply Nat.eq_of_testBit_eq; intro i
              rw [Nat.testBit_and]
              cases i with
              | zero =>
                rw [Nat.testBit_zero, Nat.testBit_zero]
                by_cases hp : E % 2 = 0
                · simp [hp]
                · have hp1 : E % 2 = 1 := by omega
                  simp [hp1]
              | succ r =>
                have h1b : (1 : Nat).testBit (r + 1) = false := by rw [Nat.testBit_succ]; simp
                have hmb : (E % 2).testBit (r + 1) = false := by
                  rw [Nat.testBit_succ]
                  have : (E % 2) / 2 = 0 := by omega
                  simp [this]
                simp [h1b, hmb]
            have h1 : (2 * 0 + 1 &&& E) = E % 2 := hand1; simp [h1]
          rw [hmask] at h1
          simpa using h1
        have hdiff_mod4 : (4 : Int) ∣ ((f (2 * m' + 1) - f (2 * m')) - 2 * boolToInt (E % 2 == 1)) := by
          rw [hdiff_eq]
          have hadd := dvd_add_of_dvd htail_dvd h0_dvd
          have hsimp : (sumSubmasks m' (mobius df) - mobius df 0) + (mobius df 0 - 2 * boolToInt (E % 2 == 1)) =
              sumSubmasks m' (mobius df) - 2 * boolToInt (E % 2 == 1) := by omega
          rwa [hsimp] at hadd
        have hsum_mod4 := dvd_add_of_dvd hih hdiff_mod4
        by_cases hEp : E % 2 = 0
        · have hE2 : E = 2 * (E / 2) := by omega
          have hand : (2 * m' + 1) &&& E = 2 * (m' &&& (E / 2)) := by
            conv => lhs; rw [hE2]
            exact and_odd_two_mul m' (E / 2)
          rw [hand, popcount_two_mul]
          have hbe : (E % 2 == 1) = false := by simp [hEp]
          rw [hbe] at hsum_mod4
          simp only [boolToInt, Bool.false_eq_true, ↓reduceIte, Int.mul_zero, Int.sub_zero] at hsum_mod4
          have hsimp : f (2 * m') - (if popcount (m' &&& (E / 2)) % 2 = 0 then (1 : Int) else -1) +
              (f (2 * m' + 1) - f (2 * m')) =
              f (2 * m' + 1) - (if popcount (m' &&& (E / 2)) % 2 = 0 then (1 : Int) else -1) := by omega
          rwa [hsimp] at hsum_mod4
        · have hEo : E % 2 = 1 := by omega
          have hE2 : E = 2 * (E / 2) + 1 := by omega
          have hand : (2 * m' + 1) &&& E = 2 * (m' &&& (E / 2)) + 1 := by
            conv => lhs; rw [hE2]
            exact and_odd_odd m' (E / 2)
          rw [hand, popcount_two_mul_add_one]
          have hbe : (E % 2 == 1) = true := by simp [hEo]
          rw [hbe] at hsum_mod4
          simp only [boolToInt, ↓reduceIte, Int.mul_one] at hsum_mod4
          by_cases hpc : popcount (m' &&& (E / 2)) % 2 = 0
          · have hpc1 : (popcount (m' &&& (E / 2)) + 1) % 2 ≠ 0 := by omega
            simp only [hpc, ↓reduceIte] at hsum_mod4
            simp only [hpc1, ↓reduceIte]
            have h4 : (4 : Int) ∣ (4 : Int) := ⟨1, by decide⟩
            have htot := dvd_add_of_dvd hsum_mod4 h4
            have hsimp : f (2 * m') - 1 + (f (2 * m' + 1) - f (2 * m') - 2) + 4 =
                f (2 * m' + 1) - (-1) := by omega
            rwa [hsimp] at htot
          · have hpc1 : (popcount (m' &&& (E / 2)) + 1) % 2 = 0 := by omega
            simp only [hpc, ↓reduceIte] at hsum_mod4
            simp only [hpc1, ↓reduceIte]
            have hsimp : f (2 * m') - (-1) + (f (2 * m' + 1) - f (2 * m') - 2) =
                f (2 * m' + 1) - 1 := by omega
            rwa [hsimp] at hsum_mod4

/-! ## Section 7: Kernel-Checked Non-Vacuity Witnesses & Sharpness Counterexamples -/

/-- Non-vacuity witness 1: `n = 7` (`0b111`), `E(7) = 5` (`0b101`), `r = 1`, `m = 5`:
    `W(7, 5) = -40 ≡ 8 (mod 16)` (exact `v_2 = 3 = popcount 7`). -/
example :
    Submask 5 7 ∧ endpointMask 7 = 5 ∧ popcount 7 = 3 ∧
    walsh 7 5 (fun k => (binomZ 7 (k : Int)) ^ 1) = -40 ∧
    (2 : Int) ^ 3 ∣ (-40 : Int) ∧ ¬ ((2 : Int) ^ 4 ∣ (-40 : Int)) := by
  decide

/-- Non-vacuity witness 2: sparse `n = 21` (`0b10101`), `n &&& (n >>> 1) = 0`, `popcount 21 = 3`,
    `r = 1`: unweighted Lucas-mask sum hits exact `v_2 = 3`. -/
example :
    21 &&& (21 >>> 1) = 0 ∧ endpointMask 21 = 0 ∧ popcount 21 = 3 ∧
    sumSubmasks 21 (fun k => binomZ 21 (k : Int)) = 52712 ∧
    (2 : Int) ^ 3 ∣ (52712 : Int) ∧ ¬ ((2 : Int) ^ 4 ∣ (52712 : Int)) := by
  decide

/-- Non-vacuity witness 3: even power `r = 4` (`v2(4) = 2`), `n = 15` (`popcount = 4`):
    `S_4(15) ≡ 16 (mod 128)`. -/
example :
    v2Nat 4 = 2 ∧ popcount 15 = 4 ∧
    (2 : Int) ^ (4 + (2 + 1)) ∣ (sumSubmasks 15 (fun k => (binomZ 15 (k : Int)) ^ 4) - (2 : Int) ^ 4) := by
  have hv : v2Nat 4 = 2 := by decide
  have hp : popcount 15 = 4 := by decide
  have h := (lucas_binom_even_pow_exact_v2 15 4 (by decide) (by decide)).1
  rw [hv, hp] at h
  exact ⟨hv, hp, h⟩

/-- Non-vacuity witness 4: mixed-product XOR-spike theorem instantiated at
    `n = 5`, `n1 = 7` (`E(7) = 5`), `n2 = 13` (`E(13) = 12`):
    `Submask 5 7`, `Submask 5 13`, target spike `(5 ^^^ 12) &&& 5 = 1`, exact `v_2 = 2`. -/
example :
    Submask 5 7 ∧ Submask 5 13 ∧ Submask 1 5 ∧
    ((endpointMask 7 ^^^ endpointMask 13) &&& 5) = 1 ∧
    (2 : Int) ^ 2 ∣ walsh 5 1 (fun k => binomZ 7 (k : Int) * binomZ 13 (k : Int)) ∧
    ¬ ((2 : Int) ^ 3 ∣ walsh 5 1 (fun k => binomZ 7 (k : Int) * binomZ 13 (k : Int))) := by
  decide

/-- Sharpness CE-1: Dropping `Submask j n` breaks Stage 1 (`n = 2, j = 1`):
    `Delta 2 1 0 = 1`, not divisible by `2^(popcount 1) = 2`. -/
theorem sharpness_non_submask :
    ¬ Submask 1 2 ∧ Delta 2 1 0 = 1 ∧ ¬ ((2 : Int) ^ (popcount 1) ∣ Delta 2 1 0) := by
  decide

/-- Sharpness CE-2: The modulus `2^(popcount n + v2(r) + 1)` in Theorem 3 is SHARP:
    at `n = 3` (`popcount = 2`), `r = 2` gives `S_2(3) = 20 ≡ 4 (mod 16)` but `≢ 4 (mod 32)`,
    and `r = 4` gives `S_4(3) = 164 ≡ 4 (mod 32)` but `≢ 4 (mod 64)`. -/
theorem sharpness_even_power_modulus :
    sumSubmasks 3 (fun k => (binomZ 3 (k : Int)) ^ 2) = 20 ∧
    (2 : Int) ^ 4 ∣ (20 - 4 : Int) ∧ ¬ ((2 : Int) ^ 5 ∣ (20 - 4 : Int)) ∧
    sumSubmasks 3 (fun k => (binomZ 3 (k : Int)) ^ 4) = 164 ∧
    (2 : Int) ^ 5 ∣ (164 - 4 : Int) ∧ ¬ ((2 : Int) ^ 6 ∣ (164 - 4 : Int)) := by
  decide

/-- Sharpness CE-3: Dropping the Lucas submask filter `k <=_2 n` (summing over all `0 <= k <= n`)
    breaks the higher-modulus congruence at `n = 2, r = 2`:
    full sum `∑_{k=0}^2 C(2,k)^2 = 6 ≢ 2 (mod 8)`. -/
theorem sharpness_dropping_lucas_mask :
    sumSubmasks 2 (fun k => (binomZ 2 (k : Int)) ^ 2) = 2 ∧
    sumRange 3 (fun k => (binomZ 2 (k : Int)) ^ 2) = 6 ∧
    ¬ ((2 : Int) ^ 3 ∣ (6 - 2 : Int)) := by
  decide

theorem sharpness_squaring_jump_needs_spike_mask :
    f_ce 0 = 1 ∧
    BitExcess 3 0 f_ce ∧
    mobius (fun k => f_ce k * f_ce k) 3 = 40 ∧
    ¬ ((2 : Int) ^ (popcount 3 + 2) ∣ mobius (fun k => f_ce k * f_ce k) 3) := by
  refine ⟨rfl, ?_, by decide, by decide⟩
  intro j hj
  have hle : j ≤ 3 := submask_le hj
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> decide

end LucasMaskEngine
