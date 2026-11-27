import StridedBitset2adicUltrametric.Defs

namespace StridedBitsetEngine
theorem sumRange_zero (f : Nat → Nat) : sumRange f 0 = 0 := rfl

theorem sumRange_succ (f : Nat → Nat) (n : Nat) :
    sumRange f (n + 1) = sumRange f n + f n := rfl

theorem sumRange_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) :
    sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumRange_add (f g : Nat → Nat) (n : Nat) :
    sumRange (fun i => f i + g i) n = sumRange f n + sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih]
    omega

theorem sumRange_mul_left (c : Nat) (f : Nat → Nat) (n : Nat) :
    sumRange (fun i => c * f i) n = c * sumRange f n := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih, Nat.mul_add]

theorem sumRange_mul_right (f : Nat → Nat) (c : Nat) (n : Nat) :
    sumRange (fun i => f i * c) n = sumRange f n * c := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih, Nat.add_mul]

theorem sumRange_swap (f : Nat → Nat → Nat) (m n : Nat) :
    sumRange (fun i => sumRange (fun j => f i j) n) m =
    sumRange (fun j => sumRange (fun i => f i j) m) n := by
  induction m with
  | zero =>
    induction n with
    | zero => rfl
    | succ n ih => rw [sumRange_zero, sumRange_succ, ← ih, sumRange_zero]; rfl
  | succ m ih =>
    rw [sumRange_succ, ih]
    rw [← sumRange_add]
    exact sumRange_congr (fun j _ => by rw [sumRange_succ])

theorem sumRange_eq_zero {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = 0) :
    sumRange f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumRange_split (f : Nat → Nat) (a b : Nat) :
    sumRange f (a + b) = sumRange f a + sumRange (fun i => f (a + i)) b := by
  induction b with
  | zero => simp [sumRange]
  | succ b ih =>
    rw [← Nat.add_assoc, sumRange_succ, sumRange_succ, ih, Nat.add_assoc]

theorem sumRange_extend {f : Nat → Nat} {a b : Nat} (hab : a ≤ b)
    (hz : ∀ i, a ≤ i → i < b → f i = 0) :
    sumRange f a = sumRange f b := by
  have hb : b = a + (b - a) := by omega
  rw [hb, sumRange_split]
  have h0 : sumRange (fun i => f (a + i)) (b - a) = 0 :=
    sumRange_eq_zero (fun i hi => hz (a + i) (by omega) (by omega))
  omega

theorem sumRange_single {f : Nat → Nat} {n k : Nat} (hk : k < n)
    (hz : ∀ i < n, i ≠ k → f i = 0) :
    sumRange f n = f k := by
  have h1 : n = k + 1 + (n - k - 1) := by omega
  rw [h1, sumRange_split, sumRange_succ]
  have hlo : sumRange f k = 0 := sumRange_eq_zero (fun i hi => hz i (by omega) (by omega))
  have hhi : sumRange (fun i => f (k + 1 + i)) (n - k - 1) = 0 :=
    sumRange_eq_zero (fun i hi => hz (k + 1 + i) (by omega) (by omega))
  omega

/-- Reindexing `sumRange` over base-`B` quotient/remainder blocks:
    `∑_{x=0}^{B*q + r} f(x) = ∑_{d=0}^{B-1} ∑_{u=0}^{q - [d > r]} f(B*u + d)`. -/
theorem sumRange_divMod_block (B : Nat) (_hB : B > 0) (f : Nat → Nat) (q r : Nat) (hr : r < B) :
    sumRange f (B * q + r + 1) =
    sumRange (fun d =>
      sumRange (fun u => f (B * u + d)) (if d ≤ r then q + 1 else q)) B := by
  induction q with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add]
    have hsplit : B = (r + 1) + (B - (r + 1)) := by omega
    have hrhs : sumRange (fun d => sumRange (fun u => f (B * u + d)) (if d ≤ r then 1 else 0)) B =
        sumRange (fun d => sumRange (fun u => f (B * u + d)) (if d ≤ r then 1 else 0)) (r + 1) +
        sumRange (fun i => sumRange (fun u => f (B * u + (r + 1 + i))) (if r + 1 + i ≤ r then 1 else 0)) (B - (r + 1)) := by
      rw [← sumRange_split, ← hsplit]
    rw [hrhs]
    have hlo : sumRange (fun d => sumRange (fun u => f (B * u + d)) (if d ≤ r then 1 else 0)) (r + 1) =
        sumRange f (r + 1) := by
      apply sumRange_congr
      intro d hd
      have hle : d ≤ r := by omega
      simp [hle, sumRange]
    have hhi : sumRange (fun i => sumRange (fun u => f (B * u + (r + 1 + i))) (if r + 1 + i ≤ r then 1 else 0)) (B - (r + 1)) = 0 := by
      apply sumRange_eq_zero
      intro i _
      have hgt : ¬(r + 1 + i ≤ r) := by omega
      simp [hgt, sumRange]
    omega
  | succ q ih =>
    have hstep : B * (q + 1) + r + 1 = (B * q + r + 1) + B := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [hstep, sumRange_split, ih]
    have htail : sumRange (fun i => f (B * q + r + 1 + i)) B =
        sumRange (fun d => f (B * (if d ≤ r then q + 1 else q) + d)) B := by
      have h1 : B = (B - (r + 1)) + (r + 1) := by omega
      have h2 : B = (r + 1) + (B - (r + 1)) := by omega
      have hl : sumRange (fun i => f (B * q + r + 1 + i)) B =
          sumRange (fun i => f (B * q + r + 1 + i)) (B - (r + 1)) +
          sumRange (fun d => f (B * q + r + 1 + (B - (r + 1) + d))) (r + 1) := by
        rw [← sumRange_split (fun i => f (B * q + r + 1 + i)), ← h1]
      have hr' : sumRange (fun d => f (B * (if d ≤ r then q + 1 else q) + d)) B =
          sumRange (fun d => f (B * (if d ≤ r then q + 1 else q) + d)) (r + 1) +
          sumRange (fun i => f (B * (if r + 1 + i ≤ r then q + 1 else q) + (r + 1 + i))) (B - (r + 1)) := by
        rw [← sumRange_split (fun d => f (B * (if d ≤ r then q + 1 else q) + d)), ← h2]
      rw [hl, hr', Nat.add_comm]
      congr 1
      · apply sumRange_congr
        intro d hd
        have hle : d ≤ r := by omega
        simp only [hle, ↓reduceIte]
        congr 1
        rw [Nat.mul_add, Nat.mul_one]; omega
      · apply sumRange_congr
        intro i _
        have hgt : ¬(r + 1 + i ≤ r) := by omega
        simp only [hgt, ↓reduceIte]
        congr 1; omega
    rw [htail, ← sumRange_add]
    apply sumRange_congr
    intro d _
    split <;> rfl

/-! ## Layer 1: Pure-Silicon 2-Adic Valuation, Popcount, Factorials, Binomials, Legendre & Odd-Parity Engine -/

theorem fact_pos : ∀ n : Nat, fact n > 0
  | 0 => by decide
  | n + 1 => Nat.mul_pos (by omega) (fact_pos n)

theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by
  cases n <;> rfl

theorem choose_eq_zero_of_lt : ∀ {n k : Nat}, n < k → choose n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    simp only [choose]
    rw [choose_eq_zero_of_lt (by omega), choose_eq_zero_of_lt (by omega)]
  | _, 0, h => by omega

theorem choose_self : ∀ n : Nat, choose n n = 1
  | 0 => rfl
  | n + 1 => by
    simp only [choose, choose_eq_zero_of_lt (by omega : n < n + 1), Nat.add_zero]
    exact choose_self n

theorem choose_pos : ∀ {n k : Nat}, k ≤ n → choose n k > 0
  | n, 0, _ => by rw [choose_zero_right]; omega
  | 0, k + 1, h => by omega
  | n + 1, k + 1, h => by
    simp only [choose]
    have h1 : choose n k > 0 := choose_pos (by omega)
    omega

theorem choose_mul_fact_mul_fact : ∀ n k : Nat, k ≤ n →
    choose n k * fact k * fact (n - k) = fact n
  | n, 0, _ => by simp [choose_zero_right, fact]
  | 0, k + 1, h => by omega
  | n + 1, k + 1, h => by
    by_cases hkn : k = n
    · subst hkn
      rw [choose_self, Nat.sub_self, fact, Nat.one_mul, Nat.mul_one]
    · have hk_le : k ≤ n := by omega
      have hk1_le : k + 1 ≤ n := by omega
      have ih1 := choose_mul_fact_mul_fact n k hk_le
      have ih2 := choose_mul_fact_mul_fact n (k + 1) hk1_le
      have hsub : n - k = (n - (k + 1)) + 1 := by omega
      have hsub2 : n + 1 - (k + 1) = n - k := by omega
      rw [hsub2, choose, Nat.add_mul, Nat.add_mul]
      -- Term 1: choose n k * fact (k+1) * fact (n - k) = (k+1) * fact n
      have t1 : choose n k * fact (k + 1) * fact (n - k) = (k + 1) * fact n := by
        calc choose n k * fact (k + 1) * fact (n - k)
            = choose n k * ((k + 1) * fact k) * fact (n - k) := rfl
          _ = (k + 1) * (choose n k * fact k * fact (n - k)) := by
              rw [Nat.mul_left_comm (choose n k), Nat.mul_assoc]
          _ = (k + 1) * fact n := by rw [ih1]
      -- Term 2: choose n (k+1) * fact (k+1) * fact (n - k) = (n - k) * fact n
      have t2 : choose n (k + 1) * fact (k + 1) * fact (n - k) = (n - k) * fact n := by
        calc choose n (k + 1) * fact (k + 1) * fact (n - k)
            = choose n (k + 1) * fact (k + 1) * ((n - k) * fact (n - (k + 1))) := by
              conv => lhs; rhs; rw [hsub, fact]
              have : n - (k + 1) + 1 = n - k := by omega
              rw [this]
          _ = (n - k) * (choose n (k + 1) * fact (k + 1) * fact (n - (k + 1))) := by
              rw [Nat.mul_left_comm (choose n (k + 1) * fact (k + 1))]
          _ = (n - k) * fact n := by rw [ih2]
      rw [t1, t2, ← Nat.add_mul]
      have hsum : k + 1 + (n - k) = n + 1 := by omega
      rw [hsum]; rfl

theorem choose_symm {n k : Nat} (hk : k ≤ n) : choose n (n - k) = choose n k := by
  have h1 := choose_mul_fact_mul_fact n k hk
  have h2 := choose_mul_fact_mul_fact n (n - k) (by omega)
  have hsub : n - (n - k) = k := by omega
  rw [hsub] at h2
  have hprod : choose n (n - k) * (fact (n - k) * fact k) = choose n k * (fact (n - k) * fact k) := by
    calc choose n (n - k) * (fact (n - k) * fact k)
        = choose n (n - k) * fact (n - k) * fact k := (Nat.mul_assoc _ _ _).symm
      _ = fact n := h2
      _ = choose n k * fact k * fact (n - k) := h1.symm
      _ = choose n k * (fact k * fact (n - k)) := Nat.mul_assoc _ _ _
      _ = choose n k * (fact (n - k) * fact k) := by rw [Nat.mul_comm (fact k)]
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (fact_pos _) (fact_pos _)) hprod

theorem choose_succ_right_eq (n k : Nat) :
    choose n (k + 1) * (k + 1) = choose n k * (n - k) := by
  by_cases hkn : k + 1 ≤ n
  · have h1 := choose_mul_fact_mul_fact n (k + 1) hkn
    have h2 := choose_mul_fact_mul_fact n k (by omega)
    have hsub : n - k = (n - (k + 1)) + 1 := by omega
    have hprod : (choose n (k + 1) * (k + 1)) * (fact k * fact (n - (k + 1))) =
                 (choose n k * (n - k)) * (fact k * fact (n - (k + 1))) := by
      have lhs_eq : (choose n (k + 1) * (k + 1)) * (fact k * fact (n - (k + 1))) = fact n := by
        calc (choose n (k + 1) * (k + 1)) * (fact k * fact (n - (k + 1)))
            = (choose n (k + 1) * (k + 1) * fact k) * fact (n - (k + 1)) := (Nat.mul_assoc _ _ _).symm
          _ = (choose n (k + 1) * ((k + 1) * fact k)) * fact (n - (k + 1)) := by
              rw [Nat.mul_assoc (choose n (k + 1))]
          _ = choose n (k + 1) * fact (k + 1) * fact (n - (k + 1)) := rfl
          _ = fact n := h1
      have rhs_eq : (choose n k * (n - k)) * (fact k * fact (n - (k + 1))) = fact n := by
        calc (choose n k * (n - k)) * (fact k * fact (n - (k + 1)))
            = choose n k * fact k * ((n - k) * fact (n - (k + 1))) := by
              rw [Nat.mul_assoc, Nat.mul_left_comm (n - k), ← Nat.mul_assoc]
          _ = choose n k * fact k * fact (n - k) := by
              congr 1
              conv => rhs; rw [hsub, fact]
              have : n - (k + 1) + 1 = n - k := by omega
              rw [this]
          _ = fact n := h2
      rw [lhs_eq, rhs_eq]
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (fact_pos _) (fact_pos _)) hprod
  · by_cases hkn' : k = n
    · subst hkn'
      rw [choose_eq_zero_of_lt (by omega : k < k + 1), Nat.sub_self, Nat.zero_mul, Nat.mul_zero]
    · rw [choose_eq_zero_of_lt (by omega : n < k + 1), choose_eq_zero_of_lt (by omega : n < k),
          Nat.zero_mul, Nat.zero_mul]

theorem v2_zero : v2 0 = 0 := by unfold v2; rfl

theorem v2_odd {n : Nat} (h : n % 2 = 1) : v2 n = 0 := by
  cases n with
  | zero => omega
  | succ k =>
    rw [v2]
    have hne : (k + 1) % 2 ≠ 0 := by omega
    simp [hne]

theorem v2_two_mul {n : Nat} (hn : n > 0) : v2 (2 * n) = 1 + v2 n := by
  cases n with
  | zero => omega
  | succ k =>
    have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h1, v2]
    have hev : ((2 * k + 1) + 1) % 2 = 0 := by omega
    have hdiv : ((2 * k + 1) + 1) / 2 = k + 1 := by omega
    simp [hev, hdiv]

theorem v2_mul_two {n : Nat} (hn : n > 0) : v2 (n * 2) = 1 + v2 n := by
  rw [Nat.mul_comm, v2_two_mul hn]

theorem v2_pow_two (k : Nat) : v2 (2 ^ k) = k := by
  induction k with
  | zero =>
    change v2 1 = 0
    exact v2_odd (by decide)
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, v2_two_mul (Nat.two_pow_pos k), ih]
    omega

theorem v2_pow_two_mul (k : Nat) {n : Nat} (hn : n > 0) : v2 (2 ^ k * n) = k + v2 n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    have hpos : 2 ^ k * n > 0 := Nat.mul_pos (Nat.two_pow_pos k) hn
    rw [h1, v2_two_mul hpos, ih]
    omega

theorem exists_odd_part : ∀ n : Nat, n > 0 → ∃ u : Nat, u % 2 = 1 ∧ n = 2 ^ v2 n * u := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hev : n % 2 = 0
    · have hhalf_pos : n / 2 > 0 := by omega
      obtain ⟨u, hu, heq⟩ := ih (n / 2) (by omega) hhalf_pos
      refine ⟨u, hu, ?_⟩
      have hn_eq : n = 2 * (n / 2) := by omega
      have hv : v2 n = 1 + v2 (n / 2) := by
        calc v2 n = v2 (2 * (n / 2)) := congrArg v2 hn_eq
          _ = 1 + v2 (n / 2) := v2_two_mul hhalf_pos
      rw [hv]
      calc n = 2 * (n / 2) := hn_eq
        _ = 2 * (2 ^ v2 (n / 2) * u) := congrArg (2 * ·) heq
        _ = (2 * 2 ^ v2 (n / 2)) * u := (Nat.mul_assoc _ _ _).symm
        _ = 2 ^ (1 + v2 (n / 2)) * u := by
            rw [Nat.pow_add, Nat.pow_one]
    · have hodd : n % 2 = 1 := by omega
      refine ⟨n, hodd, ?_⟩
      rw [v2_odd hodd, Nat.pow_zero, Nat.one_mul]

theorem v2_eq_of_odd_part {n k u : Nat} (hu : u % 2 = 1) (heq : n = 2 ^ k * u) :
    v2 n = k := by
  have hu_pos : u > 0 := by omega
  rw [heq, v2_pow_two_mul k hu_pos, v2_odd hu, Nat.add_zero]

theorem v2_mul {a b : Nat} (ha : a > 0) (hb : b > 0) : v2 (a * b) = v2 a + v2 b := by
  obtain ⟨u, hu, heqa⟩ := exists_odd_part a ha
  obtain ⟨w, hw, heqb⟩ := exists_odd_part b hb
  have huw : (u * w) % 2 = 1 := by
    rw [Nat.mul_mod, hu, hw]
  have hprod : a * b = 2 ^ (v2 a + v2 b) * (u * w) := by
    calc a * b = (2 ^ v2 a * u) * (2 ^ v2 b * w) := by rw [← heqa, ← heqb]
      _ = (2 ^ v2 a * 2 ^ v2 b) * (u * w) := by
          rw [Nat.mul_assoc, Nat.mul_left_comm u, ← Nat.mul_assoc]
      _ = 2 ^ (v2 a + v2 b) * (u * w) := by rw [← Nat.pow_add]
  exact v2_eq_of_odd_part huw hprod

theorem pow_dvd_of_le_v2 {n k : Nat} (hn : n > 0) (hle : k ≤ v2 n) : 2 ^ k ∣ n := by
  obtain ⟨u, _, heq⟩ := exists_odd_part n hn
  refine ⟨2 ^ (v2 n - k) * u, ?_⟩
  calc n = 2 ^ v2 n * u := heq
    _ = (2 ^ k * 2 ^ (v2 n - k)) * u := by
        rw [← Nat.pow_add]
        have : k + (v2 n - k) = v2 n := by omega
        rw [this]
    _ = 2 ^ k * (2 ^ (v2 n - k) * u) := Nat.mul_assoc _ _ _

theorem v2_div_pow_mod_two {n k : Nat} (hn : n > 0) (hle : k ≤ v2 n) :
    (n / 2 ^ k) % 2 = if v2 n = k then 1 else 0 := by
  obtain ⟨u, hu, heq⟩ := exists_odd_part n hn
  have hpow : 2 ^ v2 n = 2 ^ k * 2 ^ (v2 n - k) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hdiv : n / 2 ^ k = 2 ^ (v2 n - k) * u := by
    calc n / 2 ^ k = (2 ^ v2 n * u) / 2 ^ k := congrArg (· / 2 ^ k) heq
      _ = (2 ^ k * (2 ^ (v2 n - k) * u)) / 2 ^ k := by rw [hpow, Nat.mul_assoc]
      _ = 2 ^ (v2 n - k) * u := Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)
  rw [hdiv]
  by_cases hkeq : v2 n = k
  · simp [hkeq, hu]
  · have h2 : 2 ^ (v2 n - k) = 2 * 2 ^ (v2 n - k - 1) := by
      have hd : v2 n - k = (v2 n - k - 1) + 1 := by omega
      calc 2 ^ (v2 n - k) = 2 ^ ((v2 n - k - 1) + 1) := congrArg (2 ^ ·) hd
        _ = 2 ^ (v2 n - k - 1) * 2 := Nat.pow_succ _ _
        _ = 2 * 2 ^ (v2 n - k - 1) := Nat.mul_comm _ _
    simp only [hkeq, ↓reduceIte]
    rw [h2, Nat.mul_assoc]
    omega

theorem v2_lt_of_lt_pow {r k : Nat} (hr0 : 0 < r) (hr : r < 2 ^ k) : v2 r < k := by
  cases Nat.lt_or_ge (v2 r) k with
  | inl hlt => exact hlt
  | inr hle =>
    obtain ⟨q, hq⟩ := pow_dvd_of_le_v2 hr0 hle
    have hq0 : q ≥ 1 := by
      cases q with
      | zero => simp at hq; omega
      | succ _ => omega
    have : 2 ^ k * 1 ≤ 2 ^ k * q := Nat.mul_le_mul_left _ hq0
    omega

theorem v2_add_of_lt {a b : Nat} (ha : a > 0) (hb : b > 0) (hlt : v2 a < v2 b) :
    v2 (a + b) = v2 a := by
  obtain ⟨u, hu, heqa⟩ := exists_odd_part a ha
  obtain ⟨w, hw, heqb⟩ := exists_odd_part b hb
  have hpow2 : 2 ^ (v2 b - v2 a) = 2 * 2 ^ (v2 b - v2 a - 1) := by
    have hd : v2 b - v2 a = (v2 b - v2 a - 1) + 1 := by omega
    calc 2 ^ (v2 b - v2 a) = 2 ^ ((v2 b - v2 a - 1) + 1) := congrArg (2 ^ ·) hd
      _ = 2 ^ (v2 b - v2 a - 1) * 2 := Nat.pow_succ _ _
      _ = 2 * 2 ^ (v2 b - v2 a - 1) := Nat.mul_comm _ _
  have hpowb : 2 ^ v2 b = 2 ^ v2 a * 2 ^ (v2 b - v2 a) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hsum : a + b = 2 ^ v2 a * (u + 2 ^ (v2 b - v2 a) * w) := by
    calc a + b = 2 ^ v2 a * u + 2 ^ v2 b * w := by rw [← heqa, ← heqb]
      _ = 2 ^ v2 a * u + 2 ^ v2 a * (2 ^ (v2 b - v2 a) * w) := by rw [hpowb, Nat.mul_assoc]
      _ = 2 ^ v2 a * (u + 2 ^ (v2 b - v2 a) * w) := (Nat.mul_add _ _ _).symm
  have hodd : (u + 2 ^ (v2 b - v2 a) * w) % 2 = 1 := by
    rw [hpow2, Nat.mul_assoc]; omega
  exact v2_eq_of_odd_part hodd hsum

theorem v2_add_pow_mul_of_lt {k q r : Nat} (hr0 : 0 < r) (hr : r < 2 ^ k) :
    v2 (2 ^ k * q + r) = v2 r := by
  cases q with
  | zero => simp
  | succ q =>
    have hlt : v2 r < v2 (2 ^ k * (q + 1)) := by
      rw [v2_pow_two_mul k (by omega)]
      have := v2_lt_of_lt_pow hr0 hr
      omega
    rw [Nat.add_comm]
    exact v2_add_of_lt hr0 (Nat.mul_pos (Nat.two_pow_pos k) (by omega)) hlt

theorem v2_sub_pow_of_lt {k r : Nat} (hr0 : 0 < r) (hr : r < 2 ^ k) :
    v2 (2 ^ k - r) = v2 r := by
  have hlt : v2 r < k := v2_lt_of_lt_pow hr0 hr
  have hpos : 2 ^ k - r > 0 := by omega
  have hlt2 : v2 (2 ^ k - r) < k := v2_lt_of_lt_pow hpos (by omega)
  cases Nat.lt_trichotomy (v2 (2 ^ k - r)) (v2 r) with
  | inl h1 =>
    have hsum : v2 ((2 ^ k - r) + r) = v2 (2 ^ k - r) := v2_add_of_lt hpos hr0 h1
    have hcancel : (2 ^ k - r) + r = 2 ^ k := by omega
    rw [hcancel, v2_pow_two] at hsum
    omega
  | inr h2 =>
    cases h2 with
    | inl heq => exact heq
    | inr hgt =>
      have hsum : v2 (r + (2 ^ k - r)) = v2 r := v2_add_of_lt hr0 hpos hgt
      have hcancel : r + (2 ^ k - r) = 2 ^ k := by omega
      rw [hcancel, v2_pow_two] at hsum
      omega

theorem v2_add_min_le {a b : Nat} (ha : a > 0) (hb : b > 0) :
    min (v2 a) (v2 b) ≤ v2 (a + b) := by
  have hm_a : min (v2 a) (v2 b) ≤ v2 a := Nat.min_le_left _ _
  have hm_b : min (v2 a) (v2 b) ≤ v2 b := Nat.min_le_right _ _
  have hdvd : 2 ^ min (v2 a) (v2 b) ∣ a + b :=
    Nat.dvd_add (pow_dvd_of_le_v2 ha hm_a) (pow_dvd_of_le_v2 hb hm_b)
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q > 0 := by
    cases q with
    | zero => simp at hq; omega
    | succ _ => omega
  rw [hq, v2_pow_two_mul _ hq0]
  omega

/-- **Core Odd-Parity Ultrametric Sum Lemma:**
    If every nonzero term in `∑_{i < N} f i` has `v2 (f i) ≥ v`, and an ODD number of terms
    achieve `f i > 0 ∧ v2 (f i) = v`, then `∑_{i < N} f i > 0` and its `v2` is EXACTLY `v`. -/
theorem sumRange_div_pow_mod_two {N v : Nat} {f : Nat → Nat}
    (hge : ∀ i < N, f i > 0 → v ≤ v2 (f i)) :
    2 ^ v ∣ sumRange f N ∧
    (sumRange f N / 2 ^ v) % 2 =
      (sumRange (fun i => if f i > 0 ∧ v2 (f i) = v then 1 else 0) N) % 2 := by
  induction N with
  | zero =>
    simp [sumRange]
  | succ N ih =>
    obtain ⟨hdvd_prev, hmod_prev⟩ := ih (fun i hi => hge i (by omega))
    have hdvd_last : 2 ^ v ∣ f N := by
      by_cases h0 : f N = 0
      · rw [h0]; exact Nat.dvd_zero _
      · exact pow_dvd_of_le_v2 (by omega) (hge N (by omega) (by omega))
    have hdvd : 2 ^ v ∣ sumRange f (N + 1) := by
      rw [sumRange_succ]
      exact Nat.dvd_add hdvd_prev hdvd_last
    refine ⟨hdvd, ?_⟩
    rw [sumRange_succ, sumRange_succ]
    obtain ⟨a, ha⟩ := hdvd_prev
    obtain ⟨b, hb⟩ := hdvd_last
    have hdiv_sum : (sumRange f N + f N) / 2 ^ v = a + b := by
      rw [ha, hb, ← Nat.mul_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos v)]
    have hdiv_prev : sumRange f N / 2 ^ v = a := by
      rw [ha, Nat.mul_div_cancel_left _ (Nat.two_pow_pos v)]
    have hdiv_last : f N / 2 ^ v = b := by
      rw [hb, Nat.mul_div_cancel_left _ (Nat.two_pow_pos v)]
    rw [hdiv_sum]
    have hb_mod : b % 2 = (if f N > 0 ∧ v2 (f N) = v then 1 else 0) := by
      rw [← hdiv_last]
      by_cases h0 : f N = 0
      · simp [h0]
      · have hpos : f N > 0 := by omega
        have hle : v ≤ v2 (f N) := hge N (by omega) hpos
        rw [v2_div_pow_mod_two hpos hle]
        simp [hpos]
    rw [hdiv_prev] at hmod_prev
    omega

theorem v2_sumRange_odd_min {N v : Nat} {f : Nat → Nat}
    (hge : ∀ i < N, f i > 0 → v ≤ v2 (f i))
    (hodd : (sumRange (fun i => if f i > 0 ∧ v2 (f i) = v then 1 else 0) N) % 2 = 1) :
    sumRange f N > 0 ∧ v2 (sumRange f N) = v := by
  obtain ⟨⟨u, hu⟩, hmod⟩ := sumRange_div_pow_mod_two hge
  have hu_div : sumRange f N / 2 ^ v = u := by
    rw [hu, Nat.mul_div_cancel_left _ (Nat.two_pow_pos v)]
  rw [hu_div, hodd] at hmod
  have hu_pos : u > 0 := by omega
  have hsum_pos : sumRange f N > 0 := by
    rw [hu]; exact Nat.mul_pos (Nat.two_pow_pos v) hu_pos
  exact ⟨hsum_pos, v2_eq_of_odd_part hmod hu⟩

/-! ### Popcount, Legendre's Formula, and Kummer Binomial Valuations -/

theorem popcount_zero : popcount 0 = 0 := by unfold popcount; rfl

theorem popcount_one : popcount 1 = 1 := by
  rw [popcount]; simp [popcount_zero]

theorem v2_one : v2 1 = 0 := v2_odd (by decide)

theorem popcount_two_mul (n : Nat) : popcount (2 * n) = popcount n := by
  cases n with
  | zero => rfl
  | succ k =>
    have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h1, popcount]
    have hmod : ((2 * k + 1) + 1) % 2 = 0 := by omega
    have hdiv : ((2 * k + 1) + 1) / 2 = k + 1 := by omega
    simp [hmod, hdiv]

theorem popcount_two_mul_add_one (n : Nat) : popcount (2 * n + 1) = 1 + popcount n := by
  rw [popcount]
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [hmod, hdiv]

theorem popcount_succ_add_v2 : ∀ n : Nat, popcount (n + 1) + v2 (n + 1) = popcount n + 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hev : n % 2 = 0
    · have hn : n = 2 * (n / 2) := by omega
      have h1 : n + 1 = 2 * (n / 2) + 1 := by omega
      have hodd : (n + 1) % 2 = 1 := by omega
      rw [v2_odd hodd, h1, popcount_two_mul_add_one]
      have hp : popcount n = popcount (n / 2) := by
        calc popcount n = popcount (2 * (n / 2)) := congrArg popcount hn
          _ = popcount (n / 2) := popcount_two_mul _
      omega
    · have hhalf : n / 2 < n := by omega
      have hn : n = 2 * (n / 2) + 1 := by omega
      have h1 : n + 1 = 2 * (n / 2 + 1) := by omega
      have ih' := ih (n / 2) hhalf
      have hp_n : popcount n = 1 + popcount (n / 2) := by
        calc popcount n = popcount (2 * (n / 2) + 1) := congrArg popcount hn
          _ = 1 + popcount (n / 2) := popcount_two_mul_add_one _
      rw [h1, popcount_two_mul, v2_two_mul (by omega)]
      omega

theorem legendre_factorial : ∀ n : Nat, v2 (fact n) + popcount n = n := by
  intro n
  induction n with
  | zero => simp [fact, v2_one, popcount_zero]
  | succ n ih =>
    rw [fact, v2_mul (by omega) (fact_pos n)]
    have hp := popcount_succ_add_v2 n
    omega

theorem kummer_choose {n k : Nat} (hk : k ≤ n) :
    v2 (choose n k) + popcount n = popcount k + popcount (n - k) := by
  have hmul : choose n k * fact k * fact (n - k) = fact n :=
    choose_mul_fact_mul_fact n k hk
  have hc_pos : choose n k > 0 := choose_pos hk
  have hf1 : fact k > 0 := fact_pos k
  have hf2 : fact (n - k) > 0 := fact_pos (n - k)
  have hv := congrArg v2 hmul
  rw [v2_mul (Nat.mul_pos hc_pos hf1) hf2, v2_mul hc_pos hf1] at hv
  have hl1 := legendre_factorial n
  have hl2 := legendre_factorial k
  have hl3 := legendre_factorial (n - k)
  omega

theorem popcount_mul_pow_add : ∀ m q r : Nat, r < 2 ^ m →
    popcount (2 ^ m * q + r) = popcount q + popcount r := by
  intro m
  induction m with
  | zero =>
    intro q r hr
    have hr0 : r = 0 := by simp at hr; omega
    subst hr0; simp [popcount_zero]
  | succ m ih =>
    intro q r hr
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    have hr2 : r / 2 < 2 ^ m := by rw [hpow] at hr; omega
    by_cases hrem : r % 2 = 0
    · have hr_eq : r = 2 * (r / 2) := by omega
      have harg : 2 ^ (m + 1) * q + r = 2 * (2 ^ m * q + r / 2) := by
        rw [hpow, Nat.mul_assoc]; omega
      have hpr : popcount r = popcount (r / 2) := by
        calc popcount r = popcount (2 * (r / 2)) := congrArg popcount hr_eq
          _ = popcount (r / 2) := popcount_two_mul _
      rw [harg, popcount_two_mul, ih q (r / 2) hr2, hpr]
    · have hr_eq : r = 2 * (r / 2) + 1 := by omega
      have harg : 2 ^ (m + 1) * q + r = 2 * (2 ^ m * q + r / 2) + 1 := by
        rw [hpow, Nat.mul_assoc]; omega
      have hpr : popcount r = 1 + popcount (r / 2) := by
        calc popcount r = popcount (2 * (r / 2) + 1) := congrArg popcount hr_eq
          _ = 1 + popcount (r / 2) := popcount_two_mul_add_one _
      rw [harg, popcount_two_mul_add_one, ih q (r / 2) hr2, hpr]
      omega

theorem popcount_pow_add {m a : Nat} (ha : a < 2 ^ m) :
    popcount (2 ^ m + a) = 1 + popcount a := by
  have h := popcount_mul_pow_add m 1 a ha
  rw [Nat.mul_one, popcount_one] at h
  exact h

theorem popcount_pow_sub_one_sub : ∀ m x : Nat, x < 2 ^ m →
    popcount (2 ^ m - 1 - x) + popcount x = m := by
  intro m
  induction m with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by simp at hx; omega
    subst hx0; simp [popcount_zero]
  | succ m ih =>
    intro x hx
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    have hx2 : x / 2 < 2 ^ m := by rw [hpow] at hx; omega
    have hih := ih (x / 2) hx2
    by_cases hrem : x % 2 = 0
    · have hx_eq : x = 2 * (x / 2) := by omega
      have hsub : 2 ^ (m + 1) - 1 - x = 2 * (2 ^ m - 1 - x / 2) + 1 := by
        have hpos : 2 ^ m ≥ 1 := Nat.two_pow_pos m
        rw [hpow]; omega
      have hpx : popcount x = popcount (x / 2) := by
        calc popcount x = popcount (2 * (x / 2)) := congrArg popcount hx_eq
          _ = popcount (x / 2) := popcount_two_mul _
      rw [hsub, popcount_two_mul_add_one, hpx]
      omega
    · have hx_eq : x = 2 * (x / 2) + 1 := by omega
      have hsub : 2 ^ (m + 1) - 1 - x = 2 * (2 ^ m - 1 - x / 2) := by
        have hpos : 2 ^ m ≥ 1 := Nat.two_pow_pos m
        rw [hpow]; omega
      have hpx : popcount x = 1 + popcount (x / 2) := by
        calc popcount x = popcount (2 * (x / 2) + 1) := congrArg popcount hx_eq
          _ = 1 + popcount (x / 2) := popcount_two_mul_add_one _
      rw [hsub, popcount_two_mul, hpx]
      omega

/-- Exact `v2` of `C(2^m + a, r)` for `r ≤ a < 2^m`: equals `v2 C(a, r)`. -/
theorem v2_choose_pow2_add_lo {m a r : Nat} (ha : a < 2 ^ m) (hr : r ≤ a) :
    v2 (choose (2 ^ m + a) r) = v2 (choose a r) := by
  have hk1 := kummer_choose (n := 2 ^ m + a) (k := r) (by omega)
  have hk2 := kummer_choose (n := a) (k := r) hr
  have hsub : 2 ^ m + a - r = 2 ^ m + (a - r) := by omega
  rw [hsub, popcount_pow_add ha, popcount_pow_add (by omega)] at hk1
  omega

/-- Exact `v2` of `C(2^m + a, 2^m + r)` for `r ≤ a < 2^m`: equals `v2 C(a, r)`. -/
theorem v2_choose_pow2_add_hi {m a r : Nat} (ha : a < 2 ^ m) (hr : r ≤ a) :
    v2 (choose (2 ^ m + a) (2 ^ m + r)) = v2 (choose a r) := by
  have hsym : choose (2 ^ m + a) (2 ^ m + r) = choose (2 ^ m + a) (a - r) := by
    have h1 := choose_symm (n := 2 ^ m + a) (k := 2 ^ m + r) (by omega)
    have h2 : 2 ^ m + a - (2 ^ m + r) = a - r := by omega
    rw [h2] at h1
    exact h1.symm
  rw [hsym, v2_choose_pow2_add_lo ha (by omega), choose_symm hr]

/-- Exact Kummer valuation of `C(2^r, s)` for `0 < s < 2^r`: equals `r - v2 s`. -/
theorem v2_choose_pow2 {r s : Nat} (hs0 : 0 < s) (hs : s < 2 ^ r) :
    v2 (choose (2 ^ r) s) = r - v2 s := by
  have hk := kummer_choose (n := 2 ^ r) (k := s) (by omega)
  have hp_pow : popcount (2 ^ r) = 1 := by
    have h := popcount_pow_add (m := r) (a := 0) (Nat.two_pow_pos r)
    simpa [popcount_zero] using h
  have hsub : 2 ^ r - s = (2 ^ r - 1 - (s - 1)) := by omega
  have hcomp := popcount_pow_sub_one_sub r (s - 1) (by omega)
  have hstep := popcount_succ_add_v2 (s - 1)
  have hs_eq : s - 1 + 1 = s := by omega
  rw [hs_eq] at hstep
  rw [hp_pow, hsub] at hk
  have hlt : v2 s < r := v2_lt_of_lt_pow hs0 hs
  omega

/-- Exact valuation at the upper-window endpoint: `v2 C(2^m - 2, r) = v2 (r + 1)`. -/
theorem v2_choose_pow2_sub2 {m r : Nat} (hm : m ≥ 1) (hr : r ≤ 2 ^ m - 2) :
    v2 (choose (2 ^ m - 2) r) = v2 (r + 1) := by
  have hpow2 : 2 ^ m ≥ 2 := by
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    omega
  have hk := kummer_choose (n := 2 ^ m - 2) (k := r) hr
  have hp_top : popcount (2 ^ m - 2) + popcount 1 = m := by
    have h := popcount_pow_sub_one_sub m 1 (by omega)
    have h1 : 2 ^ m - 1 - 1 = 2 ^ m - 2 := by omega
    rwa [h1] at h
  have hp1 : popcount 1 = 1 := popcount_one
  have hsub : 2 ^ m - 2 - r = 2 ^ m - 1 - (r + 1) := by omega
  have hcomp := popcount_pow_sub_one_sub m (r + 1) (by omega)
  have hstep := popcount_succ_add_v2 r
  rw [hsub] at hk
  omega

/-- Exact valuation at the even-window boundary: `v2 C(2^m + 2*t, 2*t + 1) = m`. -/
theorem v2_choose_pow2_add_even_boundary {m t : Nat} (ht : 2 * t < 2 ^ m) :
    v2 (choose (2 ^ m + 2 * t) (2 * t + 1)) = m := by
  have hk := kummer_choose (n := 2 ^ m + 2 * t) (k := 2 * t + 1) (by omega)
  have hsub : 2 ^ m + 2 * t - (2 * t + 1) = 2 ^ m - 1 := by omega
  have hp_all1 : popcount (2 ^ m - 1) = m := by
    have h := popcount_pow_sub_one_sub m 0 (Nat.two_pow_pos m)
    simpa [popcount_zero] using h
  rw [hsub, hp_all1, popcount_pow_add ht, popcount_two_mul_add_one, popcount_two_mul] at hk
  omega

/-- Strict parity-alternation of `v2 C(2*M, r)` via the Pascal ratio identity. -/
theorem v2_choose_even_alt_odd {M r : Nat} (hr1 : 1 ≤ r) (hr2 : r ≤ 2 * M) (hodd : r % 2 = 1) :
    v2 (choose (2 * M) (r - 1)) < v2 (choose (2 * M) r) := by
  have hrec : choose (2 * M) r * r = choose (2 * M) (r - 1) * (2 * M - (r - 1)) := by
    have h := choose_succ_right_eq (2 * M) (r - 1)
    have hreq : r - 1 + 1 = r := by omega
    rw [hreq] at h
    exact h
  have hc1 : choose (2 * M) r > 0 := choose_pos hr2
  have hc0 : choose (2 * M) (r - 1) > 0 := choose_pos (by omega)
  have hnum_pos : 2 * M - (r - 1) > 0 := by omega
  have hv := congrArg v2 hrec
  rw [v2_mul hc1 (by omega), v2_mul hc0 hnum_pos, v2_odd hodd] at hv
  have hnum_v2 : v2 (2 * M - (r - 1)) ≥ 1 := by
    have h2 : 2 * M - (r - 1) = 2 * ((2 * M - (r - 1)) / 2) := by omega
    rw [h2, v2_two_mul (by omega)]; omega
  omega

theorem v2_choose_even_alt_even {M r : Nat} (hr1 : 1 ≤ r) (hr2 : r ≤ 2 * M) (hev : r % 2 = 0) :
    v2 (choose (2 * M) r) < v2 (choose (2 * M) (r - 1)) := by
  have hrec : choose (2 * M) r * r = choose (2 * M) (r - 1) * (2 * M - (r - 1)) := by
    have h := choose_succ_right_eq (2 * M) (r - 1)
    have hreq : r - 1 + 1 = r := by omega
    rw [hreq] at h
    exact h
  have hc1 : choose (2 * M) r > 0 := choose_pos hr2
  have hc0 : choose (2 * M) (r - 1) > 0 := choose_pos (by omega)
  have hnum_pos : 2 * M - (r - 1) > 0 := by omega
  have hv := congrArg v2 hrec
  have hnum_odd : (2 * M - (r - 1)) % 2 = 1 := by omega
  rw [v2_mul hc1 (by omega), v2_mul hc0 hnum_pos, v2_odd hnum_odd] at hv
  have hr_v2 : v2 r ≥ 1 := by
    have h2 : r = 2 * (r / 2) := by omega
    rw [h2, v2_two_mul (by omega)]; omega
  omega

/-! ## Layer 2: Periodic Bitmask-Support Sets & Combinatorial Bit-Slice Carry-Convolution Bridge -/

theorem inStrided_iff_mod_zero {m x : Nat} (_hm : m ≥ 1) :
    InStrided m x ↔ ∀ i : Nat, x.testBit i = true → i % m = 0 := by
  constructor
  · intro h i hi
    have h1 := h i hi
    cases hmod : i % m with
    | zero => rfl
    | succ k =>
      rw [hmod] at h1
      have hfalse : (1 : Nat).testBit (k + 1) = false := by
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have h2 : 2 ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hdiv : 1 / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
        simp [hdiv]
      rw [hfalse] at h1
      contradiction
  · intro h i hi
    rw [h i hi]
    decide

theorem inMaskFuel_indep : ∀ fuel1 fuel2 m mask x : Nat,
    m ≥ 1 → x ≤ fuel1 → x ≤ fuel2 →
    inMaskFuel fuel1 m mask x = inMaskFuel fuel2 m mask x := by
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 m mask x hm hx1 _
    have hx0 : x = 0 := by omega
    subst hx0
    have hm0 : (m == 0) = false := by
      cases m with
      | zero => omega
      | succ _ => rfl
    cases fuel2 with
    | zero => rfl
    | succ f2 =>
      unfold inMaskFuel
      simp [hm0, show m ≠ 0 by omega]
  | succ f1 ih =>
    intro fuel2 m mask x hm hx1 hx2
    cases fuel2 with
    | zero =>
      have hx0 : x = 0 := by omega
      subst hx0
      have hm0 : (m == 0) = false := by
        cases m with
        | zero => omega
        | succ _ => rfl
      unfold inMaskFuel
      simp [hm0, show m ≠ 0 by omega]
    | succ f2 =>
      have hm0 : (m == 0) = false := by
        cases m with
        | zero => omega
        | succ _ => rfl
      unfold inMaskFuel
      simp only [hm0, Bool.false_eq_true, ↓reduceIte]
      by_cases hx0 : x = 0
      · subst hx0; simp
      · have hxb : (x == 0) = false := by
          cases x with
          | zero => contradiction
          | succ _ => rfl
        simp only [hxb, Bool.false_eq_true, ↓reduceIte]
        have hpow : 2 ^ m ≥ 2 := by
          have := Nat.pow_le_pow_right (n := 2) (by omega) hm
          omega
        have hlt : x / 2 ^ m < x := Nat.div_lt_self (by omega) hpow
        congr 1
        exact ih f2 m mask (x / 2 ^ m) hm (by omega) (by omega)

theorem inDigitMaskB_iff {m mask d : Nat} (hd : d < 2 ^ m) :
    inDigitMaskB m mask d = true ↔ ∀ j < m, d.testBit j = true → mask.testBit j = true := by
  unfold inDigitMaskB
  simp only [hd, decide_true, Bool.true_and, beq_iff_eq]
  constructor
  · intro hand j _ hj
    have htb := congrArg (fun z => z.testBit j) hand
    rw [Nat.testBit_and] at htb
    rw [hj] at htb
    simpa using htb
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    by_cases hjm : j < m
    · cases hdj : d.testBit j with
      | false => simp
      | true => simp [hall j hjm hdj]
    · have hdj : d.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hd (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hdj]

theorem inMaskB_slice {m mask q d : Nat} (hm : m ≥ 1) (hd : d < 2 ^ m) :
    inMaskB m mask (2 ^ m * q + d) = (inDigitMaskB m mask d && inMaskB m mask q) := by
  have hm0 : (m == 0) = false := by
    cases m with
    | zero => omega
    | succ _ => rfl
  by_cases hqd : 2 ^ m * q + d = 0
  · have hq0 : q = 0 := by
      have hp := Nat.two_pow_pos m
      cases q with
      | zero => rfl
      | succ _ => rw [Nat.mul_add, Nat.mul_one] at hqd; omega
    have hd0 : d = 0 := by omega
    subst hq0; subst hd0
    unfold inMaskB inMaskFuel
    simp [show m ≠ 0 by omega, inDigitMaskB, Nat.two_pow_pos m]
  · have hpos : 2 ^ m * q + d ≥ 1 := by omega
    have hunf : inMaskB m mask (2 ^ m * q + d) =
        (inDigitMaskB m mask ((2 ^ m * q + d) % 2 ^ m) &&
         inMaskFuel (2 ^ m * q + d - 1) m mask ((2 ^ m * q + d) / 2 ^ m)) := by
      unfold inMaskB
      have hsucc : 2 ^ m * q + d = (2 ^ m * q + d - 1) + 1 := by omega
      conv => lhs; arg 1; rw [hsucc]
      conv => lhs; unfold inMaskFuel
      have hne : ((2 ^ m * q + d) == 0) = false := by
        cases h : 2 ^ m * q + d with
        | zero => contradiction
        | succ _ => rfl
      simp only [hm0, hne, Bool.false_eq_true, ↓reduceIte]
    rw [hunf]
    have hmod : (2 ^ m * q + d) % 2 ^ m = d := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hd]
    have hdiv : (2 ^ m * q + d) / 2 ^ m = q := by
      rw [Nat.mul_add_div (Nat.two_pow_pos m), Nat.div_eq_of_lt hd, Nat.add_zero]
    rw [hmod, hdiv]
    have hpow2 : 2 ^ m ≥ 2 := by
      have := Nat.pow_le_pow_right (n := 2) (by omega) hm
      omega
    have hq_le : q ≤ 2 ^ m * q + d - 1 := by
      have : 2 * q ≤ 2 ^ m * q := Nat.mul_le_mul_right q hpow2
      omega
    congr 1
    exact inMaskFuel_indep (2 ^ m * q + d - 1) q m mask q hm hq_le (Nat.le_refl q)

theorem inMaskB_iff {m mask x : Nat} (hm : m ≥ 1) :
    inMaskB m mask x = true ↔ InMask m mask x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases hx : x = 0
    · subst hx
      constructor
      · intro _ i hi
        simp at hi
      · intro _
        unfold inMaskB inMaskFuel
        simp [show m ≠ 0 by omega]
    · have hpow : 2 ^ m ≥ 2 := by
        have h1 : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
        omega
      have hlt : x / 2 ^ m < x := Nat.div_lt_self (by omega) hpow
      have hdecomp : x = 2 ^ m * (x / 2 ^ m) + x % 2 ^ m := (Nat.div_add_mod x (2 ^ m)).symm
      have hrem_lt : x % 2 ^ m < 2 ^ m := Nat.mod_lt x (Nat.two_pow_pos m)
      have hslice : inMaskB m mask x = (inDigitMaskB m mask (x % 2 ^ m) && inMaskB m mask (x / 2 ^ m)) := by
        calc inMaskB m mask x
            = inMaskB m mask (2 ^ m * (x / 2 ^ m) + x % 2 ^ m) := congrArg (inMaskB m mask) hdecomp
          _ = (inDigitMaskB m mask (x % 2 ^ m) && inMaskB m mask (x / 2 ^ m)) := inMaskB_slice hm hrem_lt
      rw [hslice, Bool.and_eq_true, inDigitMaskB_iff hrem_lt, ih (x / 2 ^ m) hlt]
      constructor
      · rintro ⟨hlo, hhi⟩ i hi
        by_cases him : i < m
        · have hmod : i % m = i := Nat.mod_eq_of_lt him
          rw [hmod]
          apply hlo i him
          rw [Nat.testBit_mod_two_pow]
          simp [him, hi]
        · have hsub : i = (i - m) + m := by omega
          have hmod : i % m = (i - m) % m := by
            calc i % m = ((i - m) + m) % m := congrArg (· % m) hsub
              _ = (i - m) % m := Nat.add_mod_right _ _
          rw [hmod]
          apply hhi (i - m)
          rw [Nat.testBit_div_two_pow]
          have : i - m + m = i := by omega
          rwa [this]
      · intro hall
        refine ⟨?_, ?_⟩
        · intro j hjm hdj
          rw [Nat.testBit_mod_two_pow] at hdj
          simp only [hjm, decide_true, Bool.true_and] at hdj
          have := hall j hdj
          rwa [Nat.mod_eq_of_lt hjm] at this
        · intro j hj
          rw [Nat.testBit_div_two_pow] at hj
          have := hall (j + m) hj
          rwa [Nat.add_mod_right] at this

theorem inDigitMaskB_one_iff {m d : Nat} (hd : d < 2 ^ m) :
    inDigitMaskB m 1 d = true ↔ (d = 0 ∨ d = 1) := by
  unfold inDigitMaskB
  simp only [hd, decide_true, Bool.true_and, beq_iff_eq]
  have h1 : d &&& 1 = d % 2 := Nat.and_one_is_mod d
  rw [h1]
  omega

theorem maskRepCount_zero (m : Nat) (hm : m ≥ 1) (masks : List Nat) :
    maskRepCount m masks 0 = 1 := by
  induction masks with
  | nil => rfl
  | cons mask rest ih =>
    simp only [maskRepCount, sumRange, Nat.zero_add, Nat.sub_zero]
    have h0 : inMaskB m mask 0 = true := by
      unfold inMaskB inMaskFuel
      simp [show m ≠ 0 by omega]
    simp [h0, ih]

theorem stridedRepCount_zero (m k : Nat) (hm : m ≥ 1) : stridedRepCount m k 0 = 1 :=
  maskRepCount_zero m hm (List.replicate k 1)

theorem digitWeight_strided (m : Nat) (hm : m ≥ 1) :
    ∀ k s : Nat, digitWeight m (List.replicate k 1) s = choose k s := by
  intro k
  induction k with
  | zero =>
    intro s
    cases s with
    | zero => rfl
    | succ s => rfl
  | succ k ih =>
    intro s
    simp only [List.replicate_succ, digitWeight]
    have hpow2 : 2 ^ m ≥ 2 := by
      have h1 : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
      omega
    have hsplit : 2 ^ m = 2 + (2 ^ m - 2) := by omega
    have hsr : sumRange (fun d => if d ≤ s ∧ inDigitMaskB m 1 d then digitWeight m (List.replicate k 1) (s - d) else 0) (2 ^ m) =
        sumRange (fun d => if d ≤ s ∧ inDigitMaskB m 1 d then digitWeight m (List.replicate k 1) (s - d) else 0) 2 +
        sumRange (fun i => if 2 + i ≤ s ∧ inDigitMaskB m 1 (2 + i) then digitWeight m (List.replicate k 1) (s - (2 + i)) else 0) (2 ^ m - 2) := by
      rw [← sumRange_split, ← hsplit]
    rw [hsr]
    have hhi : sumRange (fun i =>
        if 2 + i ≤ s ∧ inDigitMaskB m 1 (2 + i) then digitWeight m (List.replicate k 1) (s - (2 + i)) else 0)
        (2 ^ m - 2) = 0 := by
      apply sumRange_eq_zero
      intro i hi
      have hfalse : ¬(inDigitMaskB m 1 (2 + i) = true) := by
        rw [inDigitMaskB_one_iff (by omega)]
        omega
      simp [hfalse]
    rw [hhi, Nat.add_zero]
    simp only [sumRange, Nat.zero_add]
    have h0 : inDigitMaskB m 1 0 = true := (inDigitMaskB_one_iff (by omega)).2 (Or.inl rfl)
    have h1 : inDigitMaskB m 1 1 = true := (inDigitMaskB_one_iff (by omega)).2 (Or.inr rfl)
    cases s with
    | zero =>
      simp [h0, ih 0, choose_zero_right]
    | succ s =>
      simp [h0, h1, ih (s + 1), ih s, choose]
      omega

theorem digitWeight_eq_zero_of_gt (m : Nat) :
    ∀ (masks : List Nat) (s : Nat), s > masks.length * (2 ^ m - 1) →
      digitWeight m masks s = 0 := by
  intro masks
  induction masks with
  | nil =>
    intro s hs
    simp only [List.length_nil, Nat.zero_mul] at hs
    simp only [digitWeight]
    have : s ≠ 0 := by omega
    simp [this]
  | cons mask rest ih =>
    intro s hs
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hs
    simp only [digitWeight]
    apply sumRange_eq_zero
    intro d hd
    by_cases hcond : d ≤ s ∧ inDigitMaskB m mask d = true
    · simp only [hcond, and_self, ↓reduceIte]
      exact ih (s - d) (by omega)
    · simp [hcond]

/-- **Master Bit-Slice Carry-Convolution Bridge:**
    Lifts the combinatorial tuple count `maskRepCount m masks n` directly from the binary-support
    predicate `InMask` to the exact base-`2^m` carry-convolution recurrence! -/
theorem maskRepCount_slice (m : Nat) (hm : m ≥ 1) :
    ∀ (masks : List Nat) (q r : Nat), r < 2 ^ m →
      maskRepCount m masks (2 ^ m * q + r) =
      sumRange (fun c =>
        digitWeight m masks (c * 2 ^ m + r) * maskRepCount m masks (q - c)) (q + 1) := by
  intro masks
  induction masks with
  | nil =>
    intro q r hr
    simp only [maskRepCount, digitWeight]
    by_cases hqr : 2 ^ m * q + r = 0
    · have hq0 : q = 0 := by
        cases q with
        | zero => rfl
        | succ _ =>
          have := Nat.two_pow_pos m
          rw [Nat.mul_add, Nat.mul_one] at hqr; omega
      have hr0 : r = 0 := by omega
      subst hq0; subst hr0
      simp [sumRange]
    · simp only [hqr, ↓reduceIte]
      symm
      apply sumRange_eq_zero
      intro c _
      by_cases hc0 : c * 2 ^ m + r = 0
      · have hc_eq : c = 0 := by
          cases c with
          | zero => rfl
          | succ _ =>
            have := Nat.two_pow_pos m
            rw [Nat.add_mul, Nat.one_mul] at hc0; omega
        have hr0 : r = 0 := by omega
        subst hc_eq; subst hr0
        have hqne : q ≠ 0 := by
          intro hq0; subst hq0; simp at hqr
        simp [hqne]
      · have hne' : ¬(c * 2 ^ m = 0 ∧ r = 0) := by omega
        simp [hne']
  | cons mask rest ih =>
    intro q r hr
    have hB_pos : 2 ^ m > 0 := Nat.two_pow_pos m
    change sumRange (fun x => if inMaskB m mask x then maskRepCount m rest (2 ^ m * q + r - x) else 0) (2 ^ m * q + r + 1) = _
    rw [sumRange_divMod_block (2 ^ m) hB_pos _ q r hr]
    have hinner : ∀ d < 2 ^ m,
        sumRange (fun u =>
          if inMaskB m mask (2 ^ m * u + d) then maskRepCount m rest (2 ^ m * q + r - (2 ^ m * u + d)) else 0)
          (if d ≤ r then q + 1 else q) =
        sumRange (fun c =>
          (if d ≤ c * 2 ^ m + r ∧ inDigitMaskB m mask d then digitWeight m rest (c * 2 ^ m + r - d) else 0) *
          maskRepCount m (mask :: rest) (q - c)) (q + 1) := by
      intro d hd
      by_cases hmask : inDigitMaskB m mask d = true
      · by_cases hdr : d ≤ r
        · simp only [hdr, ↓reduceIte]
          have hstep1 : sumRange (fun u =>
              if inMaskB m mask (2 ^ m * u + d) then maskRepCount m rest (2 ^ m * q + r - (2 ^ m * u + d)) else 0) (q + 1) =
            sumRange (fun u =>
              sumRange (fun c =>
                (if inMaskB m mask u ∧ c ≤ q - u then
                  digitWeight m rest (c * 2 ^ m + (r - d)) * maskRepCount m rest (q - u - c)
                else 0)) (q + 1)) (q + 1) := by
            apply sumRange_congr
            intro u hu
            rw [inMaskB_slice hm hd, hmask, Bool.true_and]
            have hsub : 2 ^ m * q + r - (2 ^ m * u + d) = 2 ^ m * (q - u) + (r - d) := by
              have hle : 2 ^ m * u ≤ 2 ^ m * q := Nat.mul_le_mul_left (2 ^ m) (by omega)
              rw [Nat.mul_sub_left_distrib]; omega
            by_cases hmu : inMaskB m mask u = true
            · simp only [hmu, ↓reduceIte, true_and]
              rw [hsub, ih (q - u) (r - d) (by omega)]
              symm
              rw [← sumRange_extend (a := q - u + 1) (b := q + 1) (by omega)]
              · exact sumRange_congr (fun c hc => by
                  have hcle : c ≤ q - u := by omega
                  simp [hcle])
              · intro c hc1 _
                have hnot : ¬(c ≤ q - u) := by omega
                simp [hnot]
            · simp only [hmu, Bool.false_eq_true, ↓reduceIte, false_and]
              symm; exact sumRange_eq_zero (fun _ _ => rfl)
          rw [hstep1, sumRange_swap]
          apply sumRange_congr
          intro c hc
          have hle_d : d ≤ c * 2 ^ m + r := by omega
          simp only [hle_d, hmask, and_self, ↓reduceIte]
          have hsub_c : c * 2 ^ m + r - d = c * 2 ^ m + (r - d) := by omega
          rw [hsub_c]
          change sumRange (fun u =>
            if inMaskB m mask u = true ∧ c ≤ q - u then
              digitWeight m rest (c * 2 ^ m + (r - d)) * maskRepCount m rest (q - u - c)
            else 0) (q + 1) =
            digitWeight m rest (c * 2 ^ m + (r - d)) *
            sumRange (fun u => if inMaskB m mask u then maskRepCount m rest (q - c - u) else 0) (q - c + 1)
          rw [← sumRange_mul_left]
          rw [← sumRange_extend (a := q - c + 1) (b := q + 1) (by omega)]
          · apply sumRange_congr
            intro u hu
            have hcle : c ≤ q - u := by omega
            have hsub_eq : q - u - c = q - c - u := by omega
            by_cases hmu : inMaskB m mask u = true
            · simp [hmu, hcle, hsub_eq]
            · simp [hmu]
          · intro u hu1 _
            have hnot : ¬(c ≤ q - u) := by omega
            simp [hnot]
        · simp only [hdr, ↓reduceIte]
          have hstep1 : sumRange (fun u =>
              if inMaskB m mask (2 ^ m * u + d) then maskRepCount m rest (2 ^ m * q + r - (2 ^ m * u + d)) else 0) q =
            sumRange (fun u =>
              sumRange (fun c =>
                (if inMaskB m mask u ∧ 1 ≤ c ∧ c ≤ q - u then
                  digitWeight m rest ((c - 1) * 2 ^ m + (2 ^ m + r - d)) * maskRepCount m rest (q - u - c)
                else 0)) (q + 1)) q := by
            apply sumRange_congr
            intro u hu
            rw [inMaskB_slice hm hd, hmask, Bool.true_and]
            have hsub : 2 ^ m * q + r - (2 ^ m * u + d) = 2 ^ m * (q - 1 - u) + (2 ^ m + r - d) := by
              have hq1 : q = (q - 1 - u) + u + 1 := by omega
              have hmul : 2 ^ m * q = 2 ^ m * (q - 1 - u) + 2 ^ m * u + 2 ^ m := by
                calc 2 ^ m * q = 2 ^ m * ((q - 1 - u) + u + 1) := congrArg (2 ^ m * ·) hq1
                  _ = 2 ^ m * (q - 1 - u) + 2 ^ m * u + 2 ^ m := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
              omega
            by_cases hmu : inMaskB m mask u = true
            · simp only [hmu, ↓reduceIte, true_and]
              rw [hsub, ih (q - 1 - u) (2 ^ m + r - d) (by omega)]
              have hshift : sumRange (fun c =>
                  if 1 ≤ c ∧ c ≤ q - u then
                    digitWeight m rest ((c - 1) * 2 ^ m + (2 ^ m + r - d)) * maskRepCount m rest (q - u - c)
                  else 0) (q + 1) =
                sumRange (fun c' =>
                  if c' ≤ q - 1 - u then
                    digitWeight m rest (c' * 2 ^ m + (2 ^ m + r - d)) * maskRepCount m rest (q - 1 - u - c')
                  else 0) q := by
                have h1 : q + 1 = 1 + q := by omega
                rw [h1, sumRange_split]
                have hz0 : sumRange (fun c =>
                    if 1 ≤ c ∧ c ≤ q - u then
                      digitWeight m rest ((c - 1) * 2 ^ m + (2 ^ m + r - d)) * maskRepCount m rest (q - u - c)
                    else 0) 1 = 0 := by simp [sumRange]
                rw [hz0, Nat.zero_add]
                apply sumRange_congr
                intro c' _
                have hge1 : 1 ≤ 1 + c' := by omega
                have hsub1 : 1 + c' - 1 = c' := by omega
                have hiff : (1 + c' ≤ q - u) ↔ (c' ≤ q - 1 - u) := by omega
                have hsub2 : q - u - (1 + c') = q - 1 - u - c' := by omega
                by_cases hle : c' ≤ q - 1 - u
                · have hle' : 1 + c' ≤ q - u := hiff.2 hle
                  simp [hge1, hle, hle', hsub1, hsub2]
                · have hle' : ¬(1 + c' ≤ q - u) := fun h => hle (hiff.1 h)
                  simp [hge1, hle, hle']
              rw [hshift]
              symm
              rw [← sumRange_extend (a := q - 1 - u + 1) (b := q) (by omega)]
              · exact sumRange_congr (fun c' hc' => by
                  have hcle : c' ≤ q - 1 - u := by omega
                  simp [hcle])
              · intro c' hc1 _
                have hnot : ¬(c' ≤ q - 1 - u) := by omega
                simp [hnot]
            · simp only [hmu, Bool.false_eq_true, ↓reduceIte, false_and]
              symm; exact sumRange_eq_zero (fun _ _ => rfl)
          rw [hstep1, sumRange_swap]
          apply sumRange_congr
          intro c hc
          cases c with
          | zero =>
            have hl0 : sumRange (fun u =>
                if inMaskB m mask u = true ∧ 1 ≤ 0 ∧ 0 ≤ q - u then
                  digitWeight m rest ((0 - 1) * 2 ^ m + (2 ^ m + r - d)) * maskRepCount m rest (q - u - 0)
                else 0) q = 0 := sumRange_eq_zero (fun _ _ => by simp)
            rw [hl0]
            simp [hdr]
          | succ c' =>
            have hle_d : d ≤ (c' + 1) * 2 ^ m + r := by
              rw [Nat.add_mul, Nat.one_mul]; omega
            have hsub_c : (c' + 1) * 2 ^ m + r - d = c' * 2 ^ m + (2 ^ m + r - d) := by
              rw [Nat.add_mul, Nat.one_mul]; omega
            simp only [hle_d, hmask, and_self, ↓reduceIte, hsub_c]
            change sumRange (fun u =>
              if inMaskB m mask u = true ∧ 1 ≤ c' + 1 ∧ c' + 1 ≤ q - u then
                digitWeight m rest (c' * 2 ^ m + (2 ^ m + r - d)) * maskRepCount m rest (q - u - (c' + 1))
              else 0) q =
              digitWeight m rest (c' * 2 ^ m + (2 ^ m + r - d)) *
              sumRange (fun u => if inMaskB m mask u then maskRepCount m rest (q - (c' + 1) - u) else 0)
                (q - (c' + 1) + 1)
            rw [← sumRange_mul_left]
            rw [← sumRange_extend (a := q - (c' + 1) + 1) (b := q) (by omega)]
            · apply sumRange_congr
              intro u hu
              have hcle : 1 ≤ c' + 1 ∧ c' + 1 ≤ q - u := by omega
              have hsub_eq : q - u - (c' + 1) = q - (c' + 1) - u := by omega
              by_cases hmu : inMaskB m mask u = true
              · simp [hmu, hcle, hsub_eq]
              · simp [hmu]
            · intro u hu1 _
              have hnot : ¬(c' + 1 ≤ q - u) := by omega
              simp [hnot]
      · have hl : sumRange (fun u =>
            if inMaskB m mask (2 ^ m * u + d) then maskRepCount m rest (2 ^ m * q + r - (2 ^ m * u + d)) else 0)
            (if d ≤ r then q + 1 else q) = 0 := by
          apply sumRange_eq_zero
          intro u _
          rw [inMaskB_slice hm hd]
          have hfalse : inDigitMaskB m mask d = false := by
            cases h : inDigitMaskB m mask d <;> simp_all
          simp [hfalse]
        have hr0 : sumRange (fun c =>
            (if d ≤ c * 2 ^ m + r ∧ inDigitMaskB m mask d then digitWeight m rest (c * 2 ^ m + r - d) else 0) *
            maskRepCount m (mask :: rest) (q - c)) (q + 1) = 0 := by
          apply sumRange_eq_zero
          intro c _
          simp [hmask]
        rw [hl, hr0]
    rw [sumRange_congr hinner, sumRange_swap]
    apply sumRange_congr
    intro c _
    rw [sumRange_mul_right]
    rfl

/-- Exact base-`2^m` binomial carry-convolution recurrence for `stridedRepCount m k`. -/
theorem stridedRepCount_slice (m k : Nat) (hm : m ≥ 1) (q r : Nat) (hr : r < 2 ^ m) :
    stridedRepCount m k (2 ^ m * q + r) =
    sumRange (fun c => choose k (c * 2 ^ m + r) * stridedRepCount m k (q - c)) (q + 1) := by
  unfold stridedRepCount
  rw [maskRepCount_slice m hm (List.replicate k 1) q r hr]
  apply sumRange_congr
  intro c _
  rw [digitWeight_strided m hm k (c * 2 ^ m + r)]

/-! ## Layer 3: Reusable Infinite Proof Engine #1 — 2-Adic Odd-Parity Ultrametric Dominance Engine -/

/-- **General Odd-Parity Ultrametric Dominance Engine (`ultrametric_odd_parity_lift`):**
    For ANY base `B ≥ 2`, ANY carry-convolution recurrence
    `f (B * q + r) = ∑_{c ≤ q} w c r * f (q - c)` with `f 0 = 1`, and ANY candidate
    valuation functional `V : Nat → Nat` with `V 0 = 0`:
    if at every `n = B * q + r > 0`, every active term `w c r > 0` satisfies
    `v2 (w c r) + V (q - c) ≥ V (B * q + r)` AND an **ODD** number of active terms achieve
    equality, then `∀ n : Nat, f n > 0 ∧ v2 (f n) = V n`. -/
theorem ultrametric_odd_parity_lift
    (B : Nat) (hB : B ≥ 2)
    (w : Nat → Nat → Nat)
    (f V : Nat → Nat)
    (hf0 : f 0 = 1) (hV0 : V 0 = 0)
    (hrec : ∀ q r : Nat, r < B →
      f (B * q + r) = sumRange (fun c => w c r * f (q - c)) (q + 1))
    (hge : ∀ q r : Nat, r < B → B * q + r > 0 →
      ∀ c ≤ q, w c r > 0 → V (B * q + r) ≤ v2 (w c r) + V (q - c))
    (hodd : ∀ q r : Nat, r < B → B * q + r > 0 →
      (sumRange (fun c =>
        if w c r > 0 ∧ v2 (w c r) + V (q - c) = V (B * q + r) then 1 else 0) (q + 1)) % 2 = 1) :
    ∀ n : Nat, f n > 0 ∧ v2 (f n) = V n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      rw [hf0, hV0]
      exact ⟨by omega, v2_one⟩
    · have hn_pos : n > 0 := by omega
      let q := n / B
      let r := n % B
      have hr : r < B := Nat.mod_lt n (by omega)
      have hdecomp : B * q + r = n := Nat.div_add_mod n B
      have hq_lt : q < n := Nat.div_lt_self hn_pos hB
      have hih : ∀ c ≤ q, f (q - c) > 0 ∧ v2 (f (q - c)) = V (q - c) := by
        intro c hc
        exact ih (q - c) (by omega)
      rw [← hdecomp, hrec q r hr]
      have hqr_pos : B * q + r > 0 := by omega
      apply v2_sumRange_odd_min (v := V (B * q + r))
      · intro c hc hpos
        have hcle : c ≤ q := by omega
        have ⟨hf_pos, hf_v2⟩ := hih c hcle
        have hw_pos : w c r > 0 := by
          cases hw : w c r with
          | zero => rw [hw, Nat.zero_mul] at hpos; omega
          | succ _ => omega
        rw [v2_mul hw_pos hf_pos, hf_v2]
        exact hge q r hr hqr_pos c hcle hw_pos
      · have hcongr :
            sumRange (fun c => if w c r * f (q - c) > 0 ∧ v2 (w c r * f (q - c)) = V (B * q + r) then 1 else 0) (q + 1) =
            sumRange (fun c => if w c r > 0 ∧ v2 (w c r) + V (q - c) = V (B * q + r) then 1 else 0) (q + 1) := by
          apply sumRange_congr
          intro c hc
          have hcle : c ≤ q := by omega
          have ⟨hf_pos, hf_v2⟩ := hih c hcle
          by_cases hw : w c r > 0
          · have hprod_pos : w c r * f (q - c) > 0 := Nat.mul_pos hw hf_pos
            rw [v2_mul hw hf_pos, hf_v2]
            simp [hw, hprod_pos]
          · have hw0 : w c r = 0 := by omega
            simp [hw0]
        rw [hcongr]
        exact hodd q r hr hqr_pos

/-! ## Layer 4: Reusable Infinite Proof Engine #2 — Finite-Certificate `decide`-Verified Unit-Carry Compiler -/

theorem v2Fuel_eq_v2 : ∀ fuel n : Nat, n ≤ fuel → v2Fuel fuel n = v2 n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by omega
    subst hn0; simp [v2Fuel, v2_zero]
  | succ fuel ih =>
    intro n hn
    unfold v2Fuel
    by_cases hn0 : n = 0
    · subst hn0; simp [v2_zero]
    · simp only [hn0, ↓reduceIte]
      by_cases hev : n % 2 = 0
      · simp only [hev, ↓reduceIte]
        have hhalf_le : n / 2 ≤ fuel := by omega
        rw [ih (n / 2) hhalf_le]
        have hn_eq : n = 2 * (n / 2) := by omega
        have hpos : n / 2 > 0 := by omega
        calc 1 + v2 (n / 2) = v2 (2 * (n / 2)) := (v2_two_mul hpos).symm
          _ = v2 n := congrArg v2 hn_eq.symm
      · simp only [hev, ↓reduceIte]
        exact (v2_odd (by omega)).symm

theorem v2Exec_eq_v2 (n : Nat) : v2Exec n = v2 n :=
  v2Fuel_eq_v2 n n (Nat.le_refl n)

theorem allBelow_iff (p : Nat → Bool) : ∀ N : Nat, allBelow p N = true ↔ ∀ i < N, p i = true := by
  intro N
  induction N with
  | zero =>
    simp [allBelow]
  | succ N ih =>
    simp only [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases heq : i = N
      · subst heq; exact h2
      · exact h1 i (by omega)
    · intro hall
      exact ⟨fun i hi => hall i (by omega), hall N (by omega)⟩

theorem checkUnitCarryCert_sound {B : Nat} {w0 w1 : Nat → Nat}
    (hcert : checkUnitCarryCert B w0 w1 = true) : UnitCarrySpec B w0 w1 := by
  unfold checkUnitCarryCert at hcert
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, allBelow_iff,
             v2Exec_eq_v2] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨⟨⟨⟨hB2, hBeven⟩, hw0⟩, hw10⟩, hw1last⟩, hcarry⟩, hwrap⟩, hnext⟩, hprev⟩
  refine ⟨hB2, hBeven, hw0, hw10, hw1last, ?_, hwrap, ?_, ?_⟩
  · intro r hr hw1r
    rcases hcarry r hr with h0 | heq
    · omega
    · exact heq
  · intro r hr hev
    have h := hnext r hr
    simp only [hev, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact h
  · intro r hr hev hge2
    have h := hprev r hr
    simp only [hev, hge2, and_self, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true,
               beq_iff_eq, decide_eq_true_eq] at h
    exact h

theorem certVal_zero (B : Nat) (w0 w1 : Nat → Nat) : certVal B w0 w1 0 = 0 := by
  unfold certVal; rfl

theorem certVal_step {B : Nat} (hB : B ≥ 2) (w0 w1 : Nat → Nat) {q r : Nat}
    (hr : r < B) (hpos : B * q + r > 0) :
    certVal B w0 w1 (B * q + r) =
    v2 (w0 r) + certVal B w0 w1 (if w1 r > 0 then 2 * (q / 2) else q) := by
  cases h : B * q + r with
  | zero => omega
  | succ k =>
    conv => lhs; unfold certVal
    simp only [hB, ↓reduceDIte]
    have hdiv : (k + 1) / B = q := by
      rw [← h, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]
    have hmod : (k + 1) % B = r := by
      rw [← h, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    rw [hdiv, hmod]
    split <;> rfl

/-- **Core Local-Minimum Invariant:** Under `UnitCarrySpec B w0 w1`, every even index `2*j`
    is a strict local minimum of `certVal B w0 w1`. -/
theorem unitCarrySpec_even_min {B : Nat} {w0 w1 : Nat → Nat} (hs : UnitCarrySpec B w0 w1) :
    ∀ n : Nat,
      (n % 2 = 0 → certVal B w0 w1 n < certVal B w0 w1 (n + 1)) ∧
      (n % 2 = 0 → n ≥ 2 → certVal B w0 w1 n < certVal B w0 w1 (n - 1)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hq_le : ∀ m < n, certVal B w0 w1 (2 * (m / 2)) ≤ certVal B w0 w1 m := by
      intro m hm
      by_cases hev : m % 2 = 0
      · have : 2 * (m / 2) = m := by omega
        rw [this]; exact Nat.le_refl _
      · have hlt_m : 2 * (m / 2) < n := by omega
        have hev' : (2 * (m / 2)) % 2 = 0 := by omega
        have hsucc : 2 * (m / 2) + 1 = m := by omega
        have hlt := (ih (2 * (m / 2)) hlt_m).1 hev'
        rw [hsucc] at hlt
        omega
    have hq_pred_le : ∀ m, 1 ≤ m → m < n → certVal B w0 w1 (2 * (m / 2)) ≤ certVal B w0 w1 (m - 1) := by
      intro m hm1 hmn
      by_cases hev : m % 2 = 0
      · have heq : 2 * (m / 2) = m := by omega
        rw [heq]
        have hlt := (ih m hmn).2 hev (by omega)
        omega
      · have heq : 2 * (m / 2) = m - 1 := by omega
        rw [heq]; exact Nat.le_refl _
    constructor
    · -- Part 1: n even → certVal n < certVal (n + 1)
      intro hn_ev
      by_cases hn0 : n = 0
      · subst hn0
        rw [certVal_zero, Nat.zero_add]
        have h1 : B * 0 + 1 = 1 := by omega
        have hr1 : 1 < B := by have := hs.B_ge_two; omega
        rw [← h1, certVal_step hs.B_ge_two w0 w1 hr1 (by omega)]
        have ⟨_, hlt01⟩ := hs.even_lt_next 0 (by have := hs.B_ge_two; omega) (by decide)
        simp only [Nat.zero_add] at hlt01
        omega
      · let q := n / B
        let r := n % B
        have hr : r < B := Nat.mod_lt n (by have := hs.B_ge_two; omega)
        have hdecomp : B * q + r = n := Nat.div_add_mod n B
        have hr_ev : r % 2 = 0 := by
          have hBe := hs.B_even
          have h1 : (B * q + r) % 2 = r % 2 := by
            rw [Nat.add_mod, Nat.mul_mod, hBe]; simp
          omega
        have hr1_lt : r + 1 < B := by have := hs.B_even; omega
        have hq_lt : q < n := Nat.div_lt_self (by omega) hs.B_ge_two
        have hdecomp1 : B * q + (r + 1) = n + 1 := by omega
        have hl := certVal_step hs.B_ge_two w0 w1 hr (by omega : B * q + r > 0)
        have hr_step := certVal_step hs.B_ge_two w0 w1 hr1_lt (by omega : B * q + (r + 1) > 0)
        rw [hdecomp] at hl
        rw [hdecomp1] at hr_step
        rw [hl, hr_step]
        have ⟨hcarry_ord, hv_lt⟩ := hs.even_lt_next r hr hr_ev
        have hle_rec := hq_le q hq_lt
        rcases hcarry_ord with hw1r | hw1r1
        · simp only [hw1r, ↓reduceIte]
          split <;> omega
        · simp only [hw1r1, Nat.lt_irrefl, ↓reduceIte]
          split <;> omega
    · -- Part 2: n even ∧ n ≥ 2 → certVal n < certVal (n - 1)
      intro hn_ev hn2
      let q := n / B
      let r := n % B
      have hr : r < B := Nat.mod_lt n (by have := hs.B_ge_two; omega)
      have hdecomp : B * q + r = n := Nat.div_add_mod n B
      have hr_ev : r % 2 = 0 := by
        have hBe := hs.B_even
        have h1 : (B * q + r) % 2 = r % 2 := by
          rw [Nat.add_mod, Nat.mul_mod, hBe]; simp
        omega
      have hq_lt : q < n := Nat.div_lt_self (by omega) hs.B_ge_two
      by_cases hr0 : r = 0
      · -- Wrap-around: n = B * q, n - 1 = B * (q - 1) + (B - 1)
        have hq1 : q ≥ 1 := Nat.pos_of_ne_zero (fun hq0 => by
          rw [hq0, hr0, Nat.mul_zero, Nat.add_zero] at hdecomp; omega)
        have hprev_decomp : B * (q - 1) + (B - 1) = n - 1 := by
          have hqeq : q = (q - 1) + 1 := by omega
          have hmul : B * q = B * (q - 1) + B := by
            calc B * q = B * ((q - 1) + 1) := congrArg (B * ·) hqeq
              _ = B * (q - 1) + B := by rw [Nat.mul_add, Nat.mul_one]
          have := hs.B_ge_two
          omega
        have hB2 := hs.B_ge_two
        have hBq_pos : B * q + 0 > 0 := by
          have : B * 1 ≤ B * q := Nat.mul_le_mul_left B hq1
          omega
        have hprev_pos : B * (q - 1) + (B - 1) > 0 := by omega
        have hl := certVal_step hs.B_ge_two w0 w1 (q := q) (r := 0) (by omega) hBq_pos
        have hr_step := certVal_step hs.B_ge_two w0 w1 (q := q - 1) (r := B - 1) (by omega) hprev_pos
        rw [hr0] at hdecomp
        rw [hdecomp] at hl
        rw [hprev_decomp] at hr_step
        rw [hl, hr_step]
        simp only [hs.w1_zero_pos, hs.w1_last_zero, Nat.lt_irrefl, ↓reduceIte]
        have hle_pred := hq_pred_le q hq1 hq_lt
        have hwrap := hs.wrap_lt
        omega
      · -- Same block: r ≥ 2, n - 1 = B * q + (r - 1)
        have hr2 : r ≥ 2 := by omega
        have hprev_decomp : B * q + (r - 1) = n - 1 := by omega
        have hl := certVal_step hs.B_ge_two w0 w1 hr (by omega : B * q + r > 0)
        have hr_step := certVal_step hs.B_ge_two w0 w1 (r := r - 1) (q := q) (by omega) (by omega)
        rw [hdecomp] at hl
        rw [hprev_decomp] at hr_step
        rw [hl, hr_step]
        have ⟨hcarry_ord, hv_lt⟩ := hs.even_lt_prev r hr hr_ev hr2
        have hle_rec := hq_le q hq_lt
        rcases hcarry_ord with hw1r | hw1r1
        · simp only [hw1r, ↓reduceIte]
          split <;> omega
        · simp only [hw1r1, Nat.lt_irrefl, ↓reduceIte]
          split <;> omega

/-- **Reusable Engine Soundness Theorem (`unitCarrySpec_sound`):**
    Any sequence `f` obeying a unit-carry recurrence `(B, w0, w1)` satisfying `UnitCarrySpec`
    has `f n > 0` and exact 2-adic valuation `v2 (f n) = certVal B w0 w1 n` for ALL `n : Nat`. -/
theorem unitCarrySpec_sound
    {B : Nat} {w0 w1 : Nat → Nat} (hs : UnitCarrySpec B w0 w1)
    (f : Nat → Nat) (hf0 : f 0 = 1)
    (hrec : ∀ q r : Nat, r < B →
      f (B * q + r) =
        sumRange (fun c => (if c = 0 then w0 r else if c = 1 then w1 r else 0) * f (q - c)) (q + 1)) :
    ∀ n : Nat, f n > 0 ∧ v2 (f n) = certVal B w0 w1 n := by
  let w : Nat → Nat → Nat := fun c r => if c = 0 then w0 r else if c = 1 then w1 r else 0
  have heven := unitCarrySpec_even_min hs
  apply ultrametric_odd_parity_lift B hs.B_ge_two w f (certVal B w0 w1) hf0 (certVal_zero B w0 w1) hrec
  · -- Lower bound on every active term
    intro q r hr hqr c hc hw_pos
    rw [certVal_step hs.B_ge_two w0 w1 hr hqr]
    cases c with
    | zero =>
      simp only [w, ↓reduceIte, Nat.sub_zero]
      by_cases hw1 : w1 r > 0
      · simp only [hw1, ↓reduceIte]
        by_cases hqev : q % 2 = 0
        · have : 2 * (q / 2) = q := by omega
          rw [this]; omega
        · have hlt := (heven (2 * (q / 2))).1 (by omega)
          have hqeq : 2 * (q / 2) + 1 = q := by omega
          rw [hqeq] at hlt; omega
      · simp only [hw1, ↓reduceIte]; omega
    | succ c' =>
      cases c' with
      | zero =>
        simp only [w, Nat.zero_add, Nat.one_ne_zero, ↓reduceIte] at hw_pos ⊢
        rw [hs.carry_v2_eq r hr hw_pos]
        simp only [hw_pos, ↓reduceIte]
        by_cases hqev : q % 2 = 0
        · have hq2 : q ≥ 2 := by omega
          have hlt := (heven q).2 hqev hq2
          have hqeq : 2 * (q / 2) = q := by omega
          rw [hqeq]; omega
        · have hqeq : 2 * (q / 2) = q - 1 := by omega
          rw [hqeq]; omega
      | succ c'' =>
        have hne0 : c'' + 1 + 1 ≠ 0 := by omega
        have hne1 : c'' + 1 + 1 ≠ 1 := by omega
        simp only [w, hne0, hne1, ↓reduceIte] at hw_pos
        omega
  · -- Odd-parity minimizer count (here strictly 1 everywhere: zero ties!)
    intro q r hr hqr
    rw [certVal_step hs.B_ge_two w0 w1 hr hqr]
    have hsplit_ge2 : ∀ (g : Nat → Nat), (∀ c ≥ 2, g c = 0) →
        sumRange g (q + 1) = if q = 0 then g 0 else g 0 + g 1 := by
      intro g hg
      cases q with
      | zero => simp [sumRange]
      | succ q' =>
        have hle : 2 ≤ q' + 1 + 1 := by omega
        rw [← sumRange_extend hle (fun i hi _ => hg i hi)]
        simp [sumRange]
    rw [hsplit_ge2 _ (fun c hc => by
      have hc0 : c ≠ 0 := by omega
      have hc1 : c ≠ 1 := by omega
      simp [w, hc0, hc1])]
    by_cases hq0 : q = 0
    · subst hq0
      simp [w, hs.w0_pos r hr, certVal_zero]
    · simp only [hq0, ↓reduceIte]
      have hw0_pos : w0 r > 0 := hs.w0_pos r hr
      by_cases hw1 : w1 r > 0
      · simp only [w, hw1, ↓reduceIte, Nat.sub_zero, Nat.one_ne_zero, hw0_pos, true_and]
        rw [hs.carry_v2_eq r hr hw1]
        by_cases hqev : q % 2 = 0
        · have hq2 : q ≥ 2 := by omega
          have hlt := (heven q).2 hqev hq2
          have hqeq : 2 * (q / 2) = q := by omega
          rw [hqeq]
          have hne : certVal B w0 w1 (q - 1) ≠ certVal B w0 w1 q := by omega
          simp [hne]
        · have hlt := (heven (2 * (q / 2))).1 (by omega)
          have hqeq1 : 2 * (q / 2) = q - 1 := by omega
          have hqeq2 : 2 * (q / 2) + 1 = q := by omega
          rw [hqeq2] at hlt
          rw [hqeq1] at hlt ⊢
          have hne : certVal B w0 w1 q ≠ certVal B w0 w1 (q - 1) := by omega
          simp [hne]
      · have hw10 : w1 r = 0 := by omega
        simp [w, hw10, hw0_pos]

/-- **Finite-to-Infinite `decide` Compiler Bridge:**
    A finite Boolean check `checkUnitCarryCert B w0 w1 = true` discharges the infinite
    exact 2-adic valuation theorem `∀ n : Nat, f n > 0 ∧ v2 (f n) = certVal B w0 w1 n`. -/
theorem unitCarryCert_sound
    {B : Nat} {w0 w1 : Nat → Nat}
    (hcert : checkUnitCarryCert B w0 w1 = true)
    (f : Nat → Nat) (hf0 : f 0 = 1)
    (hrec : ∀ q r : Nat, r < B →
      f (B * q + r) =
        sumRange (fun c => (if c = 0 then w0 r else if c = 1 then w1 r else 0) * f (q - c)) (q + 1)) :
    ∀ n : Nat, f n > 0 ∧ v2 (f n) = certVal B w0 w1 n :=
  unitCarrySpec_sound (checkUnitCarryCert_sound hcert) f hf0 hrec

/-- Helper connecting `maskRepCount m masks` with unit-carry recurrence when max digit sum `< 2 * 2^m`. -/
theorem maskRepCount_unitCarry_of_cert
    (m : Nat) (hm : m ≥ 1) (masks : List Nat)
    (hmax : ∀ s ≥ 2 * 2 ^ m, digitWeight m masks s = 0)
    (hcert : checkUnitCarryCert (2 ^ m)
      (fun r => digitWeight m masks r)
      (fun r => digitWeight m masks (2 ^ m + r)) = true) :
    ∀ n : Nat,
      maskRepCount m masks n > 0 ∧
      v2 (maskRepCount m masks n) =
        certVal (2 ^ m) (fun r => digitWeight m masks r) (fun r => digitWeight m masks (2 ^ m + r)) n := by
  apply unitCarryCert_sound hcert (maskRepCount m masks) (maskRepCount_zero m hm masks)
  intro q r hr
  rw [maskRepCount_slice m hm masks q r hr]
  apply sumRange_congr
  intro c _
  cases c with
  | zero => simp
  | succ c' =>
    cases c' with
    | zero => simp
    | succ c'' =>
      have hge : (c'' + 2) * 2 ^ m + r ≥ 2 * 2 ^ m := by
        have h1 : 2 * 2 ^ m ≤ (c'' + 2) * 2 ^ m := Nat.mul_le_mul_right (2 ^ m) (by omega)
        omega
      have hz := hmax ((c'' + 2) * 2 ^ m + r) hge
      simp [hz]

/-! ### Live `decide`-Discharged Non-Binomial Periodic Bitmask Sumset Theorems -/

/-- **Non-Binomial Application 1 (Proved `∀ n : Nat` via `decide`):**
    The mixed periodic bitmask sumset `3 * S_2 + N` (`masks = [1, 1, 1, 3]` at stride `m = 2`,
    non-binomial digit weights `w0 = [1, 4, 7, 8]`, `w1 = [7, 4, 1, 0]`). -/
theorem nonbinomial_3S2_add_N_v2 :
    ∀ n : Nat,
      maskRepCount 2 [1, 1, 1, 3] n > 0 ∧
      v2 (maskRepCount 2 [1, 1, 1, 3] n) =
        certVal 4 (fun r => digitWeight 2 [1, 1, 1, 3] r)
                  (fun r => digitWeight 2 [1, 1, 1, 3] (4 + r)) n := by
  have hmax : ∀ s ≥ 8, digitWeight 2 [1, 1, 1, 3] s = 0 := by
    intro s hs
    by_cases hgt : s > 12
    · exact digitWeight_eq_zero_of_gt 2 [1, 1, 1, 3] s (by simp; omega)
    · have : s = 8 ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
  exact maskRepCount_unitCarry_of_cert 2 (by decide) [1, 1, 1, 3] hmax (by decide)

/-- **Non-Binomial Application 2 (Proved `∀ n : Nat` via `decide`):**
    The mixed 3-strided bitmask sumset `2 * S_3 + 2 * B(3, {0, 2})` (`masks = [1, 1, 5, 5]` at stride `m = 3`,
    non-binomial digit weights `w0 = [1, 4, 6, 4, 3, 8, 12, 8]`, `w1 = [3, 4, 6, 4, 1, 0, 0, 0]`). -/
theorem nonbinomial_2S3_add_2B302_v2 :
    ∀ n : Nat,
      maskRepCount 3 [1, 1, 5, 5] n > 0 ∧
      v2 (maskRepCount 3 [1, 1, 5, 5] n) =
        certVal 8 (fun r => digitWeight 3 [1, 1, 5, 5] r)
                  (fun r => digitWeight 3 [1, 1, 5, 5] (8 + r)) n := by
  have hmax : ∀ s ≥ 16, digitWeight 3 [1, 1, 5, 5] s = 0 := by
    intro s hs
    by_cases hgt : s > 28
    · exact digitWeight_eq_zero_of_gt 3 [1, 1, 5, 5] s (by simp; omega)
    · have : s = 16 ∨ s = 17 ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨
             s = 23 ∨ s = 24 ∨ s = 25 ∨ s = 26 ∨ s = 27 ∨ s = 28 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact maskRepCount_unitCarry_of_cert 3 (by decide) [1, 1, 5, 5] hmax (by decide)

/-! ## Layer 5: Infinite 2-Parameter Theorem Families via Both Engines -/

/-! ### Theorem Family 1: Even-Window Strided Sumset Exact 2-Adic Valuation Law -/

/-- Symbolic verification that the infinite 2-parameter family `(m ≥ 1, 2*t < 2^m)` satisfies `UnitCarrySpec`. -/
theorem evenWindow_unitCarrySpec {m t : Nat} (hm : m ≥ 1) (ht : 2 * t < 2 ^ m) :
    UnitCarrySpec (2 ^ m) (evenW0 m t) (evenW1 m t) := by
  have hB2 : 2 ^ m ≥ 2 := by
    have h1 : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    omega
  have hBeven : 2 ^ m % 2 = 0 := by
    have hm1 : m = (m - 1) + 1 := by omega
    have hpow : 2 ^ m = 2 ^ (m - 1) * 2 := by
      calc 2 ^ m = 2 ^ ((m - 1) + 1) := congrArg (2 ^ ·) hm1
        _ = 2 ^ (m - 1) * 2 := Nat.pow_succ _ _
    omega
  have h2M : 2 ^ m + 2 * t = 2 * (2 ^ (m - 1) + t) := by
    have hm1 : m = (m - 1) + 1 := by omega
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      calc 2 ^ m = 2 ^ ((m - 1) + 1) := congrArg (2 ^ ·) hm1
        _ = 2 ^ (m - 1) * 2 := Nat.pow_succ _ _
        _ = 2 * 2 ^ (m - 1) := Nat.mul_comm _ _
    omega
  refine ⟨hB2, hBeven, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- w0_pos
    intro r hr
    exact choose_pos (by omega)
  · -- w1_zero_pos
    exact choose_pos (by omega)
  · -- w1_last_zero
    exact choose_eq_zero_of_lt (by omega)
  · -- carry_v2_eq
    intro r hr hw1
    have hr_le : r ≤ 2 * t := by
      by_cases hle : r ≤ 2 * t
      · exact hle
      · have hz : evenW1 m t r = 0 := choose_eq_zero_of_lt (by omega)
        omega
    unfold evenW0 evenW1
    rw [v2_choose_pow2_add_lo ht hr_le, v2_choose_pow2_add_hi ht hr_le]
  · -- wrap_lt
    unfold evenW0
    rw [choose_zero_right, v2_one]
    have hsym : choose (2 ^ m + 2 * t) (2 ^ m - 1) = choose (2 ^ m + 2 * t) (2 * t + 1) := by
      have h1 := choose_symm (n := 2 ^ m + 2 * t) (k := 2 ^ m - 1) (by omega)
      have h2 : 2 ^ m + 2 * t - (2 ^ m - 1) = 2 * t + 1 := by omega
      rw [h2] at h1
      exact h1.symm
    rw [hsym, v2_choose_pow2_add_even_boundary ht]
    omega
  · -- even_lt_next
    intro r hr hev
    constructor
    · by_cases hle : r + 1 ≤ 2 * t
      · exact Or.inl (choose_pos (by omega))
      · exact Or.inr (choose_eq_zero_of_lt (by omega))
    · unfold evenW0
      rw [h2M]
      have h := v2_choose_even_alt_odd (M := 2 ^ (m - 1) + t) (r := r + 1) (by omega) (by omega) (by omega)
      simpa using h
  · -- even_lt_prev
    intro r hr hev hge2
    constructor
    · by_cases hle : r ≤ 2 * t
      · exact Or.inl (choose_pos (by omega))
      · have hgt : r - 1 > 2 * t := by omega
        exact Or.inr (choose_eq_zero_of_lt (by omega))
    · unfold evenW0
      rw [h2M]
      exact v2_choose_even_alt_even (M := 2 ^ (m - 1) + t) (r := r) (by omega) (by omega) hev

/-- **THEOREM 1 (2-Parameter Infinite Family — Even-Window Strided Valuation Law):**
    For ALL strides `m ≥ 1`, ALL even multiplicities `k = 2^m + 2*t ∈ [2^m, 2^(m+1) - 2]`,
    and ALL `n : Nat`, the combinatorial sumset count `r_{k S_m}(n)` is strictly positive and
    has exact 2-adic valuation `evenWindowVal m t n` (with strict even-local-minimum alternation). -/
theorem even_window_strided_v2 {m t : Nat} (hm : m ≥ 1) (ht : 2 * t < 2 ^ m) :
    ∀ n : Nat,
      stridedRepCount m (2 ^ m + 2 * t) n > 0 ∧
      v2 (stridedRepCount m (2 ^ m + 2 * t) n) = evenWindowVal m t n := by
  apply unitCarrySpec_sound (evenWindow_unitCarrySpec hm ht)
    (stridedRepCount m (2 ^ m + 2 * t)) (stridedRepCount_zero m (2 ^ m + 2 * t) hm)
  intro q r hr
  rw [stridedRepCount_slice m (2 ^ m + 2 * t) hm q r hr]
  apply sumRange_congr
  intro c _
  cases c with
  | zero => simp [evenW0]
  | succ c' =>
    cases c' with
    | zero => simp [evenW1]
    | succ c'' =>
      have hgt : 2 ^ m + 2 * t < (c'' + 1 + 1) * 2 ^ m + r := by
        have h1 : 2 * 2 ^ m ≤ (c'' + 1 + 1) * 2 ^ m := Nat.mul_le_mul_right (2 ^ m) (by omega)
        omega
      simp [choose_eq_zero_of_lt hgt]

/-- **COROLLARY 1A (Universal `(2^(m+1) - 2)`-Collapse Theorem):**
    For EVERY stride `m ≥ 1` and EVERY `n : Nat`, the `(2^(m+1) - 2)`-fold `m`-strided
    Moser-de Bruijn sumset representation count has the EXACT 2-adic valuation of `n + 1`!
    `∀ m ≥ 1, ∀ n : Nat, v2 (stridedRepCount m (2^(m+1) - 2) n) = v2 (n + 1)`. -/
theorem upper_endpoint_v2_collapse {m : Nat} (hm : m ≥ 1) :
    ∀ n : Nat, v2 (stridedRepCount m (2 ^ (m + 1) - 2) n) = v2 (n + 1) := by
  have hm1 : m = (m - 1) + 1 := by omega
  have hpowm : 2 ^ m = 2 * 2 ^ (m - 1) := by
    calc 2 ^ m = 2 ^ ((m - 1) + 1) := congrArg (2 ^ ·) hm1
      _ = 2 ^ (m - 1) * 2 := Nat.pow_succ _ _
      _ = 2 * 2 ^ (m - 1) := Nat.mul_comm _ _
  have hpow_pos : 2 ^ (m - 1) ≥ 1 := Nat.two_pow_pos (m - 1)
  have hB2 : 2 ^ m ≥ 2 := by omega
  let t := 2 ^ (m - 1) - 1
  have h2t : 2 * t = 2 ^ m - 2 := by omega
  have ht : 2 * t < 2 ^ m := by omega
  have hk_eq : 2 ^ m + 2 * t = 2 ^ (m + 1) - 2 := by
    have hp1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have hval : ∀ n : Nat, evenWindowVal m t n = v2 (n + 1) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hn0 : n = 0
      · subst hn0
        unfold evenWindowVal
        rw [certVal_zero, v2_one]
      · let q := n / 2 ^ m
        let r := n % 2 ^ m
        have hr : r < 2 ^ m := Nat.mod_lt n (by omega)
        have hdecomp : 2 ^ m * q + r = n := Nat.div_add_mod n (2 ^ m)
        have hq_lt : q < n := Nat.div_lt_self (by omega) hB2
        have hstep := certVal_step hB2 (evenW0 m t) (evenW1 m t) hr (by omega : 2 ^ m * q + r > 0)
        rw [hdecomp] at hstep
        change certVal (2 ^ m) (evenW0 m t) (evenW1 m t) n = v2 (n + 1)
        rw [hstep]
        by_cases hrlast : r = 2 ^ m - 1
        · have hw1_0 : evenW1 m t r = 0 := by
            rw [hrlast]; exact choose_eq_zero_of_lt (by omega)
          simp only [hw1_0, Nat.lt_irrefl, ↓reduceIte]
          have hih : certVal (2 ^ m) (evenW0 m t) (evenW1 m t) q = v2 (q + 1) := ih q hq_lt
          rw [hih]
          have hv0 : v2 (evenW0 m t r) = m := by
            rw [hrlast]
            unfold evenW0
            have hsym : choose (2 ^ m + 2 * t) (2 ^ m - 1) = choose (2 ^ m + 2 * t) (2 * t + 1) := by
              have h1 := choose_symm (n := 2 ^ m + 2 * t) (k := 2 ^ m - 1) (by omega)
              have h2 : 2 ^ m + 2 * t - (2 ^ m - 1) = 2 * t + 1 := by omega
              rw [h2] at h1; exact h1.symm
            rw [hsym, v2_choose_pow2_add_even_boundary ht]
          rw [hv0]
          have hn1 : n + 1 = 2 ^ m * (q + 1) := by
            rw [Nat.mul_add, Nat.mul_one, ← hdecomp, hrlast]; omega
          rw [hn1, v2_pow_two_mul m (Nat.succ_pos q)]
        · have hr_le : r ≤ 2 * t := by omega
          have hw1_pos : evenW1 m t r > 0 := choose_pos (by omega)
          simp only [hw1_pos, ↓reduceIte]
          have hih : certVal (2 ^ m) (evenW0 m t) (evenW1 m t) (2 * (q / 2)) = v2 (2 * (q / 2) + 1) :=
            ih (2 * (q / 2)) (by omega)
          rw [hih, v2_odd (n := 2 * (q / 2) + 1) (by omega), Nat.add_zero]
          unfold evenW0
          rw [v2_choose_pow2_add_lo ht hr_le, h2t, v2_choose_pow2_sub2 hm (by omega)]
          have hn1 : n + 1 = 2 ^ m * q + (r + 1) := by omega
          rw [hn1, v2_add_pow_mul_of_lt (by omega) (by omega)]
  intro n
  rw [← hk_eq]
  rw [(even_window_strided_v2 hm ht n).2, hval n]

/-! ### Theorem Family 2: Power-of-Two Strided Kummer Stability Law (`∀ m ≥ 1, r ≥ m, n : Nat`) -/

theorem vBase_zero (m : Nat) : vBase m 0 = 0 := certVal_zero _ _ _

theorem vBase_step_zero {m : Nat} (hm : m ≥ 1) (q : Nat) :
    vBase m (2 ^ m * q) = vBase m (2 * (q / 2)) := by
  cases q with
  | zero => simp [vBase_zero]
  | succ q' =>
    have hB2 : 2 ^ m ≥ 2 := by
      have h1 : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
      omega
    have hstep := certVal_step hB2 (evenW0 m 0) (evenW1 m 0) (q := q' + 1) (r := 0) (by omega) (by
      have := Nat.two_pow_pos m; rw [Nat.mul_add, Nat.mul_one]; omega)
    rw [Nat.add_zero] at hstep
    unfold vBase evenWindowVal
    rw [hstep]
    have hw0 : evenW0 m 0 0 = 1 := choose_zero_right _
    have hw1 : evenW1 m 0 0 > 0 := choose_pos (by omega)
    simp [hw0, hw1, v2_one]

theorem vBase_step_pos {m : Nat} (hm : m ≥ 1) (q rho : Nat) (h1 : 1 ≤ rho) (h2 : rho < 2 ^ m) :
    vBase m (2 ^ m * q + rho) = (m - v2 rho) + vBase m q := by
  have hB2 : 2 ^ m ≥ 2 := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hm
    omega
  have hstep := certVal_step hB2 (evenW0 m 0) (evenW1 m 0) (q := q) (r := rho) h2 (by omega)
  unfold vBase evenWindowVal
  rw [hstep]
  have hw1 : evenW1 m 0 rho = 0 := choose_eq_zero_of_lt (by omega)
  have hw0 : v2 (evenW0 m 0 rho) = m - v2 rho := by
    unfold evenW0; simp only [Nat.mul_zero, Nat.add_zero]
    exact v2_choose_pow2 (by omega) h2
  simp [hw1, hw0]

theorem vBase_even_min {m : Nat} (hm : m ≥ 1) :
    ∀ n : Nat,
      (n % 2 = 0 → vBase m n < vBase m (n + 1)) ∧
      (n % 2 = 0 → n ≥ 2 → vBase m n < vBase m (n - 1)) :=
  unitCarrySpec_even_min (evenWindow_unitCarrySpec hm (by have := Nat.two_pow_pos m; omega))

theorem vBase_clear_le {m : Nat} (hm : m ≥ 1) (q : Nat) :
    vBase m (2 * (q / 2)) ≤ vBase m q := by
  by_cases hq : q % 2 = 0
  · have : 2 * (q / 2) = q := by omega
    rw [this]; exact Nat.le_refl _
  · have hlt := (vBase_even_min hm (2 * (q / 2))).1 (by omega)
    have hqeq : 2 * (q / 2) + 1 = q := by omega
    rw [hqeq] at hlt; omega

theorem vBase_clear_le_pred {m : Nat} (hm : m ≥ 1) {q : Nat} (hq : q ≥ 1) :
    vBase m (2 * (q / 2)) ≤ vBase m (q - 1) := by
  by_cases hqev : q % 2 = 0
  · have hlt := (vBase_even_min hm q).2 hqev (by omega)
    have hqeq : 2 * (q / 2) = q := by omega
    rw [hqeq]; omega
  · have hqeq : 2 * (q / 2) = q - 1 := by omega
    rw [hqeq]; exact Nat.le_refl _

theorem vBase_cmp_m_add_div {m : Nat} (hm : m ≥ 1) (a : Nat) :
    ((a % 2 ^ m) % 2 = 1 → vBase m a = m + vBase m (a / 2 ^ m)) ∧
    ((a % 2 ^ m) % 2 = 0 → vBase m a < m + vBase m (a / 2 ^ m)) := by
  let q := a / 2 ^ m
  let rho := a % 2 ^ m
  have hrho : rho < 2 ^ m := Nat.mod_lt a (Nat.two_pow_pos m)
  have hdecomp : 2 ^ m * q + rho = a := Nat.div_add_mod a (2 ^ m)
  constructor
  · intro hodd
    have h1 : 1 ≤ rho := by omega
    calc vBase m a = vBase m (2 ^ m * q + rho) := congrArg (vBase m) hdecomp.symm
      _ = (m - v2 rho) + vBase m q := vBase_step_pos hm q rho h1 hrho
      _ = m + vBase m (a / 2 ^ m) := by rw [v2_odd hodd, Nat.sub_zero]
  · intro hev
    by_cases h0 : rho = 0
    · have ha_eq : a = 2 ^ m * q := by omega
      have hva : vBase m a = vBase m (2 * (q / 2)) := by
        calc vBase m a = vBase m (2 ^ m * q) := congrArg (vBase m) ha_eq
          _ = vBase m (2 * (q / 2)) := vBase_step_zero hm q
      have hclr := vBase_clear_le hm q
      change vBase m a < m + vBase m q
      omega
    · have h1 : 1 ≤ rho := by omega
      have hva : vBase m a = (m - v2 rho) + vBase m q := by
        calc vBase m a = vBase m (2 ^ m * q + rho) := congrArg (vBase m) hdecomp.symm
          _ = (m - v2 rho) + vBase m q := vBase_step_pos hm q rho h1 hrho
      have hv1 : v2 rho ≥ 1 := by
        have h2 : rho = 2 * (rho / 2) := by omega
        rw [h2, v2_two_mul (by omega)]; omega
      change vBase m a < m + vBase m q
      omega

theorem pow2StridedVal_zero (m r : Nat) : pow2StridedVal m r 0 = 0 := by
  unfold pow2StridedVal
  simp [vBase_zero]

theorem pow2StridedVal_divMod {m r a b : Nat} (hb : b < 2 ^ r) :
    pow2StridedVal m r (2 ^ r * a + b) =
    if b = 0 then vBase m (2 * (a / 2)) else (r - v2 b) + vBase m a := by
  unfold pow2StridedVal
  have hmod : (2 ^ r * a + b) % 2 ^ r = b := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have hdiv : (2 ^ r * a + b) / 2 ^ r = a := by
    rw [Nat.mul_add_div (Nat.two_pow_pos r), Nat.div_eq_of_lt hb, Nat.add_zero]
  rw [hmod, hdiv]

/-- Exact bridge: `pow2StridedVal m r (2^(r-m) * a) = vBase m a` for ALL `a : Nat`. -/
theorem pow2StridedVal_mul_C {m r : Nat} (hm : m ≥ 1) (hrm : r ≥ m) (a : Nat) :
    pow2StridedVal m r (2 ^ (r - m) * a) = vBase m a := by
  let a' := a / 2 ^ m
  let alpha := a % 2 ^ m
  have halpha : alpha < 2 ^ m := Nat.mod_lt a (Nat.two_pow_pos m)
  have ha_eq : 2 ^ m * a' + alpha = a := Nat.div_add_mod a (2 ^ m)
  have hpow_mul : 2 ^ (r - m) * 2 ^ m = 2 ^ r := by
    rw [← Nat.pow_add]; congr 1; omega
  have hCa : 2 ^ (r - m) * a = 2 ^ r * a' + 2 ^ (r - m) * alpha := by
    calc 2 ^ (r - m) * a = 2 ^ (r - m) * (2 ^ m * a' + alpha) := congrArg (2 ^ (r - m) * ·) ha_eq.symm
      _ = (2 ^ (r - m) * 2 ^ m) * a' + 2 ^ (r - m) * alpha := by rw [Nat.mul_add, Nat.mul_assoc]
      _ = 2 ^ r * a' + 2 ^ (r - m) * alpha := by rw [hpow_mul]
  have hb_lt : 2 ^ (r - m) * alpha < 2 ^ r := by
    rw [← hpow_mul]
    exact Nat.mul_lt_mul_of_pos_left halpha (Nat.two_pow_pos (r - m))
  rw [hCa, pow2StridedVal_divMod hb_lt]
  by_cases ha0 : alpha = 0
  · simp only [ha0, Nat.mul_zero, ↓reduceIte]
    rw [← ha_eq, ha0, Nat.add_zero, vBase_step_zero hm a']
  · have hpos : 2 ^ (r - m) * alpha > 0 := Nat.mul_pos (Nat.two_pow_pos (r - m)) (by omega)
    have hne : 2 ^ (r - m) * alpha ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    rw [v2_pow_two_mul (r - m) (by omega)]
    rw [← ha_eq, vBase_step_pos hm a' alpha (by omega) halpha]
    have hvlt : v2 alpha < m := v2_lt_of_lt_pow (by omega) halpha
    omega

/-- Ultrametric strict inequality for distinct nonzero offsets `< 2^d`:
    for `0 < c < 2^d`, `0 < u < 2^d`, `c ≠ u`, `v2 c + v2 |u - c| < d + v2 u`. -/
theorem v2_ultrametric_gap_lt {d c u : Nat} (hc0 : 0 < c) (hc : c < 2 ^ d)
    (_hu0 : 0 < u) (_hu : u < 2 ^ d) (hlt : c < u) :
    v2 c + v2 (u - c) < d + v2 u := by
  have huc0 : 0 < u - c := by omega
  have hmin : min (v2 c) (v2 (u - c)) ≤ v2 u := by
    have h := v2_add_min_le hc0 huc0
    have hsum : c + (u - c) = u := by omega
    rwa [hsum] at h
  have hvc : v2 c < d := v2_lt_of_lt_pow hc0 hc
  have hvuc : v2 (u - c) < d := v2_lt_of_lt_pow huc0 (by omega)
  omega

theorem v2_ultrametric_gap_gt {d c u : Nat} (hc0 : 0 < c) (hc : c < 2 ^ d)
    (hu0 : 0 < u) (_hu : u < 2 ^ d) (hgt : u < c) :
    v2 c + v2 (c - u) < d + v2 u := by
  have hcu0 : 0 < c - u := by omega
  have hmin : min (v2 c) (v2 (c - u)) ≤ v2 u := by
    by_cases hle : min (v2 c) (v2 (c - u)) ≤ v2 u
    · exact hle
    · have h1 : v2 u < v2 (c - u) := by omega
      have hsum : v2 (u + (c - u)) = v2 u := v2_add_of_lt hu0 hcu0 h1
      have heq : u + (c - u) = c := by omega
      rw [heq] at hsum
      omega
  have hvc : v2 c < d := v2_lt_of_lt_pow hc0 hc
  have hvcu : v2 (c - u) < d := v2_lt_of_lt_pow hcu0 (by omega)
  omega

/-- Helper: counting 3 distinct active indices `{0, u, C}` in `sumRange` yields `3`. -/
theorem sumRange_triple_one {N u C : Nat} {g : Nat → Nat}
    (hu0 : 0 < u) (huC : u < C) (hCN : C < N)
    (h0 : g 0 = 1) (hu : g u = 1) (hC : g C = 1)
    (hrest : ∀ i < N, i ≠ 0 → i ≠ u → i ≠ C → g i = 0) :
    sumRange g N = 3 := by
  let g0 : Nat → Nat := fun i => if i = 0 then 1 else 0
  let gu : Nat → Nat := fun i => if i = u then 1 else 0
  let gC : Nat → Nat := fun i => if i = C then 1 else 0
  have hdecomp : ∀ i < N, g i = g0 i + gu i + gC i := by
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0; simp [g0, gu, gC, h0, show 0 ≠ u by omega, show 0 ≠ C by omega]
    · by_cases hiu : i = u
      · subst hiu; simp [g0, gu, gC, hu, hi0, show i ≠ C by omega]
      · by_cases hiC : i = C
        · subst hiC; simp [g0, gu, gC, hC, hi0, hiu]
        · simp [g0, gu, gC, hi0, hiu, hiC, hrest i hi hi0 hiu hiC]
  rw [sumRange_congr hdecomp, sumRange_add, sumRange_add]
  have s0 : sumRange g0 N = 1 := by
    have := sumRange_single (f := g0) (n := N) (k := 0) (by omega) (fun i _ hne => by simp [g0, hne])
    simpa [g0] using this
  have su : sumRange gu N = 1 := by
    have := sumRange_single (f := gu) (n := N) (k := u) (by omega) (fun i _ hne => by simp [gu, hne])
    simpa [gu] using this
  have sC : sumRange gC N = 1 := by
    have := sumRange_single (f := gC) (n := N) (k := C) (by omega) (fun i _ hne => by simp [gC, hne])
    simpa [gC] using this
  omega

/-- Helper: valuation of `pow2StridedVal m r (C * a + d)` for `0 < d < C`. -/
theorem pow2StridedVal_mul_C_add {m r : Nat} (_hm : m ≥ 1) (hrm : r ≥ m) (a d : Nat)
    (hd0 : 0 < d) (hd : d < 2 ^ (r - m)) :
    pow2StridedVal m r (2 ^ (r - m) * a + d) = (r - v2 d) + vBase m (a / 2 ^ m) := by
  let a' := a / 2 ^ m
  let alpha := a % 2 ^ m
  have halpha : alpha < 2 ^ m := Nat.mod_lt a (Nat.two_pow_pos m)
  have ha_eq : 2 ^ m * a' + alpha = a := Nat.div_add_mod a (2 ^ m)
  have hpow_mul : 2 ^ (r - m) * 2 ^ m = 2 ^ r := by
    rw [← Nat.pow_add]; congr 1; omega
  have harg : 2 ^ (r - m) * a + d = 2 ^ r * a' + (2 ^ (r - m) * alpha + d) := by
    calc 2 ^ (r - m) * a + d
        = 2 ^ (r - m) * (2 ^ m * a' + alpha) + d := by rw [ha_eq]
      _ = (2 ^ (r - m) * 2 ^ m) * a' + (2 ^ (r - m) * alpha + d) := by
          rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
      _ = 2 ^ r * a' + (2 ^ (r - m) * alpha + d) := by rw [hpow_mul]
  have hb_lt : 2 ^ (r - m) * alpha + d < 2 ^ r := by
    have h1 : 2 ^ (r - m) * (alpha + 1) ≤ 2 ^ (r - m) * 2 ^ m :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, Nat.mul_one, hpow_mul] at h1
    omega
  rw [harg, pow2StridedVal_divMod hb_lt]
  have hne : 2 ^ (r - m) * alpha + d ≠ 0 := by omega
  simp only [hne, ↓reduceIte]
  rw [v2_add_pow_mul_of_lt hd0 hd]

/-- **THEOREM 2 (2-Parameter Infinite Family — Power-of-Two Strided Kummer Stability Law):**
    For ALL strides `m ≥ 1`, ALL powers `r ≥ m` (unbounded carry depth `C = 2^(r-m)`!), and ALL `n : Nat`,
    the combinatorial sumset count `r_{2^r S_m}(n)` is strictly positive and satisfies
    `v2 (r_{2^r S_m}(n)) = pow2StridedVal m r n`, proved via the Odd-Parity Ultrametric Dominance Engine
    (with tie multiplicity strictly `1` or `3` everywhere — zero 2-adic cancellation!). -/
theorem pow2_strided_kummer_v2 {m r : Nat} (hm : m ≥ 1) (hrm : r ≥ m) :
    ∀ n : Nat,
      stridedRepCount m (2 ^ r) n > 0 ∧
      v2 (stridedRepCount m (2 ^ r) n) = pow2StridedVal m r n := by
  have hB2 : 2 ^ m ≥ 2 := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hm
    omega
  let C := 2 ^ (r - m)
  have hC_pos : C ≥ 1 := Nat.two_pow_pos (r - m)
  have hBC : 2 ^ m * C = 2 ^ r := by
    rw [← Nat.pow_add]; congr 1; omega
  have hCB : C * 2 ^ m = 2 ^ r := by rw [Nat.mul_comm, hBC]
  -- Combined local analysis helper: for every (q, rem) with rem < 2^m and 2^m * q + rem > 0,
  -- establish both the lower bound `hge` and the odd-parity minimizer count `hodd`!
  have hlocal : ∀ q rem : Nat, rem < 2 ^ m → 2 ^ m * q + rem > 0 →
      (∀ c ≤ q, choose (2 ^ r) (c * 2 ^ m + rem) > 0 →
        pow2StridedVal m r (2 ^ m * q + rem) ≤
          v2 (choose (2 ^ r) (c * 2 ^ m + rem)) + pow2StridedVal m r (q - c)) ∧
      (sumRange (fun c =>
        if choose (2 ^ r) (c * 2 ^ m + rem) > 0 ∧
           v2 (choose (2 ^ r) (c * 2 ^ m + rem)) + pow2StridedVal m r (q - c) =
           pow2StridedVal m r (2 ^ m * q + rem)
        then 1 else 0) (q + 1)) % 2 = 1 := by
    intro q rem hrem hpos
    let a := q / C
    let u := q % C
    have hu_lt : u < C := Nat.mod_lt q hC_pos
    have hq_eq : C * a + u = q := Nat.div_add_mod q C
    have hn_eq : 2 ^ m * q + rem = 2 ^ r * a + (2 ^ m * u + rem) := by
      calc 2 ^ m * q + rem = 2 ^ m * (C * a + u) + rem := by rw [hq_eq]
        _ = (2 ^ m * C) * a + (2 ^ m * u + rem) := by rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
        _ = 2 ^ r * a + (2 ^ m * u + rem) := by rw [hBC]
    have hb_lt : 2 ^ m * u + rem < 2 ^ r := by
      have h1 : 2 ^ m * (u + 1) ≤ 2 ^ m * C := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, Nat.mul_one, hBC] at h1
      omega
    by_cases hrem0 : rem = 0
    · -- CASE 2: rem = 0 (n = 2^m * q = 2^r * a + 2^m * u)
      subst hrem0
      simp only [Nat.add_zero] at hn_eq hb_lt hpos
      have hq_pos : q ≥ 1 := by
        cases q with
        | zero => simp at hpos
        | succ _ => omega
      by_cases hu0 : u = 0
      · -- SUBCASE 2a: rem = 0, u = 0 (n = 2^r * a, a ≥ 1, strict unique winner between c=0 and c=C)
        have ha_pos : a ≥ 1 := Nat.pos_of_ne_zero (fun ha0 => by
          rw [ha0, hu0, Nat.mul_zero, Nat.add_zero] at hq_eq; omega)
        have hq_Ca : q = C * a := by rw [← hq_eq, hu0, Nat.add_zero]
        have hC_le_q : C ≤ q := by
          rw [hq_Ca]
          calc C = C * 1 := (Nat.mul_one C).symm
            _ ≤ C * a := Nat.mul_le_mul_left C ha_pos
        have htarget : pow2StridedVal m r (2 ^ m * q) = vBase m (2 * (a / 2)) := by
          rw [hn_eq, hu0, Nat.mul_zero, pow2StridedVal_divMod (Nat.two_pow_pos r)]
          simp
        -- Show every middle term 1 ≤ c < C has strictly larger valuation than vBase m (2 * (a / 2))
        have hmid_strict : ∀ c, 1 ≤ c → c < C →
            pow2StridedVal m r (2 ^ m * q) <
              v2 (choose (2 ^ r) (c * 2 ^ m)) + pow2StridedVal m r (q - c) := by
          intro c hc1 hcC
          rw [htarget]
          have hcs_pos : 0 < c * 2 ^ m := Nat.mul_pos (by omega) (Nat.two_pow_pos m)
          have hcs_lt : c * 2 ^ m < 2 ^ r := by
            rw [← hCB]; exact Nat.mul_lt_mul_of_pos_right hcC (Nat.two_pow_pos m)
          have hvc : v2 (choose (2 ^ r) (c * 2 ^ m)) = (r - m) - v2 c := by
            rw [v2_choose_pow2 hcs_pos hcs_lt, Nat.mul_comm, v2_pow_two_mul m (by omega)]
            have : v2 c < r - m := v2_lt_of_lt_pow (by omega) hcC
            omega
          have hqc : q - c = C * (a - 1) + (C - c) := by
            have ha1 : a = (a - 1) + 1 := by omega
            have h1 : C * a = C * (a - 1) + C := by
              calc C * a = C * ((a - 1) + 1) := congrArg (C * ·) ha1
                _ = C * (a - 1) + C := by rw [Nat.mul_add, Nat.mul_one]
            omega
          rw [hvc, hqc, pow2StridedVal_mul_C_add hm hrm (a - 1) (C - c) (by omega) (by omega),
              v2_sub_pow_of_lt (by omega) hcC]
          have hvclt : v2 c < r - m := v2_lt_of_lt_pow (by omega) hcC
          have hcmp := vBase_cmp_m_add_div hm (a - 1)
          have hle_a1 : vBase m (a - 1) ≤ m + vBase m ((a - 1) / 2 ^ m) := by
            by_cases hodd : ((a - 1) % 2 ^ m) % 2 = 1
            · rw [hcmp.1 hodd]; exact Nat.le_refl _
            · have := hcmp.2 (by omega); omega
          have hclr := vBase_clear_le_pred hm ha_pos
          omega
        -- Compare c = 0 (vBase m a) vs c = C (vBase m (a - 1))
        have hval0 : v2 (choose (2 ^ r) (0 * 2 ^ m)) + pow2StridedVal m r (q - 0) = vBase m a := by
          simp only [Nat.zero_mul, Nat.sub_zero, choose_zero_right, v2_one, Nat.zero_add, hq_Ca]
          exact pow2StridedVal_mul_C hm hrm a
        have hvalC : v2 (choose (2 ^ r) (C * 2 ^ m)) + pow2StridedVal m r (q - C) = vBase m (a - 1) := by
          have hsubC : q - C = C * (a - 1) := by
            have ha1 : a = (a - 1) + 1 := by omega
            have h1 : C * a = C * (a - 1) + C := by
              calc C * a = C * ((a - 1) + 1) := congrArg (C * ·) ha1
                _ = C * (a - 1) + C := by rw [Nat.mul_add, Nat.mul_one]
            omega
          rw [hCB, choose_self, v2_one, Nat.zero_add, hsubC]
          exact pow2StridedVal_mul_C hm hrm (a - 1)
        have hc_bound : ∀ c, choose (2 ^ r) (c * 2 ^ m) > 0 → c ≤ C := by
          intro c hcp
          by_cases hle : c ≤ C
          · exact hle
          · have : 2 ^ r < c * 2 ^ m := by
              rw [← hCB]; exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos m)
            have hz := choose_eq_zero_of_lt this
            omega
        constructor
        · intro c hc hcp
          simp only [Nat.add_zero] at hcp ⊢
          have hleC := hc_bound c hcp
          by_cases hc0 : c = 0
          · subst hc0; rw [hval0, htarget]; exact vBase_clear_le hm a
          · by_cases hcC : c = C
            · subst hcC; rw [hvalC, htarget]; exact vBase_clear_le_pred hm ha_pos
            · exact Nat.le_of_lt (hmid_strict c (by omega) (by omega))
        · simp only [Nat.add_zero]
          -- Unique winner between c = 0 (if a even) and c = C (if a odd)
          by_cases haev : a % 2 = 0
          · have hwin : sumRange (fun c =>
                if choose (2 ^ r) (c * 2 ^ m) > 0 ∧
                   v2 (choose (2 ^ r) (c * 2 ^ m)) + pow2StridedVal m r (q - c) =
                   pow2StridedVal m r (2 ^ m * q)
                then 1 else 0) (q + 1) = 1 := by
              have hlt_a := (vBase_even_min hm a).2 haev (by omega)
              have ha_eq2 : 2 * (a / 2) = a := by omega
              rw [sumRange_single (k := 0) (by omega)]
              · rw [hval0, htarget, ha_eq2, Nat.zero_mul, choose_zero_right]
                simp
              · intro c hc hne0
                by_cases hcp : choose (2 ^ r) (c * 2 ^ m) > 0
                · have hleC := hc_bound c hcp
                  by_cases hcC : c = C
                  · subst hcC
                    rw [hvalC, htarget, ha_eq2]
                    have hne : vBase m (a - 1) ≠ vBase m a := by omega
                    simp [hne]
                  · have hlt := hmid_strict c (by omega) (by omega)
                    have hne : v2 (choose (2 ^ r) (c * 2 ^ m)) + pow2StridedVal m r (q - c) ≠
                               pow2StridedVal m r (2 ^ m * q) := by omega
                    simp [hne]
                · simp [hcp]
            rw [hwin]
          · have hwin : sumRange (fun c =>
                if choose (2 ^ r) (c * 2 ^ m) > 0 ∧
                   v2 (choose (2 ^ r) (c * 2 ^ m)) + pow2StridedVal m r (q - c) =
                   pow2StridedVal m r (2 ^ m * q)
                then 1 else 0) (q + 1) = 1 := by
              have ha_eq2 : 2 * (a / 2) = a - 1 := by omega
              have hlt_a : vBase m (a - 1) < vBase m a := by
                have h := (vBase_even_min hm (a - 1)).1 (by omega)
                have hs : a - 1 + 1 = a := by omega
                rwa [hs] at h
              rw [sumRange_single (k := C) (by omega)]
              · rw [hvalC, htarget, ha_eq2, hCB, choose_self]
                simp
              · intro c hc hneC
                by_cases hcp : choose (2 ^ r) (c * 2 ^ m) > 0
                · have hleC := hc_bound c hcp
                  by_cases hc0 : c = 0
                  · subst hc0
                    rw [hval0, htarget, ha_eq2]
                    have hne : vBase m a ≠ vBase m (a - 1) := by omega
                    simp [hne]
                  · have hlt := hmid_strict c (by omega) (by omega)
                    have hne : v2 (choose (2 ^ r) (c * 2 ^ m)) + pow2StridedVal m r (q - c) ≠
                               pow2StridedVal m r (2 ^ m * q) := by omega
                    simp [hne]
                · simp [hcp]
            rw [hwin]
      · -- SUBCASE 2b: rem = 0, 1 ≤ u < C (tie multiplicity 1 if (a % 2^m) even, 3 if (a % 2^m) odd!)
        have hu1 : 1 ≤ u := by omega
        have hu_le_q : u ≤ q := by omega
        have htarget : pow2StridedVal m r (2 ^ m * q) = (r - m - v2 u) + vBase m a := by
          rw [hn_eq, pow2StridedVal_divMod hb_lt]
          have hne : 2 ^ m * u ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (Nat.two_pow_pos m) hu1)
          simp only [hne, ↓reduceIte]
          rw [v2_pow_two_mul m (by omega)]
          have : v2 u < r - m := v2_lt_of_lt_pow (by omega) hu_lt
          omega
        -- Valuation at c = u equals target!
        have hval_u : v2 (choose (2 ^ r) (u * 2 ^ m)) + pow2StridedVal m r (q - u) =
            (r - m - v2 u) + vBase m a := by
          have hus_pos : 0 < u * 2 ^ m := Nat.mul_pos (by omega) (Nat.two_pow_pos m)
          have hus_lt : u * 2 ^ m < 2 ^ r := by
            rw [← hCB]; exact Nat.mul_lt_mul_of_pos_right hu_lt (Nat.two_pow_pos m)
          rw [v2_choose_pow2 hus_pos hus_lt, Nat.mul_comm u (2 ^ m), v2_pow_two_mul m (by omega)]
          have hqu : q - u = C * a := by rw [← hq_eq, Nat.add_sub_cancel]
          rw [hqu, pow2StridedVal_mul_C hm hrm a]
          have : v2 u < r - m := v2_lt_of_lt_pow (by omega) hu_lt
          omega
        -- Valuation at c = 0:
        have hval_0 : v2 (choose (2 ^ r) (0 * 2 ^ m)) + pow2StridedVal m r (q - 0) =
            (r - v2 u) + vBase m (a / 2 ^ m) := by
          simp only [Nat.zero_mul, Nat.sub_zero, choose_zero_right, v2_one, Nat.zero_add]
          rw [← hq_eq]
          exact pow2StridedVal_mul_C_add hm hrm a u (by omega) hu_lt
        -- Valuation at c = C (when a ≥ 1, i.e., C ≤ q):
        have hval_C : a ≥ 1 →
            v2 (choose (2 ^ r) (C * 2 ^ m)) + pow2StridedVal m r (q - C) =
            (r - v2 u) + vBase m ((a - 1) / 2 ^ m) := by
          intro ha1
          have hsubC : q - C = C * (a - 1) + u := by
            have ha' : a = (a - 1) + 1 := by omega
            have h1 : C * a = C * (a - 1) + C := by
              calc C * a = C * ((a - 1) + 1) := congrArg (C * ·) ha'
                _ = C * (a - 1) + C := by rw [Nat.mul_add, Nat.mul_one]
            omega
          rw [hCB, choose_self, v2_one, Nat.zero_add, hsubC]
          exact pow2StridedVal_mul_C_add hm hrm (a - 1) u (by omega) hu_lt
        -- Valuation at every middle c (1 ≤ c < C, c ≠ u, c ≤ q) is STRICTLY > target!
        have hmid_strict : ∀ c, 1 ≤ c → c < C → c ≠ u → c ≤ q →
            (r - m - v2 u) + vBase m a <
              v2 (choose (2 ^ r) (c * 2 ^ m)) + pow2StridedVal m r (q - c) := by
          intro c hc1 hcC hne hcq
          have hcs_pos : 0 < c * 2 ^ m := Nat.mul_pos (by omega) (Nat.two_pow_pos m)
          have hcs_lt : c * 2 ^ m < 2 ^ r := by
            rw [← hCB]; exact Nat.mul_lt_mul_of_pos_right hcC (Nat.two_pow_pos m)
          have hvc : v2 (choose (2 ^ r) (c * 2 ^ m)) = (r - m) - v2 c := by
            rw [v2_choose_pow2 hcs_pos hcs_lt, Nat.mul_comm, v2_pow_two_mul m (by omega)]
            have : v2 c < r - m := v2_lt_of_lt_pow (by omega) hcC
            omega
          rw [hvc]
          have hvclt : v2 c < r - m := v2_lt_of_lt_pow (by omega) hcC
          have hvult : v2 u < r - m := v2_lt_of_lt_pow (by omega) hu_lt
          cases Nat.lt_or_gt_of_ne hne with
          | inl hcu =>
            have hqc : q - c = C * a + (u - c) := by omega
            rw [hqc, pow2StridedVal_mul_C_add hm hrm a (u - c) (by omega) (by omega)]
            have hgap := v2_ultrametric_gap_lt (d := r - m) (by omega) hcC (by omega) hu_lt hcu
            have hcmp := vBase_cmp_m_add_div hm a
            have hle_a : vBase m a ≤ m + vBase m (a / 2 ^ m) := by
              by_cases hodd : (a % 2 ^ m) % 2 = 1
              · rw [hcmp.1 hodd]; exact Nat.le_refl _
              · have := hcmp.2 (by omega); omega
            have hvuc : v2 (u - c) < r - m := v2_lt_of_lt_pow (by omega) (by omega)
            omega
          | inr huc =>
            have ha1 : a ≥ 1 := Nat.pos_of_ne_zero (fun ha0 => by
              rw [ha0, Nat.mul_zero, Nat.zero_add] at hq_eq; omega)
            have hqc : q - c = C * (a - 1) + (C - (c - u)) := by
              have ha' : a = (a - 1) + 1 := by omega
              have h1 : C * a = C * (a - 1) + C := by
                calc C * a = C * ((a - 1) + 1) := congrArg (C * ·) ha'
                  _ = C * (a - 1) + C := by rw [Nat.mul_add, Nat.mul_one]
              omega
            rw [hqc, pow2StridedVal_mul_C_add hm hrm (a - 1) (C - (c - u)) (by omega) (by omega),
                v2_sub_pow_of_lt (by omega) (by omega)]
            have hgap := v2_ultrametric_gap_gt (d := r - m) (by omega) hcC (by omega) hu_lt huc
            have hvcu : v2 (c - u) < r - m := v2_lt_of_lt_pow (by omega) (by omega)
            have hle_a : vBase m a ≤ m + vBase m ((a - 1) / 2 ^ m) := by
              by_cases ha0 : a % 2 ^ m = 0
              · have hd : 2 ^ m * (a / 2 ^ m) = a := by
                  have := Nat.div_add_mod a (2 ^ m); omega
                have hq1 : a / 2 ^ m ≥ 1 := Nat.pos_of_ne_zero (fun hq0 => by
                  rw [hq0, Nat.mul_zero] at hd; omega)
                have hdiv_sub : (a - 1) / 2 ^ m = a / 2 ^ m - 1 := by
                  have hqeq : a / 2 ^ m = (a / 2 ^ m - 1) + 1 := by omega
                  have hmul : a - 1 = 2 ^ m * (a / 2 ^ m - 1) + (2 ^ m - 1) := by
                    have h2 : 2 ^ m * (a / 2 ^ m) = 2 ^ m * (a / 2 ^ m - 1) + 2 ^ m := by
                      calc 2 ^ m * (a / 2 ^ m) = 2 ^ m * ((a / 2 ^ m - 1) + 1) := congrArg (2 ^ m * ·) hqeq
                        _ = 2 ^ m * (a / 2 ^ m - 1) + 2 ^ m := by rw [Nat.mul_add, Nat.mul_one]
                    omega
                  rw [hmul, Nat.mul_add_div (Nat.two_pow_pos m),
                      Nat.div_eq_of_lt (by omega : 2 ^ m - 1 < 2 ^ m), Nat.add_zero]
                have hva : vBase m a = vBase m (2 * ((a / 2 ^ m) / 2)) := by
                  calc vBase m a = vBase m (2 ^ m * (a / 2 ^ m)) := congrArg (vBase m) hd.symm
                    _ = vBase m (2 * ((a / 2 ^ m) / 2)) := vBase_step_zero hm (a / 2 ^ m)
                rw [hdiv_sub, hva]
                have hclr := vBase_clear_le_pred hm hq1
                omega
              · have hdiv_eq : (a - 1) / 2 ^ m = a / 2 ^ m := by
                  have hd := Nat.div_add_mod a (2 ^ m)
                  have hrem_lt : a % 2 ^ m < 2 ^ m := Nat.mod_lt a (Nat.two_pow_pos m)
                  have hsub : a - 1 = 2 ^ m * (a / 2 ^ m) + (a % 2 ^ m - 1) := by omega
                  rw [hsub, Nat.mul_add_div (Nat.two_pow_pos m),
                      Nat.div_eq_of_lt (by omega : a % 2 ^ m - 1 < 2 ^ m), Nat.add_zero]
                rw [hdiv_eq]
                have hcmp := vBase_cmp_m_add_div hm a
                by_cases hodd : (a % 2 ^ m) % 2 = 1
                · rw [hcmp.1 hodd]; exact Nat.le_refl _
                · have := hcmp.2 (by omega); omega
            omega
        have hc_bound : ∀ c, choose (2 ^ r) (c * 2 ^ m) > 0 → c ≤ C := by
          intro c hcp
          by_cases hle : c ≤ C
          · exact hle
          · have : 2 ^ r < c * 2 ^ m := by
              rw [← hCB]; exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos m)
            have hz := choose_eq_zero_of_lt this
            omega
        have hvult : v2 u < r - m := v2_lt_of_lt_pow (by omega) hu_lt
        have hcmp := vBase_cmp_m_add_div hm a
        -- Check c = 0 and c = C comparison with target!
        have hc0_cmp :
            ((a % 2 ^ m) % 2 = 1 → (r - v2 u) + vBase m (a / 2 ^ m) = (r - m - v2 u) + vBase m a) ∧
            ((a % 2 ^ m) % 2 = 0 → (r - m - v2 u) + vBase m a < (r - v2 u) + vBase m (a / 2 ^ m)) := by
          constructor
          · intro hodd; rw [hcmp.1 hodd]; omega
          · intro hev; have := hcmp.2 hev; omega
        have hcC_cmp : a ≥ 1 →
            ((a % 2 ^ m) % 2 = 1 → (r - v2 u) + vBase m ((a - 1) / 2 ^ m) = (r - m - v2 u) + vBase m a) ∧
            ((a % 2 ^ m) % 2 = 0 → (r - m - v2 u) + vBase m a < (r - v2 u) + vBase m ((a - 1) / 2 ^ m)) := by
          intro ha1
          by_cases ha0 : a % 2 ^ m = 0
          · have hd : 2 ^ m * (a / 2 ^ m) = a := by have := Nat.div_add_mod a (2 ^ m); omega
            have hq1 : a / 2 ^ m ≥ 1 := Nat.pos_of_ne_zero (fun hq0 => by
              rw [hq0, Nat.mul_zero] at hd; omega)
            have hdiv_sub : (a - 1) / 2 ^ m = a / 2 ^ m - 1 := by
              have hqeq : a / 2 ^ m = (a / 2 ^ m - 1) + 1 := by omega
              have hmul : a - 1 = 2 ^ m * (a / 2 ^ m - 1) + (2 ^ m - 1) := by
                have h2 : 2 ^ m * (a / 2 ^ m) = 2 ^ m * (a / 2 ^ m - 1) + 2 ^ m := by
                  calc 2 ^ m * (a / 2 ^ m) = 2 ^ m * ((a / 2 ^ m - 1) + 1) := congrArg (2 ^ m * ·) hqeq
                    _ = 2 ^ m * (a / 2 ^ m - 1) + 2 ^ m := by rw [Nat.mul_add, Nat.mul_one]
                omega
              rw [hmul, Nat.mul_add_div (Nat.two_pow_pos m),
                  Nat.div_eq_of_lt (by omega : 2 ^ m - 1 < 2 ^ m), Nat.add_zero]
            have hva : vBase m a = vBase m (2 * ((a / 2 ^ m) / 2)) := by
              calc vBase m a = vBase m (2 ^ m * (a / 2 ^ m)) := congrArg (vBase m) hd.symm
                _ = vBase m (2 * ((a / 2 ^ m) / 2)) := vBase_step_zero hm (a / 2 ^ m)
            constructor
            · intro hodd; omega
            · intro _
              rw [hdiv_sub, hva]
              have hclr := vBase_clear_le_pred hm hq1
              omega
          · have hdiv_eq : (a - 1) / 2 ^ m = a / 2 ^ m := by
              have hd := Nat.div_add_mod a (2 ^ m)
              have hrem_lt : a % 2 ^ m < 2 ^ m := Nat.mod_lt a (Nat.two_pow_pos m)
              have hsub : a - 1 = 2 ^ m * (a / 2 ^ m) + (a % 2 ^ m - 1) := by omega
              rw [hsub, Nat.mul_add_div (Nat.two_pow_pos m),
                  Nat.div_eq_of_lt (by omega : a % 2 ^ m - 1 < 2 ^ m), Nat.add_zero]
            rw [hdiv_eq]
            exact hc0_cmp
        constructor
        · -- Lower bound hge
          intro c hcq hcp
          simp only [Nat.add_zero] at hcp ⊢
          rw [htarget]
          have hleC := hc_bound c hcp
          by_cases hc0 : c = 0
          · subst hc0; rw [hval_0]
            by_cases hodd : (a % 2 ^ m) % 2 = 1
            · rw [hc0_cmp.1 hodd]; exact Nat.le_refl _
            · exact Nat.le_of_lt (hc0_cmp.2 (by omega))
          · by_cases hcu : c = u
            · subst hcu; rw [hval_u]; exact Nat.le_refl _
            · by_cases hcC : c = C
              · subst hcC
                have ha1 : a ≥ 1 := Nat.pos_of_ne_zero (fun ha0 => by
                  rw [ha0, Nat.mul_zero, Nat.zero_add] at hq_eq; omega)
                rw [hval_C ha1]
                by_cases hodd : (a % 2 ^ m) % 2 = 1
                · rw [(hcC_cmp ha1).1 hodd]; exact Nat.le_refl _
                · exact Nat.le_of_lt ((hcC_cmp ha1).2 (by omega))
              · exact Nat.le_of_lt (hmid_strict c (by omega) (by omega) hcu hcq)
        · simp only [Nat.add_zero]
          -- Odd-parity minimizer count: 3 if (a % 2^m) odd, 1 if (a % 2^m) even!
          by_cases hodd : (a % 2 ^ m) % 2 = 1
          · have ha1 : a ≥ 1 := Nat.pos_of_ne_zero (fun ha0 => by
              rw [ha0] at hodd; simp at hodd)
            have hC_le_q : C ≤ q := by
              have : C * 1 ≤ C * a := Nat.mul_le_mul_left C ha1
              omega
            have hcount3 : sumRange (fun c =>
                if choose (2 ^ r) (c * 2 ^ m) > 0 ∧
                   v2 (choose (2 ^ r) (c * 2 ^ m)) + pow2StridedVal m r (q - c) =
                   pow2StridedVal m r (2 ^ m * q)
                then 1 else 0) (q + 1) = 3 := by
              apply sumRange_triple_one (u := u) (C := C) hu1 hu_lt (by omega)
              · rw [hval_0, htarget, hc0_cmp.1 hodd, Nat.zero_mul, choose_zero_right]
                simp
              · have hus_le : u * 2 ^ m ≤ 2 ^ r := by
                  rw [← hCB]; exact Nat.mul_le_mul_right _ (by omega)
                rw [hval_u, htarget]
                simp [choose_pos hus_le]
              · rw [hval_C ha1, htarget, (hcC_cmp ha1).1 hodd, hCB, choose_self]
                simp
              · intro c hc hne0 hneu hneC
                by_cases hcp : choose (2 ^ r) (c * 2 ^ m) > 0
                · have hleC := hc_bound c hcp
                  have hlt := hmid_strict c (by omega) (by omega) hneu (by omega)
                  rw [htarget]
                  have hne : v2 (choose (2 ^ r) (c * 2 ^ m)) + pow2StridedVal m r (q - c) ≠
                             (r - m - v2 u) + vBase m a := by omega
                  simp [hne]
                · simp [hcp]
            rw [hcount3]
          · have hev : (a % 2 ^ m) % 2 = 0 := by omega
            have hcount1 : sumRange (fun c =>
                if choose (2 ^ r) (c * 2 ^ m) > 0 ∧
                   v2 (choose (2 ^ r) (c * 2 ^ m)) + pow2StridedVal m r (q - c) =
                   pow2StridedVal m r (2 ^ m * q)
                then 1 else 0) (q + 1) = 1 := by
              rw [sumRange_single (k := u) (by omega)]
              · have hus_le : u * 2 ^ m ≤ 2 ^ r := by
                  rw [← hCB]; exact Nat.mul_le_mul_right _ (by omega)
                rw [hval_u, htarget]
                simp [choose_pos hus_le]
              · intro c hc hneu
                by_cases hcp : choose (2 ^ r) (c * 2 ^ m) > 0
                · have hleC := hc_bound c hcp
                  rw [htarget]
                  by_cases hc0 : c = 0
                  · subst hc0; rw [hval_0]
                    have hlt := hc0_cmp.2 hev
                    have hne : (r - v2 u) + vBase m (a / 2 ^ m) ≠ (r - m - v2 u) + vBase m a := by omega
                    simp [hne]
                  · by_cases hcC : c = C
                    · subst hcC
                      have ha1 : a ≥ 1 := Nat.pos_of_ne_zero (fun ha0 => by
                        rw [ha0, Nat.mul_zero, Nat.zero_add] at hq_eq; omega)
                      rw [hval_C ha1]
                      have hlt := (hcC_cmp ha1).2 hev
                      have hne : (r - v2 u) + vBase m ((a - 1) / 2 ^ m) ≠ (r - m - v2 u) + vBase m a := by omega
                      simp [hne]
                    · have hlt := hmid_strict c (by omega) (by omega) hneu (by omega)
                      have hne : v2 (choose (2 ^ r) (c * 2 ^ m)) + pow2StridedVal m r (q - c) ≠
                                 (r - m - v2 u) + vBase m a := by omega
                      simp [hne]
                · simp [hcp]
            rw [hcount1]
    · -- CASE 1: 1 ≤ rem < 2^m (strict unique winner at c = u!)
      have hrem1 : 1 ≤ rem := by omega
      have hu_le_q : u ≤ q := by omega
      have htarget : pow2StridedVal m r (2 ^ m * q + rem) = (r - v2 rem) + vBase m a := by
        rw [hn_eq, pow2StridedVal_divMod hb_lt]
        have hne : 2 ^ m * u + rem ≠ 0 := by omega
        simp only [hne, ↓reduceIte]
        rw [v2_add_pow_mul_of_lt (by omega) hrem]
      have hc_bound : ∀ c, choose (2 ^ r) (c * 2 ^ m + rem) > 0 → c < C := by
        intro c hcp
        cases Nat.lt_or_ge c C with
        | inl hlt => exact hlt
        | inr hge =>
          have h1 : 2 ^ r < c * 2 ^ m + rem := by
            have : C * 2 ^ m ≤ c * 2 ^ m := Nat.mul_le_mul_right _ hge
            omega
          have hz := choose_eq_zero_of_lt h1
          omega
      have hbin_v2 : ∀ c < C, v2 (choose (2 ^ r) (c * 2 ^ m + rem)) = r - v2 rem := by
        intro c hcC
        have hlt : c * 2 ^ m + rem < 2 ^ r := by
          have h1 : (c + 1) * 2 ^ m ≤ C * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul, hCB] at h1
          omega
        rw [v2_choose_pow2 (by omega) hlt, Nat.mul_comm c (2 ^ m),
            v2_add_pow_mul_of_lt (by omega) hrem]
      have hval_u : v2 (choose (2 ^ r) (u * 2 ^ m + rem)) + pow2StridedVal m r (q - u) =
          (r - v2 rem) + vBase m a := by
        rw [hbin_v2 u hu_lt]
        have hqu : q - u = C * a := by rw [← hq_eq, Nat.add_sub_cancel]
        rw [hqu, pow2StridedVal_mul_C hm hrm a]
      -- Show every c ≠ u (c < C, c ≤ q) has strictly larger pow2StridedVal m r (q - c) > vBase m a!
      have hother_strict : ∀ c, c < C → c ≠ u → c ≤ q →
          vBase m a < pow2StridedVal m r (q - c) := by
        intro c hcC hne hcq
        cases Nat.lt_or_gt_of_ne hne with
        | inl hcu =>
          have hqc : q - c = C * a + (u - c) := by omega
          rw [hqc, pow2StridedVal_mul_C_add hm hrm a (u - c) (by omega) (by omega)]
          have hvuc : v2 (u - c) < r - m := v2_lt_of_lt_pow (by omega) (by omega)
          have hcmp := vBase_cmp_m_add_div hm a
          have hle_a : vBase m a ≤ m + vBase m (a / 2 ^ m) := by
            by_cases hodd : (a % 2 ^ m) % 2 = 1
            · rw [hcmp.1 hodd]; exact Nat.le_refl _
            · have := hcmp.2 (by omega); omega
          omega
        | inr huc =>
          have ha1 : a ≥ 1 := Nat.pos_of_ne_zero (fun ha0 => by
            rw [ha0, Nat.mul_zero, Nat.zero_add] at hq_eq; omega)
          have hqc : q - c = C * (a - 1) + (C - (c - u)) := by
            have ha' : a = (a - 1) + 1 := by omega
            have h1 : C * a = C * (a - 1) + C := by
              calc C * a = C * ((a - 1) + 1) := congrArg (C * ·) ha'
                _ = C * (a - 1) + C := by rw [Nat.mul_add, Nat.mul_one]
            omega
          rw [hqc, pow2StridedVal_mul_C_add hm hrm (a - 1) (C - (c - u)) (by omega) (by omega),
              v2_sub_pow_of_lt (by omega) (by omega)]
          have hvcu : v2 (c - u) < r - m := v2_lt_of_lt_pow (by omega) (by omega)
          have hle_a : vBase m a ≤ m + vBase m ((a - 1) / 2 ^ m) := by
            by_cases ha0 : a % 2 ^ m = 0
            · have hd : 2 ^ m * (a / 2 ^ m) = a := by have := Nat.div_add_mod a (2 ^ m); omega
              have hq1 : a / 2 ^ m ≥ 1 := Nat.pos_of_ne_zero (fun hq0 => by
                rw [hq0, Nat.mul_zero] at hd; omega)
              have hdiv_sub : (a - 1) / 2 ^ m = a / 2 ^ m - 1 := by
                have hqeq : a / 2 ^ m = (a / 2 ^ m - 1) + 1 := by omega
                have hmul : a - 1 = 2 ^ m * (a / 2 ^ m - 1) + (2 ^ m - 1) := by
                  have h2 : 2 ^ m * (a / 2 ^ m) = 2 ^ m * (a / 2 ^ m - 1) + 2 ^ m := by
                    calc 2 ^ m * (a / 2 ^ m) = 2 ^ m * ((a / 2 ^ m - 1) + 1) := congrArg (2 ^ m * ·) hqeq
                      _ = 2 ^ m * (a / 2 ^ m - 1) + 2 ^ m := by rw [Nat.mul_add, Nat.mul_one]
                  omega
                rw [hmul, Nat.mul_add_div (Nat.two_pow_pos m),
                    Nat.div_eq_of_lt (by omega : 2 ^ m - 1 < 2 ^ m), Nat.add_zero]
              have hva : vBase m a = vBase m (2 * ((a / 2 ^ m) / 2)) := by
                calc vBase m a = vBase m (2 ^ m * (a / 2 ^ m)) := congrArg (vBase m) hd.symm
                  _ = vBase m (2 * ((a / 2 ^ m) / 2)) := vBase_step_zero hm (a / 2 ^ m)
              rw [hdiv_sub, hva]
              have hclr := vBase_clear_le_pred hm hq1
              omega
            · have hdiv_eq : (a - 1) / 2 ^ m = a / 2 ^ m := by
                have hd := Nat.div_add_mod a (2 ^ m)
                have hrem_lt : a % 2 ^ m < 2 ^ m := Nat.mod_lt a (Nat.two_pow_pos m)
                have hsub : a - 1 = 2 ^ m * (a / 2 ^ m) + (a % 2 ^ m - 1) := by omega
                rw [hsub, Nat.mul_add_div (Nat.two_pow_pos m),
                    Nat.div_eq_of_lt (by omega : a % 2 ^ m - 1 < 2 ^ m), Nat.add_zero]
              rw [hdiv_eq]
              have hcmp := vBase_cmp_m_add_div hm a
              by_cases hodd : (a % 2 ^ m) % 2 = 1
              · rw [hcmp.1 hodd]; exact Nat.le_refl _
              · have := hcmp.2 (by omega); omega
          omega
      constructor
      · intro c hcq hcp
        rw [htarget]
        have hcC := hc_bound c hcp
        by_cases hcu : c = u
        · subst hcu; rw [hval_u]; exact Nat.le_refl _
        · rw [hbin_v2 c hcC]
          have := hother_strict c hcC hcu hcq
          omega
      · have hcount1 : sumRange (fun c =>
            if choose (2 ^ r) (c * 2 ^ m + rem) > 0 ∧
               v2 (choose (2 ^ r) (c * 2 ^ m + rem)) + pow2StridedVal m r (q - c) =
               pow2StridedVal m r (2 ^ m * q + rem)
            then 1 else 0) (q + 1) = 1 := by
          rw [sumRange_single (k := u) (by omega)]
          · have hlt : u * 2 ^ m + rem ≤ 2 ^ r := by
              have h1 : (u + 1) * 2 ^ m ≤ C * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
              rw [Nat.add_mul, Nat.one_mul, hCB] at h1
              omega
            rw [hval_u, htarget]
            simp [choose_pos hlt]
          · intro c hc hneu
            by_cases hcp : choose (2 ^ r) (c * 2 ^ m + rem) > 0
            · have hcC := hc_bound c hcp
              rw [htarget, hbin_v2 c hcC]
              have hlt := hother_strict c hcC hneu (by omega)
              have hne : pow2StridedVal m r (q - c) ≠ vBase m a := by omega
              simp [hne]
            · simp [hcp]
        rw [hcount1]
  exact ultrametric_odd_parity_lift (2 ^ m) hB2
    (fun c rem => choose (2 ^ r) (c * 2 ^ m + rem))
    (stridedRepCount m (2 ^ r)) (pow2StridedVal m r)
    (stridedRepCount_zero m (2 ^ r) hm) (pow2StridedVal_zero m r)
    (fun q rem hrem => stridedRepCount_slice m (2 ^ r) hm q rem hrem)
    (fun q rem hrem hpos => (hlocal q rem hrem hpos).1)
    (fun q rem hrem hpos => (hlocal q rem hrem hpos).2)

/-- **COROLLARY 2A (Exact `r`-Invariance / Stability Law):**
    For ALL strides `m ≥ 1`, ALL powers `r1, r2 ≥ m`, and ALL `a : Nat`,
    `v2 (r_{2^r1 S_m}(2^r1 * a)) = v2 (r_{2^r2 S_m}(2^r2 * a))`. -/
theorem pow2_strided_r_invariance {m r1 r2 : Nat} (hm : m ≥ 1) (hr1 : r1 ≥ m) (hr2 : r2 ≥ m) (a : Nat) :
    v2 (stridedRepCount m (2 ^ r1) (2 ^ r1 * a)) = v2 (stridedRepCount m (2 ^ r2) (2 ^ r2 * a)) := by
  rw [(pow2_strided_kummer_v2 hm hr1 (2 ^ r1 * a)).2,
      (pow2_strided_kummer_v2 hm hr2 (2 ^ r2 * a)).2]
  have h1 := pow2StridedVal_divMod (m := m) (r := r1) (a := a) (b := 0) (Nat.two_pow_pos r1)
  have h2 := pow2StridedVal_divMod (m := m) (r := r2) (a := a) (b := 0) (Nat.two_pow_pos r2)
  simp only [Nat.add_zero, ↓reduceIte] at h1 h2
  rw [h1, h2]

/-- Exact characterization of when `vBase m (2 * (a / 2)) = 0`: iff `a ∈ S_m`! -/
theorem vBase_clear_eq_zero_iff {m : Nat} (hm : m ≥ 1) :
    ∀ a : Nat, vBase m (2 * (a / 2)) = 0 ↔ InStrided m a := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    have hB2 : 2 ^ m ≥ 2 := by
      have := Nat.pow_le_pow_right (n := 2) (by omega) hm
      omega
    have hBeven : 2 ^ m % 2 = 0 := by
      have hm1 : m = (m - 1) + 1 := by omega
      have hpow : 2 ^ m = 2 ^ (m - 1) * 2 := by
        calc 2 ^ m = 2 ^ ((m - 1) + 1) := congrArg (2 ^ ·) hm1
          _ = 2 ^ (m - 1) * 2 := Nat.pow_succ _ _
      omega
    by_cases ha0 : a = 0
    · subst ha0
      simp only [Nat.zero_div, Nat.mul_zero, vBase_zero, true_iff]
      intro i hi; simp at hi
    · let q := a / 2 ^ m
      let rho := a % 2 ^ m
      have hrho : rho < 2 ^ m := Nat.mod_lt a (by omega)
      have ha_eq : 2 ^ m * q + rho = a := Nat.div_add_mod a (2 ^ m)
      have hq_lt : q < a := Nat.div_lt_self (by omega) hB2
      have hstr : InStrided m a ↔ (rho = 0 ∨ rho = 1) ∧ InStrided m q := by
        unfold InStrided
        rw [← inMaskB_iff hm, ← inMaskB_iff hm, ← ha_eq, inMaskB_slice hm hrho,
            Bool.and_eq_true, inDigitMaskB_one_iff hrho]
      rw [hstr]
      have hclear : 2 * (a / 2) = 2 ^ m * q + 2 * (rho / 2) := by
        have h1 : 2 ^ m = 2 * (2 ^ m / 2) := by omega
        have h2 : a = 2 * (2 ^ m / 2 * q + rho / 2) + rho % 2 := by
          have : 2 ^ m * q = 2 * (2 ^ m / 2 * q) := by
            calc 2 ^ m * q = (2 * (2 ^ m / 2)) * q := congrArg (· * q) h1
              _ = 2 * (2 ^ m / 2 * q) := Nat.mul_assoc _ _ _
          omega
        have hdiv2 : a / 2 = 2 ^ m / 2 * q + rho / 2 := by omega
        have hmul2 : 2 * (a / 2) = 2 * (2 ^ m / 2 * q) + 2 * (rho / 2) := by
          rw [hdiv2, Nat.mul_add]
        have h3 : 2 * (2 ^ m / 2 * q) = 2 ^ m * q := by
          rw [← Nat.mul_assoc, ← h1]
        omega
      rw [hclear]
      by_cases hrho01 : rho = 0 ∨ rho = 1
      · have hrho2 : 2 * (rho / 2) = 0 := by omega
        rw [hrho2, Nat.add_zero, vBase_step_zero hm q, ih q hq_lt]
        simp [hrho01]
      · have hrho2_pos : 1 ≤ 2 * (rho / 2) := by omega
        have hrho2_lt : 2 * (rho / 2) < 2 ^ m := by omega
        rw [vBase_step_pos hm q (2 * (rho / 2)) hrho2_pos hrho2_lt]
        have hvlt : v2 (2 * (rho / 2)) < m := v2_lt_of_lt_pow (by omega) hrho2_lt
        constructor
        · intro h0; omega
        · intro ⟨h01, _⟩; exact absurd h01 hrho01

/-- **COROLLARY 2B (Exact Oddness Characterization for ALL `m ≥ 1, r ≥ m, n : Nat`):**
    `r_{2^r S_m}(n)` is odd IF AND ONLY IF `2^r ∣ n` and `n / 2^r ∈ S_m`! -/
theorem pow2_strided_odd_iff {m r : Nat} (hm : m ≥ 1) (hrm : r ≥ m) (n : Nat) :
    stridedRepCount m (2 ^ r) n % 2 = 1 ↔ (2 ^ r ∣ n ∧ InStrided m (n / 2 ^ r)) := by
  have ⟨hpos, hv⟩ := pow2_strided_kummer_v2 hm hrm n
  have hodd_iff_v0 : stridedRepCount m (2 ^ r) n % 2 = 1 ↔ v2 (stridedRepCount m (2 ^ r) n) = 0 := by
    constructor
    · exact v2_odd
    · intro hv0
      obtain ⟨u, hu, heq⟩ := exists_odd_part _ hpos
      rw [hv0, Nat.pow_zero, Nat.one_mul] at heq
      rw [heq]; exact hu
  rw [hodd_iff_v0, hv]
  unfold pow2StridedVal
  by_cases hmod : n % 2 ^ r = 0
  · simp only [hmod, ↓reduceIte]
    rw [vBase_clear_eq_zero_iff hm (n / 2 ^ r)]
    have hdvd : 2 ^ r ∣ n := Nat.dvd_of_mod_eq_zero hmod
    simp [hdvd]
  · simp only [hmod, ↓reduceIte]
    have hlt : v2 (n % 2 ^ r) < r := v2_lt_of_lt_pow (by omega) (Nat.mod_lt n (Nat.two_pow_pos r))
    have hndvd : ¬(2 ^ r ∣ n) := by
      intro hd; have := Nat.mod_eq_zero_of_dvd hd; contradiction
    constructor
    · intro h0; omega
    · intro ⟨hd, _⟩; exact absurd hd hndvd

/-! ## Layer 6: Kernel-Checked Non-Vacuity Witnesses, Sharpness Counterexamples & Axiom Verification -/

/-- Non-vacuity witness 1: `InStrided 2 21` (`21 = 1 + 4 + 16 = 0b10101 ∈ S_2`) and `¬InStrided 2 2`. -/
theorem witness_inStrided_21 : InStrided 2 21 :=
  (inMaskB_iff (by decide : 2 ≥ 1)).1 (by decide)

theorem witness_not_inStrided_2 : ¬InStrided 2 2 := by
  unfold InStrided
  rw [← inMaskB_iff (by decide : 2 ≥ 1)]
  decide

/-- Non-vacuity witness 2: Concrete values of `stridedRepCount` showing non-trivial multiplicity
    and exact valuation match with Theorem 1 / Corollary 1A / Theorem 2. -/
theorem witness_values :
    stridedRepCount 2 4 4 = 5 ∧
    stridedRepCount 2 6 7 = 120 ∧
    stridedRepCount 2 8 12 = 2024 ∧
    maskRepCount 2 [1, 1, 1, 3] 5 = 20 := by
  decide

/-- Non-vacuity witness 3: Theorem 2 genuinely hits 3-way ties (tie multiplicity 3, odd -> no cancellation)!
    At `m = 2, r = 3 (K = 8), n = 12 (q = 3, rem = 0)`, the three recurrence terms are
    `C(8,0)*r(3) = 56`, `C(8,4)*r(2) = 70*28 = 1960`, `C(8,8)*r(1) = 8`, ALL with `v2 = 3`,
    summing to `2024` which still has `v2 = 3`! -/
theorem witness_three_way_tie_survives :
    choose 8 0 * stridedRepCount 2 8 3 = 56 ∧
    choose 8 4 * stridedRepCount 2 8 2 = 1960 ∧
    choose 8 8 * stridedRepCount 2 8 1 = 8 ∧
    v2Exec 56 = 3 ∧ v2Exec 1960 = 3 ∧ v2Exec 8 = 3 ∧
    stridedRepCount 2 8 12 = 2024 ∧ v2Exec 2024 = 3 := by
  decide

/-- **Sharpness Counterexample 1 (Lower Boundary `k < 2^m`):**
    Just below `k = 2^m` (at `m = 2, k = 2 = 2^1`), `r_{2 S_2}(3) = 0`: positivity & valuation law fail! -/
theorem sharpness_below_pow2 : stridedRepCount 2 2 3 = 0 := by decide

/-- **Sharpness Counterexample 2 (Odd `k = 2^m + 1` in Theorem 1):**
    At `m = 2, k = 5` (odd, strictly between `4` and `6`), at `n = 4`:
    both recurrence terms `C(5,0)*r(1) = 5` and `C(5,4)*r(0) = 5` have `v2 = 0`, causing a
    2-way tie with 2-adic cancellation (`stridedRepCount 2 5 4 = 10`, `v2 10 = 1 > 0`)! -/
theorem sharpness_odd_k_cancellation :
    choose 5 0 * stridedRepCount 2 5 1 = 5 ∧
    choose 5 4 * stridedRepCount 2 5 0 = 5 ∧
    v2Exec 5 = 0 ∧
    stridedRepCount 2 5 4 = 10 ∧ v2Exec 10 = 1 := by
  decide

/-- **Sharpness Counterexample 3 (Even `k > 2^(m+1) - 2`, non-power-of-two):**
    At `m = 2, k = 10` (even, `10 > 6`, not a power of 2), at `n = 4`:
    terms `C(10,0)*r(1) = 10` and `C(10,4)*r(0) = 210` both have `v2 = 1`, causing a
    2-way tie with 2-adic cancellation (`stridedRepCount 2 10 4 = 220`, `v2 220 = 2 > 1`)! -/
theorem sharpness_above_window_cancellation :
    choose 10 0 * stridedRepCount 2 10 1 = 10 ∧
    choose 10 4 * stridedRepCount 2 10 0 = 210 ∧
    v2Exec 10 = 1 ∧ v2Exec 210 = 1 ∧
    stridedRepCount 2 10 4 = 220 ∧ v2Exec 220 = 2 := by
  decide

end StridedBitsetEngine
