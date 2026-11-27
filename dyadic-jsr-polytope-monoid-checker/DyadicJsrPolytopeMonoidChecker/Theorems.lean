import DyadicJsrPolytopeMonoidChecker.Defs

namespace DyadicMonoidEngine
theorem iabs_nonneg (x : Int) : 0 ≤ iabs x := by
  unfold iabs; split <;> omega

theorem le_iabs (x : Int) : x ≤ iabs x := by
  unfold iabs; split <;> omega

theorem neg_le_iabs (x : Int) : -x ≤ iabs x := by
  unfold iabs; split <;> omega

theorem iabs_le_iff (x y : Int) : iabs x ≤ y ↔ (-y ≤ x ∧ x ≤ y) := by
  unfold iabs; split <;> omega

theorem iabs_add_le (x y : Int) : iabs (x + y) ≤ iabs x + iabs y := by
  unfold iabs; split <;> split <;> split <;> omega

theorem iabs_mul (x y : Int) : iabs (x * y) = iabs x * iabs y := by
  unfold iabs
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · have hxy : 0 ≤ x * y := Int.mul_nonneg hx hy
    simp [hx, hy, hxy]
  · have hy' : y < 0 := Int.lt_of_not_ge hy
    by_cases hx0 : x = 0
    · subst hx0; simp
    · have hxy : ¬(0 ≤ x * y) := by
        have h1 : 0 < x := by omega
        have h2 : 0 < -y := by omega
        have h3 : 0 < x * (-y) := Int.mul_pos h1 h2
        rw [Int.mul_neg] at h3; omega
      simp [hx, hy, hxy, Int.mul_neg]
  · have hx' : x < 0 := Int.lt_of_not_ge hx
    by_cases hy0 : y = 0
    · subst hy0; simp
    · have hxy : ¬(0 ≤ x * y) := by
        have h1 : 0 < -x := by omega
        have h2 : 0 < y := by omega
        have h3 : 0 < (-x) * y := Int.mul_pos h1 h2
        rw [Int.neg_mul] at h3; omega
      simp [hx, hy, hxy, Int.neg_mul]
  · have hxy : 0 ≤ x * y := by
      have h1 : 0 ≤ -x := by omega
      have h2 : 0 ≤ -y := by omega
      have h3 : 0 ≤ (-x) * (-y) := Int.mul_nonneg h1 h2
      rw [Int.neg_mul_neg] at h3; exact h3
    simp [hx, hy, hxy, Int.neg_mul_neg]

theorem iabs_natCast (n : Nat) : iabs (n : Int) = (n : Int) := by
  unfold iabs; split <;> omega

theorem iabs_zero : iabs 0 = 0 := rfl

theorem iabs_eq_self {x : Int} (h : 0 ≤ x) : iabs x = x := by
  unfold iabs; simp [h]

theorem iabs_pow (x : Int) : ∀ n : Nat, iabs (x ^ n) = (iabs x) ^ n
  | 0 => by simp [Int.pow_zero, iabs]
  | n + 1 => by simp [Int.pow_succ, iabs_mul, iabs_pow x n]

theorem int_pow_nonneg {a : Int} (ha : 0 ≤ a) : ∀ n : Nat, 0 ≤ a ^ n
  | 0 => by simp [Int.pow_zero]
  | n + 1 => by rw [Int.pow_succ]; exact Int.mul_nonneg (int_pow_nonneg ha n) ha

theorem int_max_eq_right {a b : Int} (h : a ≤ b) : max a b = b := by omega
theorem int_max_eq_left {a b : Int} (h : b ≤ a) : max a b = a := by omega

theorem pow2Int_pos (n : Nat) : 0 < pow2Int n := by
  unfold pow2Int
  have h : 0 < 2 ^ n := Nat.pow_pos (by omega)
  omega

theorem pow2Int_nonneg (n : Nat) : 0 ≤ pow2Int n := by
  have h := pow2Int_pos n; omega

theorem pow2Int_zero : pow2Int 0 = 1 := rfl

theorem pow2Int_add (a b : Nat) : pow2Int (a + b) = pow2Int a * pow2Int b := by
  unfold pow2Int
  rw [Nat.pow_add, Int.natCast_mul]

theorem pow2Int_mul (a b : Nat) : pow2Int (a * b) = (pow2Int a) ^ b := by
  induction b with
  | zero => simp [pow2Int, Int.pow_zero]
  | succ k ih => rw [Nat.mul_succ, pow2Int_add, ih, Int.pow_succ]

namespace Dyad
theorem pow_num (a : Dyad) : ∀ n : Nat, (pow a n).num = a.num ^ n
  | 0 => by simp [pow, one, Int.pow_zero]
  | n + 1 => by simp [pow, mul, pow_num a n, Int.pow_succ]

theorem pow_shift (a : Dyad) : ∀ n : Nat, (pow a n).shift = a.shift * n
  | 0 => rfl
  | n + 1 => by simp [pow, mul, pow_shift a n, Nat.mul_succ]

theorem eqv_refl (a : Dyad) : eqv a a := rfl

theorem eqv_symm {a b : Dyad} (h : eqv a b) : eqv b a := h.symm

theorem eqv_trans {a b c : Dyad} (h1 : eqv a b) (h2 : eqv b c) : eqv a c := by
  unfold eqv at *
  have hb : 0 < pow2Int b.shift := pow2Int_pos b.shift
  have hmul : (a.num * pow2Int c.shift) * pow2Int b.shift = (c.num * pow2Int a.shift) * pow2Int b.shift := by
    calc (a.num * pow2Int c.shift) * pow2Int b.shift
        = (a.num * pow2Int b.shift) * pow2Int c.shift := by ac_rfl
      _ = (b.num * pow2Int a.shift) * pow2Int c.shift := by rw [h1]
      _ = (b.num * pow2Int c.shift) * pow2Int a.shift := by ac_rfl
      _ = (c.num * pow2Int b.shift) * pow2Int a.shift := by rw [h2]
      _ = (c.num * pow2Int a.shift) * pow2Int b.shift := by ac_rfl
  exact Int.eq_of_mul_eq_mul_right (by omega) hmul

theorem le_refl (a : Dyad) : le a a := Int.le_refl _

theorem le_trans {a b c : Dyad} (h1 : le a b) (h2 : le b c) : le a c := by
  unfold le at *
  have ha : 0 ≤ pow2Int a.shift := pow2Int_nonneg a.shift
  have hb : 0 < pow2Int b.shift := pow2Int_pos b.shift
  have hc : 0 ≤ pow2Int c.shift := pow2Int_nonneg c.shift
  have h1' := Int.mul_le_mul_of_nonneg_right h1 hc
  have h2' := Int.mul_le_mul_of_nonneg_right h2 ha
  have hmid : (a.num * pow2Int c.shift) * pow2Int b.shift ≤ (c.num * pow2Int a.shift) * pow2Int b.shift := by
    calc (a.num * pow2Int c.shift) * pow2Int b.shift
        = (a.num * pow2Int b.shift) * pow2Int c.shift := by ac_rfl
      _ ≤ (b.num * pow2Int a.shift) * pow2Int c.shift := h1'
      _ = (b.num * pow2Int c.shift) * pow2Int a.shift := by ac_rfl
      _ ≤ (c.num * pow2Int b.shift) * pow2Int a.shift := h2'
      _ = (c.num * pow2Int a.shift) * pow2Int b.shift := by ac_rfl
  exact Int.le_of_mul_le_mul_right hmid hb

theorem lt_of_le_of_lt {a b c : Dyad} (h1 : le a b) (h2 : lt b c) : lt a c := by
  unfold le lt at *
  have ha : 0 < pow2Int a.shift := pow2Int_pos a.shift
  have hb : 0 < pow2Int b.shift := pow2Int_pos b.shift
  have hc : 0 ≤ pow2Int c.shift := pow2Int_nonneg c.shift
  have h1' := Int.mul_le_mul_of_nonneg_right h1 hc
  have h2' := Int.mul_lt_mul_of_pos_right h2 ha
  have hmid : (a.num * pow2Int c.shift) * pow2Int b.shift < (c.num * pow2Int a.shift) * pow2Int b.shift := by
    calc (a.num * pow2Int c.shift) * pow2Int b.shift
        = (a.num * pow2Int b.shift) * pow2Int c.shift := by ac_rfl
      _ ≤ (b.num * pow2Int a.shift) * pow2Int c.shift := h1'
      _ = (b.num * pow2Int c.shift) * pow2Int a.shift := by ac_rfl
      _ < (c.num * pow2Int b.shift) * pow2Int a.shift := h2'
      _ = (c.num * pow2Int a.shift) * pow2Int b.shift := by ac_rfl
  exact Int.lt_of_mul_lt_mul_right hmid (by omega)

theorem lt_of_lt_of_le {a b c : Dyad} (h1 : lt a b) (h2 : le b c) : lt a c := by
  unfold le lt at *
  have ha : 0 ≤ pow2Int a.shift := pow2Int_nonneg a.shift
  have hb : 0 < pow2Int b.shift := pow2Int_pos b.shift
  have hc : 0 < pow2Int c.shift := pow2Int_pos c.shift
  have h1' := Int.mul_lt_mul_of_pos_right h1 hc
  have h2' := Int.mul_le_mul_of_nonneg_right h2 ha
  have hmid : (a.num * pow2Int c.shift) * pow2Int b.shift < (c.num * pow2Int a.shift) * pow2Int b.shift := by
    calc (a.num * pow2Int c.shift) * pow2Int b.shift
        = (a.num * pow2Int b.shift) * pow2Int c.shift := by ac_rfl
      _ < (b.num * pow2Int a.shift) * pow2Int c.shift := h1'
      _ = (b.num * pow2Int c.shift) * pow2Int a.shift := by ac_rfl
      _ ≤ (c.num * pow2Int b.shift) * pow2Int a.shift := h2'
      _ = (c.num * pow2Int a.shift) * pow2Int b.shift := by ac_rfl
  exact Int.lt_of_mul_lt_mul_right hmid (by omega)

theorem le_of_eqv_left {a a' b : Dyad} (heq : eqv a a') (hle : le a' b) : le a b :=
  le_trans (Int.le_of_eq heq) hle

theorem le_of_eqv_right {a b b' : Dyad} (hle : le a b') (heq : eqv b' b) : le a b :=
  le_trans hle (Int.le_of_eq heq)

theorem abs_eqv_congr {a b : Dyad} (h : eqv a b) : eqv (abs a) (abs b) := by
  unfold eqv abs at *
  have h1 : iabs (a.num * pow2Int b.shift) = iabs (b.num * pow2Int a.shift) := by rw [h]
  rw [iabs_mul, iabs_mul, iabs_eq_self (pow2Int_nonneg _), iabs_eq_self (pow2Int_nonneg _)] at h1
  exact h1

theorem add_eqv_congr {a a' b b' : Dyad} (ha : eqv a a') (hb : eqv b b') :
    eqv (add a b) (add a' b') := by
  unfold eqv add at *
  rw [pow2Int_add, pow2Int_add, Int.add_mul, Int.add_mul]
  have t1 : (a.num * pow2Int b.shift) * (pow2Int a'.shift * pow2Int b'.shift) =
            (a'.num * pow2Int b'.shift) * (pow2Int a.shift * pow2Int b.shift) := by
    calc (a.num * pow2Int b.shift) * (pow2Int a'.shift * pow2Int b'.shift)
        = (a.num * pow2Int a'.shift) * (pow2Int b.shift * pow2Int b'.shift) := by ac_rfl
      _ = (a'.num * pow2Int a.shift) * (pow2Int b.shift * pow2Int b'.shift) := by rw [ha]
      _ = (a'.num * pow2Int b'.shift) * (pow2Int a.shift * pow2Int b.shift) := by ac_rfl
  have t2 : (b.num * pow2Int a.shift) * (pow2Int a'.shift * pow2Int b'.shift) =
            (b'.num * pow2Int a'.shift) * (pow2Int a.shift * pow2Int b.shift) := by
    calc (b.num * pow2Int a.shift) * (pow2Int a'.shift * pow2Int b'.shift)
        = (b.num * pow2Int b'.shift) * (pow2Int a.shift * pow2Int a'.shift) := by ac_rfl
      _ = (b'.num * pow2Int b.shift) * (pow2Int a.shift * pow2Int a'.shift) := by rw [hb]
      _ = (b'.num * pow2Int a'.shift) * (pow2Int a.shift * pow2Int b.shift) := by ac_rfl
  rw [t1, t2]

theorem mul_eqv_congr {a a' b b' : Dyad} (ha : eqv a a') (hb : eqv b b') :
    eqv (mul a b) (mul a' b') := by
  unfold eqv mul at *
  rw [pow2Int_add, pow2Int_add]
  calc (a.num * b.num) * (pow2Int a'.shift * pow2Int b'.shift)
      = (a.num * pow2Int a'.shift) * (b.num * pow2Int b'.shift) := by ac_rfl
    _ = (a'.num * pow2Int a.shift) * (b'.num * pow2Int b.shift) := by rw [ha, hb]
    _ = (a'.num * b'.num) * (pow2Int a.shift * pow2Int b.shift) := by ac_rfl

theorem add_same_shift_eqv (x y : Int) (s : Nat) :
    eqv (add ⟨x, s⟩ ⟨y, s⟩) ⟨x + y, s⟩ := by
  unfold eqv add
  rw [pow2Int_add, ← Int.add_mul, Int.mul_assoc]

theorem zero_eqv_scaled (s : Nat) : eqv zero ⟨0, s⟩ := by
  simp [eqv, zero]

/-- Explicit uniform exponential decay in `Z[1/2]`: whenever `p < 2^q`, for EVERY `C` and
    EVERY precision `2^{-k}`, there is an explicit `N` such that `∀ n ≥ N, C * (p/2^q)^n < 2^{-k}`. -/
theorem strict_contraction_decay (C p q k : Nat) (hlt : p < 2 ^ q) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      lt (mul (ofNat C) (pow ⟨(p : Int), q⟩ n)) ⟨1, k⟩ := by
  by_cases hp : p = 0
  · refine ⟨1, ?_⟩
    intro n hn
    unfold lt mul ofNat
    rw [pow_num, pow_shift, Nat.zero_add, hp]
    have hpow0 : ((0 : Nat) : Int) ^ n = 0 := by
      cases n with
      | zero => omega
      | succ r => simp [Int.pow_succ]
    rw [hpow0]
    have hpos : 0 < pow2Int (q * n) := pow2Int_pos (q * n)
    simp; exact hpos
  · have hbinom : ∀ m : Nat, p ^ m * (p + m) ≤ (p + 1) ^ (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ r ih =>
        rw [Nat.pow_succ (p + 1) (r + 1)]
        have hstep : (p ^ r * (p + r)) * (p + 1) ≤ (p + 1) ^ (r + 1) * (p + 1) :=
          Nat.mul_le_mul_right (p + 1) ih
        have halg : p ^ (r + 1) * (p + (r + 1)) ≤ (p ^ r * (p + r)) * (p + 1) := by
          rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc]
          apply Nat.mul_le_mul_left
          have h3 : p * (p + (r + 1)) = p * p + p * r + p := by
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
          have h4 : (p + r) * (p + 1) = p * p + p * r + p + r := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm r p]
            omega
          omega
        exact Nat.le_trans halg hstep
    let m0 := C * 2 ^ k * p
    refine ⟨m0 + 1, ?_⟩
    intro n hn
    have hstep1 : p ^ m0 * (p + m0) ≤ (p + 1) ^ (m0 + 1) := hbinom m0
    have hpow_le : (p + 1) ^ (m0 + 1) ≤ (2 ^ q) ^ (m0 + 1) := Nat.pow_le_pow_left hlt (m0 + 1)
    have hC_lt : C * 2 ^ k * p ^ (m0 + 1) < (2 ^ q) ^ (m0 + 1) := by
      have h1 : C * 2 ^ k * p ^ (m0 + 1) < p ^ m0 * (p + m0) := by
        rw [Nat.pow_succ]
        have heq : C * 2 ^ k * (p ^ m0 * p) = p ^ m0 * m0 := by dsimp [m0]; ac_rfl
        rw [heq, Nat.mul_add]
        have hpos_p : 0 < p ^ m0 * p := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
        omega
      exact Nat.lt_of_lt_of_le h1 (Nat.le_trans hstep1 hpow_le)
    have hnat_n : C * 2 ^ k * p ^ n < (2 ^ q) ^ n := by
      let r := n - (m0 + 1)
      have hnr : n = (m0 + 1) + r := by omega
      rw [hnr, Nat.pow_add p, Nat.pow_add (2 ^ q)]
      have hpos_pr : 0 < p ^ r := Nat.pow_pos (by omega)
      have hmul1 : C * 2 ^ k * (p ^ (m0 + 1) * p ^ r) < (2 ^ q) ^ (m0 + 1) * p ^ r := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_lt_mul_of_pos_right hC_lt hpos_pr
      have hmul2 : (2 ^ q) ^ (m0 + 1) * p ^ r ≤ (2 ^ q) ^ (m0 + 1) * (2 ^ q) ^ r :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) r)
      exact Nat.lt_of_lt_of_le hmul1 hmul2
    unfold lt mul ofNat
    rw [pow_num, pow_shift, Nat.zero_add, pow2Int_mul]
    unfold pow2Int
    have hcast : ((C * 2 ^ k * p ^ n : Nat) : Int) < (((2 ^ q) ^ n : Nat) : Int) :=
      Int.ofNat_lt.mpr hnat_n
    rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_pow, Int.natCast_pow] at hcast
    have hgoal : ((C : Int) * (p : Int) ^ n) * ((2 ^ k : Nat) : Int) =
                 (C : Int) * ((2 ^ k : Nat) : Int) * (p : Int) ^ n := by ac_rfl
    rw [hgoal, Int.one_mul]
    exact hcast

/-- Explicit unbounded exponential explosion in `Z[1/2]`: whenever `a > 2^s`, for EVERY bound `B`,
    there exists `k : Nat` such that `B < (a / 2^s)^k`. -/
theorem strict_explosion_unbounded (a s B : Nat) (hgt : 2 ^ s < a) :
    ∃ k : Nat, lt (ofNat B) (pow ⟨(a : Int), s⟩ k) := by
  let b := 2 ^ s
  have hb_pos : 0 < b := Nat.pow_pos (by omega)
  have hbinom : ∀ m : Nat, b ^ m * (b + m) ≤ (b + 1) ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ r ih =>
      rw [Nat.pow_succ (b + 1) (r + 1)]
      have hstep := Nat.mul_le_mul_right (b + 1) ih
      have halg : b ^ (r + 1) * (b + (r + 1)) ≤ (b ^ r * (b + r)) * (b + 1) := by
        rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc]
        apply Nat.mul_le_mul_left
        have h3 : b * (b + (r + 1)) = b * b + b * r + b := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
        have h4 : (b + r) * (b + 1) = b * b + b * r + b + r := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_comm r b]; omega
        omega
      exact Nat.le_trans halg hstep
  let m0 := B * b
  refine ⟨m0 + 1, ?_⟩
  have h1 : B * b ^ (m0 + 1) < b ^ m0 * (b + m0) := by
    rw [Nat.pow_succ]
    have heq : B * (b ^ m0 * b) = b ^ m0 * m0 := by dsimp [m0]; ac_rfl
    rw [heq, Nat.mul_add]
    have hpos : 0 < b ^ m0 * b := Nat.mul_pos (Nat.pow_pos hb_pos) hb_pos
    omega
  have h2 : b ^ m0 * (b + m0) ≤ a ^ (m0 + 1) :=
    Nat.le_trans (hbinom m0) (Nat.pow_le_pow_left hgt (m0 + 1))
  have hlt_nat : B * (2 ^ s) ^ (m0 + 1) < a ^ (m0 + 1) := Nat.lt_of_lt_of_le h1 h2
  unfold lt ofNat
  rw [pow_num, pow_shift, pow2Int_zero, Int.mul_one, pow2Int_mul]
  unfold pow2Int
  have hcast : ((B * (2 ^ s) ^ (m0 + 1) : Nat) : Int) < ((a ^ (m0 + 1) : Nat) : Int) :=
    Int.ofNat_lt.mpr hlt_nat
  rw [Int.natCast_mul, Int.natCast_pow, Int.natCast_pow] at hcast
  exact hcast

end Dyad
theorem finSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    finSum f = finSum g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSum, h (Fin.last k)]
    rw [ih (fun i => h i.castSucc)]

theorem finSum_zero (n : Nat) : finSum (fun _ : Fin n => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [finSum, ih]

theorem finSum_add {n : Nat} (f g : Fin n → Int) :
    finSum (fun i => f i + g i) = finSum f + finSum g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
    omega

theorem finSum_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    finSum (fun i => c * f i) = c * finSum f := by
  induction n with
  | zero => simp [finSum]
  | succ k ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc), Int.mul_add]

theorem finSum_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    finSum (fun i => f i * c) = finSum f * c := by
  induction n with
  | zero => simp [finSum]
  | succ k ih =>
    simp only [finSum]
    rw [ih (fun i => f i.castSucc), Int.add_mul]

theorem finSum_swap {m n : Nat} (f : Fin m → Fin n → Int) :
    finSum (fun i => finSum (fun j => f i j)) = finSum (fun j => finSum (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [finSum]
    symm
    exact finSum_zero n
  | succ k ih =>
    simp only [finSum]
    rw [ih (fun i j => f i.castSucc j)]
    rw [← finSum_add]

theorem finSum_le_finSum {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i ≤ g i) :
    finSum f ≤ finSum g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    simp only [finSum]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h (Fin.last k)
    omega

theorem finSum_nonneg {n : Nat} {f : Fin n → Int} (h : ∀ i, 0 ≤ f i) :
    0 ≤ finSum f := by
  have h0 := finSum_le_finSum (f := fun _ : Fin n => (0 : Int)) (g := f) h
  rw [finSum_zero] at h0
  exact h0

theorem iabs_finSum_le {n : Nat} (f : Fin n → Int) :
    iabs (finSum f) ≤ finSum (fun i => iabs (f i)) := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    simp only [finSum]
    have h1 := iabs_add_le (finSum (fun i : Fin k => f i.castSucc)) (f (Fin.last k))
    have h2 := ih (fun i => f i.castSucc)
    omega

theorem finSum_single {n : Nat} (j : Fin n) (v : Int) :
    finSum (fun i : Fin n => if i = j then v else 0) = v := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    simp only [finSum]
    by_cases hj : j = Fin.last k
    · subst hj
      have hcast : ∀ i : Fin k, i.castSucc ≠ Fin.last k := by
        intro i h
        have hv : i.val = k := congrArg Fin.val h
        omega
      have hz : finSum (fun i : Fin k => if i.castSucc = Fin.last k then v else 0) = 0 := by
        calc finSum (fun i : Fin k => if i.castSucc = Fin.last k then v else 0)
            = finSum (fun _ : Fin k => (0 : Int)) := finSum_congr (fun i => by simp [hcast i])
          _ = 0 := finSum_zero k
      simp [hz]
    · have hjlt : j.val < k := by
        have h1 : j.val < k + 1 := j.isLt
        have h2 : j.val ≠ k := fun hv => hj (Fin.ext hv)
        omega
      let j' : Fin k := ⟨j.val, hjlt⟩
      have hcast_eq : ∀ i : Fin k, (i.castSucc = j) ↔ (i = j') := by
        intro i
        constructor
        · intro h
          have hv : i.val = j.val := congrArg Fin.val h
          exact Fin.ext hv
        · intro h
          have hv : i.val = j.val := congrArg Fin.val h
          exact Fin.ext hv
      have hlast : Fin.last k ≠ j := fun h => hj h.symm
      simp only [hlast, ↓reduceIte, Int.add_zero]
      have hcongr : finSum (fun i : Fin k => if i.castSucc = j then v else 0) =
                    finSum (fun i : Fin k => if i = j' then v else 0) := by
        apply finSum_congr; intro i
        by_cases hi : i = j'
        · have hi' : i.castSucc = j := (hcast_eq i).mpr hi
          subst hi
          simp only [hi', ↓reduceIte]
        · have hi' : i.castSucc ≠ j := fun h => hi ((hcast_eq i).mp h)
          simp only [hi', hi, ↓reduceIte]
      rw [hcongr]
      exact ih j'

theorem finSum_natCast {n : Nat} (f : Fin n → Nat) :
    finSum (fun i => (f i : Int)) = (finSumNat f : Int) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [finSum, finSumNat]
    rw [ih (fun i => f i.castSucc), Int.natCast_add]

theorem finSumD_scaled_eqv {n : Nat} (s : Nat) (f : Fin n → Dyad) (g : Fin n → Int)
    (h : ∀ i, Dyad.eqv (f i) ⟨g i, s⟩) :
    Dyad.eqv (finSumD f) ⟨finSum g, s⟩ := by
  induction n with
  | zero =>
    simp only [finSumD, finSum]
    exact Dyad.zero_eqv_scaled s
  | succ k ih =>
    simp only [finSumD, finSum]
    have h1 := ih (fun i => f i.castSucc) (fun i => g i.castSucc) (fun i => h i.castSucc)
    have h2 := h (Fin.last k)
    exact Dyad.eqv_trans (Dyad.add_eqv_congr h1 h2) (Dyad.add_same_shift_eqv _ _ s)

theorem vecMaxAbs_nonneg {n : Nat} (v : Vec n) : 0 ≤ vecMaxAbs v := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    simp only [vecMaxAbs]
    have h1 := ih (fun i => v i.castSucc)
    omega

theorem iabs_le_vecMaxAbs {n : Nat} (v : Vec n) (i : Fin n) :
    iabs (v i) ≤ vecMaxAbs v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    simp only [vecMaxAbs]
    by_cases hi : i = Fin.last k
    · subst hi; omega
    · have hilt : i.val < k := by
        have h1 := i.isLt
        have h2 : i.val ≠ k := fun hv => hi (Fin.ext hv)
        omega
      let i' : Fin k := ⟨i.val, hilt⟩
      have heq : i'.castSucc = i := Fin.ext rfl
      have h1 := ih (fun j => v j.castSucc) i'
      rw [heq] at h1
      omega

theorem vecMaxAbs_le {n : Nat} {v : Vec n} {B : Int} (hB : 0 ≤ B)
    (h : ∀ i : Fin n, iabs (v i) ≤ B) : vecMaxAbs v ≤ B := by
  induction n with
  | zero => exact hB
  | succ k ih =>
    simp only [vecMaxAbs]
    have h1 := ih (fun i => h i.castSucc)
    have h2 := h (Fin.last k)
    omega

theorem rowAbsSum_nonneg {r c : Nat} (M : Mat r c) (i : Fin r) : 0 ≤ rowAbsSum M i :=
  finSum_nonneg (fun j => iabs_nonneg (M i j))

theorem rowAbsSum_le_matInfNorm {r c : Nat} (M : Mat r c) (i : Fin r) :
    rowAbsSum M i ≤ matInfNorm M := by
  have h := iabs_le_vecMaxAbs (fun k : Fin r => rowAbsSum M k) i
  rw [iabs_eq_self (rowAbsSum_nonneg M i)] at h
  exact h

theorem matVec_matMul {r k c : Nat} (A : Mat r k) (B : Mat k c) (x : Vec c) (i : Fin r) :
    matVec (matMul A B) x i = matVec A (matVec B x) i := by
  unfold matVec matMul
  calc finSum (fun j => finSum (fun t => A i t * B t j) * x j)
      = finSum (fun j => finSum (fun t => (A i t * B t j) * x j)) := by
          apply finSum_congr; intro j; rw [finSum_mul_right]
    _ = finSum (fun t => finSum (fun j => (A i t * B t j) * x j)) := finSum_swap _
    _ = finSum (fun t => finSum (fun j => A i t * (B t j * x j))) := by
          apply finSum_congr; intro t; apply finSum_congr; intro j; rw [Int.mul_assoc]
    _ = finSum (fun t => A i t * finSum (fun j => B t j * x j)) := by
          apply finSum_congr; intro t; rw [finSum_mul_left]

theorem matVec_scaleMat {r c : Nat} (s : Int) (M : Mat r c) (x : Vec c) (i : Fin r) :
    matVec (scaleMat s M) x i = s * matVec M x i := by
  unfold matVec scaleMat
  rw [← finSum_mul_left]
  apply finSum_congr; intro j; rw [Int.mul_assoc]

theorem matVec_scaleVec {r c : Nat} (s : Int) (M : Mat r c) (x : Vec c) (i : Fin r) :
    matVec M (fun j => s * x j) i = s * matVec M x i := by
  unfold matVec
  rw [← finSum_mul_left]
  apply finSum_congr; intro j; dsimp only; ac_rfl

theorem matVec_matId {d : Nat} (x : Vec d) (i : Fin d) :
    matVec (matId d) x i = x i := by
  unfold matVec matId
  have h : (fun j : Fin d => (if i = j then (1 : Int) else 0) * x j) =
           (fun j : Fin d => if j = i then x i else 0) := by
    funext j
    by_cases hij : j = i
    · subst hij; simp
    · have hji : i ≠ j := fun h => hij h.symm
      simp [hij, hji]
  rw [h, finSum_single]

theorem matVec_stdBasis {r c : Nat} (M : Mat r c) (q : Fin c) (p : Fin r) :
    matVec M (stdBasis q) p = M p q := by
  unfold matVec stdBasis
  have h : (fun j : Fin c => M p j * (if j = q then (1 : Int) else 0)) =
           (fun j : Fin c => if j = q then M p q else 0) := by
    funext j
    by_cases hj : j = q
    · subst hj; simp
    · simp [hj]
  rw [h, finSum_single]

theorem matMul_assoc {a b c d : Nat} (A : Mat a b) (B : Mat b c) (C : Mat c d) (i : Fin a) (j : Fin d) :
    matMul (matMul A B) C i j = matMul A (matMul B C) i j :=
  matVec_matMul A B (fun t => C t j) i

theorem matMul_id_left {r c : Nat} (M : Mat r c) (i : Fin r) (j : Fin c) :
    matMul (matId r) M i j = M i j := matVec_matId (fun t => M t j) i

theorem matMul_id_right {r c : Nat} (M : Mat r c) (i : Fin r) (j : Fin c) :
    matMul M (matId c) i j = M i j := matVec_stdBasis M j i

/-- Key inequality: `| (M x)_i | ≤ rowAbsSum M i * ‖x‖_∞`. -/
theorem iabs_matVec_le {r c : Nat} (M : Mat r c) (x : Vec c) (i : Fin r) :
    iabs (matVec M x i) ≤ rowAbsSum M i * vecMaxAbs x := by
  unfold matVec rowAbsSum
  calc iabs (finSum (fun j => M i j * x j))
      ≤ finSum (fun j => iabs (M i j * x j)) := iabs_finSum_le _
    _ = finSum (fun j => iabs (M i j) * iabs (x j)) := by
          apply finSum_congr; intro j; exact iabs_mul _ _
    _ ≤ finSum (fun j => iabs (M i j) * vecMaxAbs x) := by
          apply finSum_le_finSum; intro j
          exact Int.mul_le_mul_of_nonneg_left (iabs_le_vecMaxAbs x j) (iabs_nonneg _)
    _ = finSum (fun j => iabs (M i j)) * vecMaxAbs x := finSum_mul_right _ _

theorem dyadicMatMul_scaled_eqv {r k c : Nat} (sA sB : Nat)
    (A : MatD r k) (B : MatD k c) (Ai : Mat r k) (Bi : Mat k c)
    (hA : ∀ i t, Dyad.eqv (A i t) ⟨Ai i t, sA⟩)
    (hB : ∀ t j, Dyad.eqv (B t j) ⟨Bi t j, sB⟩)
    (i : Fin r) (j : Fin c) :
    Dyad.eqv (dyadicMatMul A B i j) ⟨matMul Ai Bi i j, sA + sB⟩ := by
  unfold dyadicMatMul matMul
  apply finSumD_scaled_eqv (sA + sB)
  intro t
  exact Dyad.mul_eqv_congr (hA i t) (hB t j)

theorem dyadicRowAbsSum_scaled_eqv {r c : Nat} (s : Nat) (M : MatD r c) (Mi : Mat r c)
    (hM : ∀ i j, Dyad.eqv (M i j) ⟨Mi i j, s⟩) (i : Fin r) :
    Dyad.eqv (dyadicRowAbsSum M i) ⟨rowAbsSum Mi i, s⟩ := by
  unfold dyadicRowAbsSum rowAbsSum
  apply finSumD_scaled_eqv s
  intro j
  exact Dyad.abs_eqv_congr (hM i j)

theorem intWordProd_append {d m : Nat} (A : Fin m → Mat d d) (w1 w2 : List (Fin m)) (i j : Fin d) :
    intWordProd A (w1 ++ w2) i j = matMul (intWordProd A w2) (intWordProd A w1) i j := by
  induction w1 generalizing i j with
  | nil =>
    simp only [List.nil_append, intWordProd]
    rw [matMul_id_right]
  | cons b bs ih =>
    simp only [List.cons_append, intWordProd]
    have hstep : matMul (intWordProd A (bs ++ w2)) (A b) i j =
                 matMul (matMul (intWordProd A w2) (intWordProd A bs)) (A b) i j := by
      unfold matMul
      apply finSum_congr; intro t
      rw [ih i t]
      rfl
    rw [hstep]
    exact matMul_assoc _ _ _ i j

theorem intWordProdRL_eq_reverse {d m : Nat} (A : Fin m → Mat d d) (w : List (Fin m)) (i j : Fin d) :
    intWordProdRL A w i j = intWordProd A w.reverse i j := by
  induction w generalizing i j with
  | nil => rfl
  | cons b bs ih =>
    simp only [intWordProdRL, List.reverse_cons]
    rw [intWordProd_append]
    unfold matMul
    apply finSum_congr; intro t
    have hsingle : intWordProd A [b] i t = A b i t := by
      simp only [intWordProd]
      exact matMul_id_left (A b) i t
    rw [hsingle, ih t j]

/-- Exact homomorphism bridging `dyadicWordProd` (over `Z[1/2]`) to `intWordProd` (over `Int`). -/
theorem dyadicWordProd_eqv {d m : Nat} (s : Nat) (A : Fin m → Mat d d)
    (w : List (Fin m)) (i j : Fin d) :
    Dyad.eqv (dyadicWordProd (fun b => scaleDyadicMat s (A b)) w i j)
               ⟨intWordProd A w i j, s * w.length⟩ := by
  induction w generalizing i j with
  | nil =>
    simp only [dyadicWordProd, dyadicMatId, intWordProd, matId, List.length_nil, Nat.mul_zero]
    by_cases hij : i = j <;> simp [hij, Dyad.eqv, Dyad.one, Dyad.zero]
  | cons b bs ih =>
    simp only [dyadicWordProd, intWordProd, List.length_cons, Nat.mul_succ]
    exact dyadicMatMul_scaled_eqv (s * bs.length) s
      (dyadicWordProd (fun b => scaleDyadicMat s (A b)) bs)
      (scaleDyadicMat s (A b))
      (intWordProd A bs) (A b) ih (fun _ _ => Dyad.eqv_refl _) i j

theorem dyadicWordProdRL_eqv {d m : Nat} (s : Nat) (A : Fin m → Mat d d)
    (w : List (Fin m)) (i j : Fin d) :
    Dyad.eqv (dyadicWordProdRL (fun b => scaleDyadicMat s (A b)) w i j)
               ⟨intWordProdRL A w i j, s * w.length⟩ := by
  induction w generalizing i j with
  | nil =>
    simp only [dyadicWordProdRL, dyadicMatId, intWordProdRL, matId, List.length_nil, Nat.mul_zero]
    by_cases hij : i = j <;> simp [hij, Dyad.eqv, Dyad.one, Dyad.zero]
  | cons b bs ih =>
    simp only [dyadicWordProdRL, intWordProdRL, List.length_cons, Nat.mul_succ]
    have hcomm : s + s * bs.length = s * bs.length + s := Nat.add_comm _ _
    rw [← hcomm]
    exact dyadicMatMul_scaled_eqv s (s * bs.length)
      (scaleDyadicMat s (A b))
      (dyadicWordProdRL (fun b => scaleDyadicMat s (A b)) bs)
      (A b) (intWordProdRL A bs) (fun _ _ => Dyad.eqv_refl _) ih i j

-- Infinite-Alphabet Dyadic Convex-Hull Product Semantics --

theorem convexDyadicProd_eqv {d m : Nat} (s : Nat) (A : Fin m → Mat d d)
    (ws : List (DyadicConvexStep m)) (i j : Fin d) :
    Dyad.eqv (convexDyadicProd s A ws i j) ⟨convexIntProd A ws i j, convexShiftSum s ws⟩ := by
  induction ws generalizing i j with
  | nil =>
    simp only [convexDyadicProd, dyadicMatId, convexIntProd, matId, convexShiftSum]
    by_cases hij : i = j <;> simp [hij, Dyad.eqv, Dyad.one, Dyad.zero]
  | cons st rest ih =>
    simp only [convexDyadicProd, convexIntProd, convexShiftSum]
    exact dyadicMatMul_scaled_eqv (convexShiftSum s rest) (s + st.q)
      (convexDyadicProd s A rest) (convexStepDyadicMat s A st)
      (convexIntProd A rest) (convexStepIntMat A st) ih (fun _ _ => Dyad.eqv_refl _) i j

-- ============================================================================
-- SECTION 3: Pure-Data Certificate Structures & Decidable Checkers
-- ============================================================================

theorem finAll_eq_true {n : Nat} {p : Fin n → Bool} :
    finAll p = true ↔ ∀ i : Fin n, p i = true := by
  induction n with
  | zero =>
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _; rfl
  | succ k ih =>
    simp only [finAll, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = Fin.last k
      · subst hi; exact h2
      · have hilt : i.val < k := by
          have := i.isLt
          have hne : i.val ≠ k := fun hv => hi (Fin.ext hv)
          omega
        let i' : Fin k := ⟨i.val, hilt⟩
        have heq : i'.castSucc = i := Fin.ext rfl
        rw [← heq]; exact h1 i'
    · intro h
      exact ⟨fun i => h i.castSucc, h (Fin.last k)⟩

theorem matEqBool_eq_true {r c : Nat} {A B : Mat r c} :
    matEqBool A B = true ↔ ∀ i j, A i j = B i j := by
  unfold matEqBool
  simp [finAll_eq_true]

theorem repeatWord_length {α : Type} (w : List α) : ∀ k : Nat, (repeatWord w k).length = w.length * k
  | 0 => by simp [repeatWord]
  | k + 1 => by simp [repeatWord, repeatWord_length w k, Nat.mul_succ, Nat.add_comm]

/-- Helper: lift `s * |v_i| ≤ B` over `i : Fin n` to `s * ‖v‖_∞ ≤ B`. -/
theorem mul_vecMaxAbs_le {n : Nat} {s B : Int} {v : Vec n}
    (hB : 0 ≤ B) (hp : ∀ i : Fin n, s * iabs (v i) ≤ B) :
    s * vecMaxAbs v ≤ B := by
  induction n with
  | zero => simp [vecMaxAbs]; exact hB
  | succ k ih =>
    simp only [vecMaxAbs]
    have h1 := ih (v := fun i => v i.castSucc) (fun i => hp i.castSucc)
    have h2 := hp (Fin.last k)
    by_cases hm : vecMaxAbs (fun i : Fin k => v i.castSucc) ≤ iabs (v (Fin.last k))
    · rw [int_max_eq_right hm]; exact h2
    · rw [int_max_eq_left (Int.le_of_not_le hm)]; exact h1

-- 4A. Switched Polytope Soundness Meta-Theorems --

/-- One-step integer polytope contraction from a valid edge certificate. -/
theorem polytope_step_int {d m Q K : Nat} (cert : SwitchedPolytopeCert d m Q K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    {q q' : Fin Q} {b : Fin m} (hstep : cert.step q b = some q') (x : Vec d) :
    pow2Int cert.lamShift * vecMaxAbs (matVec (cert.W q') (matVec (cert.A b) x)) ≤
    ((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int) * vecMaxAbs (matVec (cert.W q) x) := by
  unfold checkSwitchedPolytopeCert at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, finAll_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hD, _⟩, hedges⟩, _⟩, hrate⟩, _⟩
  have hedge := hedges q b
  rw [hstep] at hedge
  simp only [Bool.and_eq_true, matEqBool_eq_true, finAll_eq_true, decide_eq_true_eq] at hedge
  rcases hedge with ⟨hinter, hrow⟩
  -- First prove D * ‖W_{q'} A_b x‖_∞ ≤ Lambda * ‖W_q x‖_∞
  have hD_step : (cert.D : Int) * vecMaxAbs (matVec (cert.W q') (matVec (cert.A b) x)) ≤
      (cert.Lambda : Int) * vecMaxAbs (matVec (cert.W q) x) := by
    apply mul_vecMaxAbs_le (Int.mul_nonneg (Int.natCast_nonneg _) (vecMaxAbs_nonneg _))
    intro i
    have heq_i : (cert.D : Int) * matVec (cert.W q') (matVec (cert.A b) x) i =
                 matVec (cert.C q b) (matVec (cert.W q) x) i := by
      rw [← matVec_matMul (cert.W q') (cert.A b) x i]
      rw [← matVec_scaleMat (cert.D : Int) (matMul (cert.W q') (cert.A b)) x i]
      rw [← matVec_matMul (cert.C q b) (cert.W q) x i]
      unfold matVec; apply finSum_congr; intro j; rw [hinter i j]
    calc (cert.D : Int) * iabs (matVec (cert.W q') (matVec (cert.A b) x) i)
        = iabs (cert.D : Int) * iabs (matVec (cert.W q') (matVec (cert.A b) x) i) := by
            rw [iabs_natCast]
      _ = iabs ((cert.D : Int) * matVec (cert.W q') (matVec (cert.A b) x) i) := by
            rw [← iabs_mul]
      _ = iabs (matVec (cert.C q b) (matVec (cert.W q) x) i) := by rw [heq_i]
      _ ≤ rowAbsSum (cert.C q b) i * vecMaxAbs (matVec (cert.W q) x) :=
            iabs_matVec_le _ _ i
      _ ≤ (cert.Lambda : Int) * vecMaxAbs (matVec (cert.W q) x) :=
            Int.mul_le_mul_of_nonneg_right (hrow i) (vecMaxAbs_nonneg _)
  -- Eliminate D using hrate: Lambda * 2^lamShift ≤ lamNum * D * 2^scaleShift
  have hD_pos : (0 : Int) < (cert.D : Int) := by omega
  have hrate_int : (cert.Lambda : Int) * pow2Int cert.lamShift ≤
      (cert.D : Int) * ((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int) := by
    unfold pow2Int
    have hnat : cert.Lambda * 2 ^ cert.lamShift ≤ cert.D * (cert.lamNum * 2 ^ cert.scaleShift) := by
      have hcomm : cert.lamNum * cert.D * 2 ^ cert.scaleShift =
                   cert.D * (cert.lamNum * 2 ^ cert.scaleShift) := by ac_rfl
      omega
    have hc := Int.ofNat_le.mpr hnat
    rw [Int.natCast_mul, Int.natCast_mul] at hc
    exact hc
  have hmul : (cert.D : Int) * (pow2Int cert.lamShift * vecMaxAbs (matVec (cert.W q') (matVec (cert.A b) x))) ≤
              (cert.D : Int) * (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int) * vecMaxAbs (matVec (cert.W q) x)) := by
    calc (cert.D : Int) * (pow2Int cert.lamShift * vecMaxAbs (matVec (cert.W q') (matVec (cert.A b) x)))
        = pow2Int cert.lamShift * ((cert.D : Int) * vecMaxAbs (matVec (cert.W q') (matVec (cert.A b) x))) := by ac_rfl
      _ ≤ pow2Int cert.lamShift * ((cert.Lambda : Int) * vecMaxAbs (matVec (cert.W q) x)) :=
            Int.mul_le_mul_of_nonneg_left hD_step (pow2Int_nonneg _)
      _ = ((cert.Lambda : Int) * pow2Int cert.lamShift) * vecMaxAbs (matVec (cert.W q) x) := by ac_rfl
      _ ≤ ((cert.D : Int) * ((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int)) * vecMaxAbs (matVec (cert.W q) x) :=
            Int.mul_le_mul_of_nonneg_right hrate_int (vecMaxAbs_nonneg _)
      _ = (cert.D : Int) * (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int) * vecMaxAbs (matVec (cert.W q) x)) := by ac_rfl
  exact Int.le_of_mul_le_mul_left hmul hD_pos

/-- General inductive contraction along ANY DFA-accepted word `w` of arbitrary length `|w|`. -/
theorem switched_polytope_word_norm {d m Q K : Nat} (cert : SwitchedPolytopeCert d m Q K)
    (hchk : checkSwitchedPolytopeCert cert = true) :
    ∀ (w : List (Fin m)) (q0 qn : Fin Q) (x : Vec d),
      runDFA cert.step q0 w = some qn →
      (pow2Int cert.lamShift) ^ w.length * vecMaxAbs (matVec (cert.W qn) (matVec (intWordProd cert.A w) x)) ≤
      (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length * vecMaxAbs (matVec (cert.W q0) x) := by
  intro w
  induction w with
  | nil =>
    intro q0 qn x hrun
    simp only [runDFA, Option.some.injEq] at hrun
    subst hrun
    have hid : matVec (intWordProd cert.A []) x = x := by
      funext i; exact matVec_matId x i
    rw [hid]
    simp [Int.pow_zero]
  | cons b bs ih =>
    intro q0 qn x hrun
    simp only [runDFA] at hrun
    cases hstep : cert.step q0 b with
    | none => rw [hstep] at hrun; cases hrun
    | some q1 =>
      rw [hstep] at hrun
      have h1 := polytope_step_int cert hchk hstep x
      have h2 := ih q1 qn (matVec (cert.A b) x) hrun
      have heq_vec : matVec (intWordProd cert.A (b :: bs)) x =
                     matVec (intWordProd cert.A bs) (matVec (cert.A b) x) := by
        funext i; exact matVec_matMul (intWordProd cert.A bs) (cert.A b) x i
      rw [heq_vec, List.length_cons, Int.pow_succ, Int.pow_succ]
      have hpow_nn2 := int_pow_nonneg (Int.natCast_nonneg (cert.lamNum * 2 ^ cert.scaleShift)) bs.length
      calc ((pow2Int cert.lamShift) ^ bs.length * pow2Int cert.lamShift) *
              vecMaxAbs (matVec (cert.W qn) (matVec (intWordProd cert.A bs) (matVec (cert.A b) x)))
          = pow2Int cert.lamShift *
              ((pow2Int cert.lamShift) ^ bs.length *
                vecMaxAbs (matVec (cert.W qn) (matVec (intWordProd cert.A bs) (matVec (cert.A b) x)))) := by ac_rfl
        _ ≤ pow2Int cert.lamShift *
              ((((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ bs.length *
                vecMaxAbs (matVec (cert.W q1) (matVec (cert.A b) x))) :=
              Int.mul_le_mul_of_nonneg_left h2 (pow2Int_nonneg _)
        _ = (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ bs.length *
              (pow2Int cert.lamShift * vecMaxAbs (matVec (cert.W q1) (matVec (cert.A b) x))) := by ac_rfl
        _ ≤ (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ bs.length *
              (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int) * vecMaxAbs (matVec (cert.W q0) x)) :=
              Int.mul_le_mul_of_nonneg_left h1 hpow_nn2
        _ = ((((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ bs.length *
              (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int))) * vecMaxAbs (matVec (cert.W q0) x) := by ac_rfl

/-- Coercivity lifting: converts polytope norm bound to standard `ℓ_∞` operator norm bound. -/
theorem polytope_coercivity_lift {d m Q K : Nat} (cert : SwitchedPolytopeCert d m Q K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    (q0 qn : Fin Q) (P : Mat d d) (L R : Int) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hbound : ∀ x : Vec d, L * vecMaxAbs (matVec (cert.W qn) (matVec P x)) ≤ R * vecMaxAbs (matVec (cert.W q0) x)) :
    L * matInfNorm P ≤ (cert.C_const : Int) * R := by
  unfold checkSwitchedPolytopeCert at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, finAll_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨_, hDU⟩, _⟩, hcoerc⟩, _⟩, hCconst⟩
  have hq0 := hcoerc q0
  have hqn := hcoerc qn
  simp only [matEqBool_eq_true] at hq0 hqn
  rcases hq0 with ⟨⟨_, _⟩, hW0⟩
  rcases hqn with ⟨⟨hUWn, hUn⟩, _⟩
  have hDU_pos : (0 : Int) < (cert.D_U : Int) := by omega
  have hrow_bound : ∀ p : Fin d, L * rowAbsSum P p ≤ (cert.C_const : Int) * R := by
    intro p
    let sgn : Vec d := fun j => if 0 ≤ P p j then 1 else -1
    have hsgn_max : vecMaxAbs sgn ≤ 1 := by
      apply vecMaxAbs_le (by omega)
      intro j
      dsimp [sgn]
      by_cases h : 0 ≤ P p j <;> simp [h, iabs]
    have hPsgn : matVec P sgn p = rowAbsSum P p := by
      unfold matVec rowAbsSum
      apply finSum_congr; intro j
      dsimp [sgn]
      by_cases h : 0 ≤ P p j
      · simp only [h, ↓reduceIte, Int.mul_one, iabs_eq_self h]
      · simp only [h, ↓reduceIte]
        have habs : iabs (P p j) = -P p j := by unfold iabs; simp [h]
        omega
    -- Step 1: D_U * rowAbsSum P p ≤ kappa * ‖W_{qn} P sgn‖_∞
    have h1 : (cert.D_U : Int) * rowAbsSum P p ≤
        (cert.kappa : Int) * vecMaxAbs (matVec (cert.W qn) (matVec P sgn)) := by
      have heq_p : (cert.D_U : Int) * matVec P sgn p =
                   matVec (cert.U qn) (matVec (cert.W qn) (matVec P sgn)) p := by
        rw [← matVec_matMul (cert.U qn) (cert.W qn) (matVec P sgn) p]
        have hsc : matVec (scaleMat (cert.D_U : Int) (matId d)) (matVec P sgn) p =
                   (cert.D_U : Int) * matVec P sgn p := by
          rw [matVec_scaleMat, matVec_matId]
        rw [← hsc]
        unfold matVec; apply finSum_congr; intro j; rw [hUWn p j]
      calc (cert.D_U : Int) * rowAbsSum P p
          = (cert.D_U : Int) * matVec P sgn p := by rw [hPsgn]
        _ ≤ iabs ((cert.D_U : Int) * matVec P sgn p) := le_iabs _
        _ = iabs (matVec (cert.U qn) (matVec (cert.W qn) (matVec P sgn)) p) := by rw [heq_p]
        _ ≤ rowAbsSum (cert.U qn) p * vecMaxAbs (matVec (cert.W qn) (matVec P sgn)) :=
              iabs_matVec_le _ _ p
        _ ≤ (cert.kappa : Int) * vecMaxAbs (matVec (cert.W qn) (matVec P sgn)) :=
              Int.mul_le_mul_of_nonneg_right (hUn p) (vecMaxAbs_nonneg _)
    -- Step 2: ‖W_{q0} sgn‖_∞ ≤ omega
    have h2 : vecMaxAbs (matVec (cert.W q0) sgn) ≤ (cert.omega : Int) := by
      apply vecMaxAbs_le (Int.natCast_nonneg _)
      intro i
      calc iabs (matVec (cert.W q0) sgn i)
          ≤ rowAbsSum (cert.W q0) i * vecMaxAbs sgn := iabs_matVec_le _ _ i
        _ ≤ (cert.omega : Int) * 1 := by
              have hle1 := Int.mul_le_mul_of_nonneg_right (hW0 i) (vecMaxAbs_nonneg sgn)
              have hle2 := Int.mul_le_mul_of_nonneg_left hsgn_max (Int.natCast_nonneg cert.omega)
              exact Int.le_trans hle1 hle2
        _ = (cert.omega : Int) := Int.mul_one _
    -- Combine h1, hbound sgn, h2, and kappa * omega ≤ C_const * D_U
    have hC_int : (cert.kappa : Int) * (cert.omega : Int) ≤
                  (cert.D_U : Int) * (cert.C_const : Int) := by
      have hnat : cert.kappa * cert.omega ≤ cert.D_U * cert.C_const := by
        rw [Nat.mul_comm cert.D_U cert.C_const]; exact hCconst
      have hc := Int.ofNat_le.mpr hnat
      rw [Int.natCast_mul, Int.natCast_mul] at hc
      exact hc
    have hmul : (cert.D_U : Int) * (L * rowAbsSum P p) ≤
                (cert.D_U : Int) * ((cert.C_const : Int) * R) := by
      calc (cert.D_U : Int) * (L * rowAbsSum P p)
          = L * ((cert.D_U : Int) * rowAbsSum P p) := by ac_rfl
        _ ≤ L * ((cert.kappa : Int) * vecMaxAbs (matVec (cert.W qn) (matVec P sgn))) :=
              Int.mul_le_mul_of_nonneg_left h1 hL
        _ = (cert.kappa : Int) * (L * vecMaxAbs (matVec (cert.W qn) (matVec P sgn))) := by ac_rfl
        _ ≤ (cert.kappa : Int) * (R * vecMaxAbs (matVec (cert.W q0) sgn)) :=
              Int.mul_le_mul_of_nonneg_left (hbound sgn) (Int.natCast_nonneg _)
        _ ≤ (cert.kappa : Int) * (R * (cert.omega : Int)) :=
              Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul_of_nonneg_left h2 hR) (Int.natCast_nonneg _)
        _ = ((cert.kappa : Int) * (cert.omega : Int)) * R := by ac_rfl
        _ ≤ ((cert.D_U : Int) * (cert.C_const : Int)) * R :=
              Int.mul_le_mul_of_nonneg_right hC_int hR
        _ = (cert.D_U : Int) * ((cert.C_const : Int) * R) := by ac_rfl
    exact Int.le_of_mul_le_mul_left hmul hDU_pos
  -- Lift over all rows p : Fin d to L * matInfNorm P ≤ C_const * R
  unfold matInfNorm
  apply mul_vecMaxAbs_le (Int.mul_nonneg (Int.natCast_nonneg _) hR)
  intro p
  rw [iabs_eq_self (rowAbsSum_nonneg P p)]
  exact hrow_bound p

/-- **MAIN SOUNDNESS META-THEOREM 1 (DFA-Switched Exact Dyadic Operator-Norm Contraction):**
    If `checkSwitchedPolytopeCert cert = true`, then for EVERY word `w` of arbitrary length
    accepted by the DFA (`runDFA cert.step q0 w = some qn`) and EVERY row `p : Fin d`,
    the exact `Z[1/2]` row `ℓ_1` norm of `dyadicWordProd M w` satisfies:
    `‖(dyadicWordProd M w)_p‖_1 ≤_{Z[1/2]} C_const * (lamNum / 2^lamShift)^|w|`. -/
theorem switched_polytope_sound {d m Q K : Nat} (cert : SwitchedPolytopeCert d m Q K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    (q0 qn : Fin Q) (w : List (Fin m)) (hrun : runDFA cert.step q0 w = some qn)
    (p : Fin d) :
    Dyad.le (dyadicRowAbsSum (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w) p)
              (Dyad.mul (Dyad.ofNat cert.C_const) (Dyad.pow ⟨(cert.lamNum : Int), cert.lamShift⟩ w.length)) := by
  have hnorm := switched_polytope_word_norm cert hchk w q0 qn
  have hpowL_nn := int_pow_nonneg (pow2Int_nonneg cert.lamShift) w.length
  have hpowR_nn := int_pow_nonneg (Int.natCast_nonneg (cert.lamNum * 2 ^ cert.scaleShift)) w.length
  have hinf := polytope_coercivity_lift cert hchk q0 qn (intWordProd cert.A w)
    ((pow2Int cert.lamShift) ^ w.length)
    (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int) ^ w.length)
    hpowL_nn hpowR_nn (fun x => hnorm x hrun)
  have hrow_le : (pow2Int cert.lamShift) ^ w.length * rowAbsSum (intWordProd cert.A w) p ≤
      (cert.C_const : Int) * (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int) ^ w.length) :=
    Int.le_trans (Int.mul_le_mul_of_nonneg_left (rowAbsSum_le_matInfNorm _ p) hpowL_nn) hinf
  have heqv : Dyad.eqv
      (dyadicRowAbsSum (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w) p)
      ⟨rowAbsSum (intWordProd cert.A w) p, cert.scaleShift * w.length⟩ :=
    dyadicRowAbsSum_scaled_eqv (cert.scaleShift * w.length) _ _
      (dyadicWordProd_eqv cert.scaleShift cert.A w) p
  apply Dyad.le_of_eqv_left heqv
  unfold Dyad.le Dyad.mul Dyad.ofNat
  rw [Dyad.pow_num, Dyad.pow_shift, Nat.zero_add, pow2Int_mul, pow2Int_mul]
  have hpow_mul : (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length =
      (cert.lamNum : Int) ^ w.length * (pow2Int cert.scaleShift) ^ w.length := by
    rw [Int.natCast_mul]
    unfold pow2Int
    induction w.length with
    | zero => simp [Int.pow_zero]
    | succ k ih => rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, ih]; ac_rfl
  rw [hpow_mul] at hrow_le
  have hl : rowAbsSum (intWordProd cert.A w) p * (pow2Int cert.lamShift) ^ w.length =
            (pow2Int cert.lamShift) ^ w.length * rowAbsSum (intWordProd cert.A w) p := by ac_rfl
  have hr : ((cert.C_const : Int) * (cert.lamNum : Int) ^ w.length) * (pow2Int cert.scaleShift) ^ w.length =
            (cert.C_const : Int) * ((cert.lamNum : Int) ^ w.length * (pow2Int cert.scaleShift) ^ w.length) := by ac_rfl
  rw [hl, hr]
  exact hrow_le

/-- Helper: in a 1-state unconstrained DFA (`step 0 b = some 0`), every word is accepted. -/
theorem runDFA_unconstrained {m : Nat} (step : Fin 1 → Fin m → Option (Fin 1))
    (hall : ∀ b : Fin m, step 0 b = some 0) :
    ∀ w : List (Fin m), runDFA step 0 w = some 0
  | [] => rfl
  | b :: bs => by simp [runDFA, hall b, runDFA_unconstrained step hall bs]

/-- **COROLLARY 1B (Unconstrained Binary Matrix-Monoid Contraction for ALL words `w`):** -/
theorem unconstrained_polytope_sound {d m K : Nat} (cert : SwitchedPolytopeCert d m 1 K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    (hall : ∀ b : Fin m, cert.step 0 b = some 0)
    (w : List (Fin m)) (p : Fin d) :
    Dyad.le (dyadicRowAbsSum (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w) p)
              (Dyad.mul (Dyad.ofNat cert.C_const) (Dyad.pow ⟨(cert.lamNum : Int), cert.lamShift⟩ w.length)) :=
  switched_polytope_sound cert hchk 0 0 w (runDFA_unconstrained cert.step hall w) p

/-- **COROLLARY 1C (Right-to-Left Product `M_{b_1} * ... * M_{b_n}` Contraction for ALL words `w`):** -/
theorem unconstrained_polytope_sound_RL {d m K : Nat} (cert : SwitchedPolytopeCert d m 1 K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    (hall : ∀ b : Fin m, cert.step 0 b = some 0)
    (w : List (Fin m)) (p : Fin d) :
    Dyad.le (dyadicRowAbsSum (dyadicWordProdRL (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w) p)
              (Dyad.mul (Dyad.ofNat cert.C_const) (Dyad.pow ⟨(cert.lamNum : Int), cert.lamShift⟩ w.length)) := by
  have hrev := unconstrained_polytope_sound cert hchk hall w.reverse p
  rw [List.length_reverse] at hrev
  have heqv1 : Dyad.eqv
      (dyadicRowAbsSum (dyadicWordProdRL (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w) p)
      ⟨rowAbsSum (intWordProdRL cert.A w) p, cert.scaleShift * w.length⟩ :=
    dyadicRowAbsSum_scaled_eqv _ _ _ (dyadicWordProdRL_eqv cert.scaleShift cert.A w) p
  have heqv2 : Dyad.eqv
      (dyadicRowAbsSum (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w.reverse) p)
      ⟨rowAbsSum (intWordProd cert.A w.reverse) p, cert.scaleShift * w.length⟩ := by
    have h := dyadicRowAbsSum_scaled_eqv _ _ _ (dyadicWordProd_eqv cert.scaleShift cert.A w.reverse) p
    rw [List.length_reverse] at h
    exact h
  have hroweq : rowAbsSum (intWordProdRL cert.A w) p = rowAbsSum (intWordProd cert.A w.reverse) p := by
    unfold rowAbsSum; apply finSum_congr; intro j; rw [intWordProdRL_eq_reverse cert.A w p j]
  rw [hroweq] at heqv1
  exact Dyad.le_of_eqv_left (Dyad.eqv_trans heqv1 (Dyad.eqv_symm heqv2)) hrev

-- 4B. Infinite-Alphabet Dyadic Convex-Hull Lifting Meta-Theorem --

/-- One-step polytope contraction for ANY dyadic convex combination of generators (`Q = 1`). -/
theorem convex_polytope_step_int {d m K : Nat} (cert : SwitchedPolytopeCert d m 1 K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    (hall : ∀ b : Fin m, cert.step 0 b = some 0)
    (st : DyadicConvexStep m) (hval : st.valid) (x : Vec d) :
    pow2Int cert.lamShift * vecMaxAbs (matVec (cert.W 0) (matVec (convexStepIntMat cert.A st) x)) ≤
    ((cert.lamNum * 2 ^ (cert.scaleShift + st.q) : Nat) : Int) * vecMaxAbs (matVec (cert.W 0) x) := by
  have hlin : ∀ i : Fin K,
      matVec (cert.W 0) (matVec (convexStepIntMat cert.A st) x) i =
      finSum (fun b : Fin m => (st.weights b : Int) * matVec (cert.W 0) (matVec (cert.A b) x) i) := by
    intro i
    unfold matVec convexStepIntMat
    calc finSum (fun j => cert.W 0 i j * finSum (fun t => finSum (fun b => (st.weights b : Int) * cert.A b j t) * x t))
        = finSum (fun j => cert.W 0 i j * finSum (fun t => finSum (fun b => ((st.weights b : Int) * cert.A b j t) * x t))) := by
            apply finSum_congr; intro j; congr 1; apply finSum_congr; intro t; rw [finSum_mul_right]
      _ = finSum (fun j => cert.W 0 i j * finSum (fun b => finSum (fun t => ((st.weights b : Int) * cert.A b j t) * x t))) := by
            apply finSum_congr; intro j; congr 1; exact finSum_swap _
      _ = finSum (fun j => finSum (fun b => cert.W 0 i j * finSum (fun t => ((st.weights b : Int) * cert.A b j t) * x t))) := by
            apply finSum_congr; intro j; rw [← finSum_mul_left]
      _ = finSum (fun b => finSum (fun j => cert.W 0 i j * finSum (fun t => ((st.weights b : Int) * cert.A b j t) * x t))) :=
            finSum_swap _
      _ = finSum (fun b => (st.weights b : Int) * finSum (fun j => cert.W 0 i j * finSum (fun t => cert.A b j t * x t))) := by
            apply finSum_congr; intro b
            rw [← finSum_mul_left]
            apply finSum_congr; intro j
            have hinner : finSum (fun t => ((st.weights b : Int) * cert.A b j t) * x t) =
                          (st.weights b : Int) * finSum (fun t => cert.A b j t * x t) := by
              rw [← finSum_mul_left]
              apply finSum_congr; intro t; rw [Int.mul_assoc]
            rw [hinner]; ac_rfl
  apply mul_vecMaxAbs_le (Int.mul_nonneg (Int.natCast_nonneg _) (vecMaxAbs_nonneg _))
  intro i
  rw [hlin i]
  have htri : iabs (finSum (fun b : Fin m => (st.weights b : Int) * matVec (cert.W 0) (matVec (cert.A b) x) i)) ≤
      finSum (fun b : Fin m => (st.weights b : Int) * iabs (matVec (cert.W 0) (matVec (cert.A b) x) i)) := by
    calc iabs (finSum _)
        ≤ finSum (fun b => iabs ((st.weights b : Int) * matVec (cert.W 0) (matVec (cert.A b) x) i)) :=
            iabs_finSum_le _
      _ = finSum (fun b => (st.weights b : Int) * iabs (matVec (cert.W 0) (matVec (cert.A b) x) i)) := by
            apply finSum_congr; intro b; rw [iabs_mul, iabs_natCast]
  have h1 := Int.mul_le_mul_of_nonneg_left htri (pow2Int_nonneg cert.lamShift)
  rw [← finSum_mul_left] at h1
  have h2 : finSum (fun b : Fin m => pow2Int cert.lamShift * ((st.weights b : Int) * iabs (matVec (cert.W 0) (matVec (cert.A b) x) i))) ≤
      finSum (fun b : Fin m => (st.weights b : Int) * (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int) * vecMaxAbs (matVec (cert.W 0) x))) := by
    apply finSum_le_finSum; intro b
    rw [Int.mul_left_comm]
    apply Int.mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
    have hstep_b := polytope_step_int cert hchk (hall b) x
    exact Int.le_trans (Int.mul_le_mul_of_nonneg_left (iabs_le_vecMaxAbs _ i) (pow2Int_nonneg _)) hstep_b
  rw [finSum_mul_right, finSum_natCast, hval] at h2
  have heqR : ((2 ^ st.q : Nat) : Int) * (((cert.lamNum * 2 ^ cert.scaleShift : Nat) : Int) * vecMaxAbs (matVec (cert.W 0) x)) =
      ((cert.lamNum * 2 ^ (cert.scaleShift + st.q) : Nat) : Int) * vecMaxAbs (matVec (cert.W 0) x) := by
    rw [← Int.mul_assoc]
    congr 1
    rw [← Int.natCast_mul]
    congr 1
    rw [Nat.pow_add]; ac_rfl
  rw [heqR] at h2
  exact Int.le_trans h1 h2

/-- Inductive polytope norm contraction for arbitrary-length dyadic convex-combination sequences. -/
theorem convex_polytope_seq_norm {d m K : Nat} (cert : SwitchedPolytopeCert d m 1 K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    (hall : ∀ b : Fin m, cert.step 0 b = some 0) :
    ∀ (ws : List (DyadicConvexStep m)), (∀ st ∈ ws, st.valid) → ∀ (x : Vec d),
      (pow2Int cert.lamShift) ^ ws.length * vecMaxAbs (matVec (cert.W 0) (matVec (convexIntProd cert.A ws) x)) ≤
      ((cert.lamNum : Int) ^ ws.length * pow2Int (convexShiftSum cert.scaleShift ws)) *
        vecMaxAbs (matVec (cert.W 0) x) := by
  intro ws
  induction ws with
  | nil =>
    intro _ x
    have hid : matVec (convexIntProd cert.A []) x = x := by funext i; exact matVec_matId x i
    rw [hid]
    simp [convexShiftSum, pow2Int_zero, Int.pow_zero]
  | cons st rest ih =>
    intro hvals x
    have hst : st.valid := hvals st (List.Mem.head _)
    have hrest : ∀ s ∈ rest, s.valid := fun s hs => hvals s (List.Mem.tail _ hs)
    have h1 := convex_polytope_step_int cert hchk hall st hst x
    have h2 := ih hrest (matVec (convexStepIntMat cert.A st) x)
    have heq_vec : matVec (convexIntProd cert.A (st :: rest)) x =
                   matVec (convexIntProd cert.A rest) (matVec (convexStepIntMat cert.A st) x) := by
      funext i; exact matVec_matMul (convexIntProd cert.A rest) (convexStepIntMat cert.A st) x i
    rw [heq_vec, List.length_cons, Int.pow_succ, Int.pow_succ, convexShiftSum, pow2Int_add]
    have hR_nn : 0 ≤ (cert.lamNum : Int) ^ rest.length * pow2Int (convexShiftSum cert.scaleShift rest) :=
      Int.mul_nonneg (int_pow_nonneg (Int.natCast_nonneg _) rest.length) (pow2Int_nonneg _)
    calc ((pow2Int cert.lamShift) ^ rest.length * pow2Int cert.lamShift) *
            vecMaxAbs (matVec (cert.W 0) (matVec (convexIntProd cert.A rest) (matVec (convexStepIntMat cert.A st) x)))
        = pow2Int cert.lamShift *
            ((pow2Int cert.lamShift) ^ rest.length *
              vecMaxAbs (matVec (cert.W 0) (matVec (convexIntProd cert.A rest) (matVec (convexStepIntMat cert.A st) x)))) := by ac_rfl
      _ ≤ pow2Int cert.lamShift *
            (((cert.lamNum : Int) ^ rest.length * pow2Int (convexShiftSum cert.scaleShift rest)) *
              vecMaxAbs (matVec (cert.W 0) (matVec (convexStepIntMat cert.A st) x))) :=
            Int.mul_le_mul_of_nonneg_left h2 (pow2Int_nonneg _)
      _ = ((cert.lamNum : Int) ^ rest.length * pow2Int (convexShiftSum cert.scaleShift rest)) *
            (pow2Int cert.lamShift * vecMaxAbs (matVec (cert.W 0) (matVec (convexStepIntMat cert.A st) x))) := by ac_rfl
      _ ≤ ((cert.lamNum : Int) ^ rest.length * pow2Int (convexShiftSum cert.scaleShift rest)) *
            (((cert.lamNum * 2 ^ (cert.scaleShift + st.q) : Nat) : Int) * vecMaxAbs (matVec (cert.W 0) x)) :=
            Int.mul_le_mul_of_nonneg_left h1 hR_nn
      _ = (((cert.lamNum : Int) ^ rest.length * (cert.lamNum : Int)) *
            (pow2Int (convexShiftSum cert.scaleShift rest) * pow2Int (cert.scaleShift + st.q))) *
            vecMaxAbs (matVec (cert.W 0) x) := by
            have hsp : ((cert.lamNum * 2 ^ (cert.scaleShift + st.q) : Nat) : Int) =
                       (cert.lamNum : Int) * pow2Int (cert.scaleShift + st.q) := by
              unfold pow2Int; rw [Int.natCast_mul]
            rw [hsp]; ac_rfl

/-- **MAIN SOUNDNESS META-THEOREM 2 (Infinite-Alphabet Dyadic Convex-Hull Contraction):**
    One finite polytope certificate checked by `decide` on `m` vertex matrices AUTOMATICALLY
    certifies uniform exponential contraction for ALL arbitrary-length, time-varying products
    drawn from the ENTIRE INFINITE dyadic convex hull `conv_{Z[1/2]}(M_0, ..., M_{m-1})`! -/
theorem convex_hull_infinite_alphabet_sound {d m K : Nat} (cert : SwitchedPolytopeCert d m 1 K)
    (hchk : checkSwitchedPolytopeCert cert = true)
    (hall : ∀ b : Fin m, cert.step 0 b = some 0)
    (ws : List (DyadicConvexStep m)) (hvals : ∀ st ∈ ws, st.valid) (p : Fin d) :
    Dyad.le (dyadicRowAbsSum (convexDyadicProd cert.scaleShift cert.A ws) p)
              (Dyad.mul (Dyad.ofNat cert.C_const) (Dyad.pow ⟨(cert.lamNum : Int), cert.lamShift⟩ ws.length)) := by
  have hseq := convex_polytope_seq_norm cert hchk hall ws hvals
  have hpowL_nn := int_pow_nonneg (pow2Int_nonneg cert.lamShift) ws.length
  have hpowR_nn : 0 ≤ (cert.lamNum : Int) ^ ws.length * pow2Int (convexShiftSum cert.scaleShift ws) :=
    Int.mul_nonneg (int_pow_nonneg (Int.natCast_nonneg _) ws.length) (pow2Int_nonneg _)
  have hinf := polytope_coercivity_lift cert hchk 0 0 (convexIntProd cert.A ws)
    ((pow2Int cert.lamShift) ^ ws.length)
    ((cert.lamNum : Int) ^ ws.length * pow2Int (convexShiftSum cert.scaleShift ws))
    hpowL_nn hpowR_nn hseq
  have hrow_le : (pow2Int cert.lamShift) ^ ws.length * rowAbsSum (convexIntProd cert.A ws) p ≤
      (cert.C_const : Int) * ((cert.lamNum : Int) ^ ws.length * pow2Int (convexShiftSum cert.scaleShift ws)) :=
    Int.le_trans (Int.mul_le_mul_of_nonneg_left (rowAbsSum_le_matInfNorm _ p) hpowL_nn) hinf
  have heqv : Dyad.eqv
      (dyadicRowAbsSum (convexDyadicProd cert.scaleShift cert.A ws) p)
      ⟨rowAbsSum (convexIntProd cert.A ws) p, convexShiftSum cert.scaleShift ws⟩ :=
    dyadicRowAbsSum_scaled_eqv (convexShiftSum cert.scaleShift ws) _ _
      (convexDyadicProd_eqv cert.scaleShift cert.A ws) p
  apply Dyad.le_of_eqv_left heqv
  unfold Dyad.le Dyad.mul Dyad.ofNat
  rw [Dyad.pow_num, Dyad.pow_shift, Nat.zero_add, pow2Int_mul]
  dsimp only
  have hl : rowAbsSum (convexIntProd cert.A ws) p * (pow2Int cert.lamShift) ^ ws.length =
            (pow2Int cert.lamShift) ^ ws.length * rowAbsSum (convexIntProd cert.A ws) p := by ac_rfl
  have hr : ((cert.C_const : Int) * (cert.lamNum : Int) ^ ws.length) * pow2Int (convexShiftSum cert.scaleShift ws) =
            (cert.C_const : Int) * ((cert.lamNum : Int) ^ ws.length * pow2Int (convexShiftSum cert.scaleShift ws)) := by ac_rfl
  rw [hl, hr]
  exact hrow_le

-- 4C. Switched Invariant-Cone Positivity & Subradius Soundness Meta-Theorems --

/-- One-step invariant cone preservation and lower-margin scaling. -/
theorem cone_step_int {d m Q K : Nat} (cert : SwitchedConeCert d m Q K)
    (hchk : checkSwitchedConeCert cert = true)
    {q q' : Fin Q} {b : Fin m} (hstep : cert.step q b = some q')
    (x : Vec d) (B : Int) (hB : 0 ≤ B)
    (hx : ∀ j : Fin K, B ≤ matVec (cert.W q) x j) :
    ∀ i : Fin K,
      ((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int) * B ≤
      pow2Int cert.lamMinShift * matVec (cert.W q') (matVec (cert.A b) x) i := by
  unfold checkSwitchedConeCert at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, finAll_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨hD, _⟩, hedges⟩, _⟩, _⟩, hrate⟩, _⟩
  have hedge := hedges q b
  rw [hstep] at hedge
  simp only [Bool.and_eq_true, matEqBool_eq_true, finAll_eq_true, decide_eq_true_eq] at hedge
  rcases hedge with ⟨⟨hinter, hnn⟩, hrsum⟩
  intro i
  have hD_step : (cert.LambdaMin : Int) * B ≤
      (cert.D : Int) * matVec (cert.W q') (matVec (cert.A b) x) i := by
    have heq_i : (cert.D : Int) * matVec (cert.W q') (matVec (cert.A b) x) i =
                 matVec (cert.C q b) (matVec (cert.W q) x) i := by
      rw [← matVec_matMul (cert.W q') (cert.A b) x i]
      rw [← matVec_scaleMat (cert.D : Int) (matMul (cert.W q') (cert.A b)) x i]
      rw [← matVec_matMul (cert.C q b) (cert.W q) x i]
      unfold matVec; apply finSum_congr; intro j; rw [hinter i j]
    rw [heq_i]
    unfold matVec
    calc (cert.LambdaMin : Int) * B
        ≤ finSum (cert.C q b i) * B := Int.mul_le_mul_of_nonneg_right (hrsum i) hB
      _ = finSum (fun j => cert.C q b i j * B) := (finSum_mul_right _ _).symm
      _ ≤ finSum (fun j => cert.C q b i j * matVec (cert.W q) x j) := by
            apply finSum_le_finSum; intro j
            exact Int.mul_le_mul_of_nonneg_left (hx j) (hnn i j)
  have hD_pos : (0 : Int) < (cert.D : Int) := by omega
  have hrate_int : (cert.D : Int) * ((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int) ≤
      (cert.LambdaMin : Int) * pow2Int cert.lamMinShift := by
    unfold pow2Int
    have hnat : cert.D * (cert.lamMinNum * 2 ^ cert.scaleShift) ≤ cert.LambdaMin * 2 ^ cert.lamMinShift := by
      have hc : cert.lamMinNum * cert.D * 2 ^ cert.scaleShift =
                cert.D * (cert.lamMinNum * 2 ^ cert.scaleShift) := by ac_rfl
      omega
    have hc := Int.ofNat_le.mpr hnat
    rw [Int.natCast_mul, Int.natCast_mul] at hc
    exact hc
  have hmul : (cert.D : Int) * (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int) * B) ≤
              (cert.D : Int) * (pow2Int cert.lamMinShift * matVec (cert.W q') (matVec (cert.A b) x) i) := by
    calc (cert.D : Int) * (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int) * B)
        = ((cert.D : Int) * ((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) * B := by ac_rfl
      _ ≤ ((cert.LambdaMin : Int) * pow2Int cert.lamMinShift) * B :=
            Int.mul_le_mul_of_nonneg_right hrate_int hB
      _ = pow2Int cert.lamMinShift * ((cert.LambdaMin : Int) * B) := by ac_rfl
      _ ≤ pow2Int cert.lamMinShift * ((cert.D : Int) * matVec (cert.W q') (matVec (cert.A b) x) i) :=
            Int.mul_le_mul_of_nonneg_left hD_step (pow2Int_nonneg _)
      _ = (cert.D : Int) * (pow2Int cert.lamMinShift * matVec (cert.W q') (matVec (cert.A b) x) i) := by ac_rfl
  exact Int.le_of_mul_le_mul_left hmul hD_pos

/-- Inductive cone margin along ANY DFA-accepted word `w`. -/
theorem switched_cone_word_margin {d m Q K : Nat} (cert : SwitchedConeCert d m Q K)
    (hchk : checkSwitchedConeCert cert = true) :
    ∀ (w : List (Fin m)) (q qn : Fin Q) (x : Vec d) (B : Int),
      0 ≤ B → (∀ j : Fin K, B ≤ matVec (cert.W q) x j) →
      runDFA cert.step q w = some qn →
      ∀ i : Fin K,
        (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length * B ≤
        (pow2Int cert.lamMinShift) ^ w.length * matVec (cert.W qn) (matVec (intWordProd cert.A w) x) i := by
  intro w
  induction w with
  | nil =>
    intro q qn x B _ hx hrun i
    simp only [runDFA, Option.some.injEq] at hrun
    subst hrun
    have hid : matVec (intWordProd cert.A []) x = x := by funext j; exact matVec_matId x j
    rw [hid]
    simp [Int.pow_zero, hx i]
  | cons b bs ih =>
    intro q qn x B hB hx hrun i
    simp only [runDFA] at hrun
    cases hstep : cert.step q b with
    | none => rw [hstep] at hrun; cases hrun
    | some q1 =>
      rw [hstep] at hrun
      have h1 := cone_step_int cert hchk hstep x B hB hx
      let y : Vec d := fun j => pow2Int cert.lamMinShift * matVec (cert.A b) x j
      have hy_margin : ∀ j : Fin K,
          ((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int) * B ≤ matVec (cert.W q1) y j := by
        intro j
        rw [matVec_scaleVec]; exact h1 j
      have h2 := ih q1 qn y (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int) * B)
        (Int.mul_nonneg (Int.natCast_nonneg _) hB) hy_margin hrun i
      have hscale_out : matVec (cert.W qn) (matVec (intWordProd cert.A bs) y) i =
          pow2Int cert.lamMinShift * matVec (cert.W qn) (matVec (intWordProd cert.A (b :: bs)) x) i := by
        have hv : matVec (intWordProd cert.A bs) y =
                  fun t => pow2Int cert.lamMinShift * matVec (intWordProd cert.A (b :: bs)) x t := by
          funext t
          simp only [intWordProd]
          rw [matVec_scaleVec, matVec_matMul (intWordProd cert.A bs) (cert.A b) x t]
        rw [hv, matVec_scaleVec]
      rw [hscale_out] at h2
      rw [List.length_cons, Int.pow_succ, Int.pow_succ]
      calc ((((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ bs.length *
              ((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) * B
          = (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ bs.length *
              (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int) * B) := by ac_rfl
        _ ≤ (pow2Int cert.lamMinShift) ^ bs.length *
              (pow2Int cert.lamMinShift * matVec (cert.W qn) (matVec (intWordProd cert.A (b :: bs)) x) i) := h2
        _ = ((pow2Int cert.lamMinShift) ^ bs.length * pow2Int cert.lamMinShift) *
              matVec (cert.W qn) (matVec (intWordProd cert.A (b :: bs)) x) i := by ac_rfl

/-- **MAIN SOUNDNESS META-THEOREM 3 (DFA-Switched Invariant-Cone Strict Positivity & Subradius):**
    If `checkSwitchedConeCert cert = true`, then for EVERY word `w` of arbitrary length accepted
    from `cert.q0`, the exact `Z[1/2]` scalar readout `u · (dyadicWordProd M w · x0)` satisfies:
    `c0 * (lamMinNum / 2^lamMinShift)^|w| ≤_{Z[1/2]} u · (dyadicWordProd M w · x0)`. -/
theorem switched_cone_sound {d m Q K : Nat} (cert : SwitchedConeCert d m Q K)
    (hchk : checkSwitchedConeCert cert = true)
    (qn : Fin Q) (w : List (Fin m)) (hrun : runDFA cert.step cert.q0 w = some qn) :
    Dyad.le
      (Dyad.mul ⟨(cert.c0Num : Int), cert.c0Shift⟩
                  (Dyad.pow ⟨(cert.lamMinNum : Int), cert.lamMinShift⟩ w.length))
      (dyadicVecDot (fun i => Dyad.ofInt (cert.u i))
        (dyadicMatVec (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w)
                      (fun j => Dyad.ofInt (cert.x0 j)))) := by
  have hchk' := hchk
  unfold checkSwitchedConeCert at hchk'
  simp only [Bool.and_eq_true, decide_eq_true_eq, finAll_eq_true] at hchk'
  rcases hchk' with ⟨⟨⟨⟨⟨⟨_, hDu⟩, _⟩, hinit⟩, hread⟩, _⟩, hc0⟩
  have hread_qn := hread qn
  rcases hread_qn with ⟨⟨halpha_nn, hSalpha⟩, hdecomp⟩
  have hmargin := switched_cone_word_margin cert hchk w cert.q0 qn cert.x0 (cert.m0 : Int)
    (Int.natCast_nonneg _) hinit hrun
  let z : Vec d := matVec (intWordProd cert.A w) cert.x0
  have hdot_eq : (cert.D_u : Int) * vecDot cert.u z = vecDot (cert.alpha qn) (matVec (cert.W qn) z) := by
    unfold vecDot matVec
    rw [← finSum_mul_left]
    calc finSum (fun p => (cert.D_u : Int) * (cert.u p * z p))
        = finSum (fun p => ((cert.D_u : Int) * cert.u p) * z p) := by
            apply finSum_congr; intro p; ac_rfl
      _ = finSum (fun p => finSum (fun i => cert.alpha qn i * cert.W qn i p) * z p) := by
            apply finSum_congr; intro p; rw [hdecomp p]
      _ = finSum (fun p => finSum (fun i => (cert.alpha qn i * cert.W qn i p) * z p)) := by
            apply finSum_congr; intro p; rw [finSum_mul_right]
      _ = finSum (fun i => finSum (fun p => (cert.alpha qn i * cert.W qn i p) * z p)) := finSum_swap _
      _ = finSum (fun i => cert.alpha qn i * finSum (fun p => cert.W qn i p * z p)) := by
            apply finSum_congr; intro i
            rw [← finSum_mul_left]
            apply finSum_congr; intro p; ac_rfl
  have hDu_pos : (0 : Int) < (cert.D_u : Int) := by omega
  have hpowL_nn := int_pow_nonneg (Int.natCast_nonneg (cert.lamMinNum * 2 ^ cert.scaleShift)) w.length
  have hstep1 : ((cert.S_alpha * cert.m0 : Nat) : Int) * (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length ≤
      (cert.D_u : Int) * ((pow2Int cert.lamMinShift) ^ w.length * vecDot cert.u z) := by
    rw [Int.mul_left_comm, hdot_eq]
    unfold vecDot
    rw [← finSum_mul_left]
    calc ((cert.S_alpha * cert.m0 : Nat) : Int) * (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length
        = (cert.S_alpha : Int) * ((((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length * (cert.m0 : Int)) := by
            rw [Int.natCast_mul]; ac_rfl
      _ ≤ finSum (cert.alpha qn) * ((((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length * (cert.m0 : Int)) :=
            Int.mul_le_mul_of_nonneg_right hSalpha (Int.mul_nonneg hpowL_nn (Int.natCast_nonneg _))
      _ = finSum (fun i => cert.alpha qn i * ((((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length * (cert.m0 : Int))) :=
            (finSum_mul_right _ _).symm
      _ ≤ finSum (fun i => cert.alpha qn i * ((pow2Int cert.lamMinShift) ^ w.length * matVec (cert.W qn) z i)) := by
            apply finSum_le_finSum; intro i
            exact Int.mul_le_mul_of_nonneg_left (hmargin i) (halpha_nn i)
      _ = finSum (fun i => (pow2Int cert.lamMinShift) ^ w.length * (cert.alpha qn i * matVec (cert.W qn) z i)) := by
            apply finSum_congr; intro i; ac_rfl
  have hc0_int : (cert.D_u : Int) * (cert.c0Num : Int) ≤
      ((cert.S_alpha * cert.m0 : Nat) : Int) * pow2Int cert.c0Shift := by
    unfold pow2Int
    have hnat : cert.D_u * cert.c0Num ≤ (cert.S_alpha * cert.m0) * 2 ^ cert.c0Shift := by
      rw [Nat.mul_comm cert.D_u cert.c0Num]; exact hc0
    have hc := Int.ofNat_le.mpr hnat
    rw [Int.natCast_mul, Int.natCast_mul] at hc
    exact hc
  have hfinal_int : (cert.c0Num : Int) * (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length ≤
      pow2Int cert.c0Shift * ((pow2Int cert.lamMinShift) ^ w.length * vecDot cert.u z) := by
    have hmul : (cert.D_u : Int) * ((cert.c0Num : Int) * (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length) ≤
        (cert.D_u : Int) * (pow2Int cert.c0Shift * ((pow2Int cert.lamMinShift) ^ w.length * vecDot cert.u z)) := by
      calc (cert.D_u : Int) * ((cert.c0Num : Int) * (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length)
          = ((cert.D_u : Int) * (cert.c0Num : Int)) * (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length := by ac_rfl
        _ ≤ (((cert.S_alpha * cert.m0 : Nat) : Int) * pow2Int cert.c0Shift) *
              (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length :=
              Int.mul_le_mul_of_nonneg_right hc0_int hpowL_nn
        _ = pow2Int cert.c0Shift * (((cert.S_alpha * cert.m0 : Nat) : Int) *
              (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length) := by ac_rfl
        _ ≤ pow2Int cert.c0Shift * ((cert.D_u : Int) * ((pow2Int cert.lamMinShift) ^ w.length * vecDot cert.u z)) :=
              Int.mul_le_mul_of_nonneg_left hstep1 (pow2Int_nonneg _)
        _ = (cert.D_u : Int) * (pow2Int cert.c0Shift * ((pow2Int cert.lamMinShift) ^ w.length * vecDot cert.u z)) := by ac_rfl
    exact Int.le_of_mul_le_mul_left hmul hDu_pos
  have heqv_vec : ∀ i : Fin d,
      Dyad.eqv (dyadicMatVec (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w)
                    (fun j => Dyad.ofInt (cert.x0 j)) i)
                 ⟨z i, cert.scaleShift * w.length⟩ := by
    intro i
    unfold dyadicMatVec z matVec
    apply finSumD_scaled_eqv (cert.scaleShift * w.length)
    intro j
    have hm := dyadicWordProd_eqv cert.scaleShift cert.A w i j
    have hmul := Dyad.mul_eqv_congr hm (Dyad.eqv_refl (Dyad.ofInt (cert.x0 j)))
    simp only [Dyad.mul, Dyad.ofInt, Nat.add_zero] at hmul
    exact hmul
  have heqv_dot : Dyad.eqv
      (dyadicVecDot (fun i => Dyad.ofInt (cert.u i))
        (dyadicMatVec (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w)
                      (fun j => Dyad.ofInt (cert.x0 j))))
      ⟨vecDot cert.u z, cert.scaleShift * w.length⟩ := by
    unfold dyadicVecDot vecDot
    apply finSumD_scaled_eqv (cert.scaleShift * w.length)
    intro i
    have hmul := Dyad.mul_eqv_congr (Dyad.eqv_refl (Dyad.ofInt (cert.u i))) (heqv_vec i)
    exact Dyad.eqv_trans hmul (by simp [Dyad.eqv, Dyad.mul, Dyad.ofInt])
  apply Dyad.le_of_eqv_right _ (Dyad.eqv_symm heqv_dot)
  unfold Dyad.le Dyad.mul
  rw [Dyad.pow_num, Dyad.pow_shift, pow2Int_add, pow2Int_mul, pow2Int_mul]
  dsimp only
  have hpow_mul : (((cert.lamMinNum * 2 ^ cert.scaleShift : Nat) : Int)) ^ w.length =
      (cert.lamMinNum : Int) ^ w.length * (pow2Int cert.scaleShift) ^ w.length := by
    rw [Int.natCast_mul]
    unfold pow2Int
    induction w.length with
    | zero => simp [Int.pow_zero]
    | succ k ih => rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, ih]; ac_rfl
  rw [hpow_mul] at hfinal_int
  have hl : ((cert.c0Num : Int) * (cert.lamMinNum : Int) ^ w.length) * (pow2Int cert.scaleShift) ^ w.length =
            (cert.c0Num : Int) * ((cert.lamMinNum : Int) ^ w.length * (pow2Int cert.scaleShift) ^ w.length) := by ac_rfl
  have hr : vecDot cert.u z * (pow2Int cert.c0Shift * (pow2Int cert.lamMinShift) ^ w.length) =
            pow2Int cert.c0Shift * ((pow2Int cert.lamMinShift) ^ w.length * vecDot cert.u z) := by ac_rfl
  rw [hl, hr]
  exact hfinal_int

/-- **COROLLARY 3B (Unconstrained Invariant-Cone Strict Positivity for ALL words `w`):** -/
theorem unconstrained_cone_sound {d m K : Nat} (cert : SwitchedConeCert d m 1 K)
    (hchk : checkSwitchedConeCert cert = true)
    (hall : ∀ b : Fin m, cert.step 0 b = some 0)
    (w : List (Fin m)) :
    Dyad.le
      (Dyad.mul ⟨(cert.c0Num : Int), cert.c0Shift⟩
                  (Dyad.pow ⟨(cert.lamMinNum : Int), cert.lamMinShift⟩ w.length))
      (dyadicVecDot (fun i => Dyad.ofInt (cert.u i))
        (dyadicMatVec (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) w)
                      (fun j => Dyad.ofInt (cert.x0 j)))) := by
  have hq0 : cert.q0 = 0 := Fin.ext (by omega)
  have hrun : runDFA cert.step cert.q0 w = some 0 := by
    rw [hq0]; exact runDFA_unconstrained cert.step hall w
  exact switched_cone_sound cert hchk 0 w hrun

-- 4D. Periodic Exact Eigen-Witness Soundness Meta-Theorem --

/-- Exact `k`-fold power of an eigenvector along `repeatWord w k`. -/
theorem periodic_eigen_pow {d m : Nat} (cert : PeriodicEigenCert d m)
    (hchk : checkPeriodicEigenCert cert = true) :
    ∀ (k : Nat) (i : Fin d),
      matVec (intWordProd cert.A (repeatWord cert.word k)) cert.v i = cert.eig ^ k * cert.v i := by
  unfold checkPeriodicEigenCert at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, finAll_eq_true] at hchk
  rcases hchk with ⟨⟨_, _⟩, heig⟩
  intro k
  induction k with
  | zero =>
    intro i
    simp only [repeatWord, intWordProd, Int.pow_zero, Int.one_mul]
    exact matVec_matId cert.v i
  | succ r ih =>
    intro i
    simp only [repeatWord]
    have happ : ∀ p q, intWordProd cert.A (cert.word ++ repeatWord cert.word r) p q =
        matMul (intWordProd cert.A (repeatWord cert.word r)) (intWordProd cert.A cert.word) p q :=
      intWordProd_append cert.A cert.word (repeatWord cert.word r)
    have h1 : matVec (intWordProd cert.A (cert.word ++ repeatWord cert.word r)) cert.v i =
              matVec (intWordProd cert.A (repeatWord cert.word r)) (matVec (intWordProd cert.A cert.word) cert.v) i := by
      calc matVec (intWordProd cert.A (cert.word ++ repeatWord cert.word r)) cert.v i
          = matVec (matMul (intWordProd cert.A (repeatWord cert.word r)) (intWordProd cert.A cert.word)) cert.v i := by
              unfold matVec; apply finSum_congr; intro j; rw [happ i j]
        _ = matVec (intWordProd cert.A (repeatWord cert.word r)) (matVec (intWordProd cert.A cert.word) cert.v) i :=
              matVec_matMul _ _ _ i
    have h2 : matVec (intWordProd cert.A (repeatWord cert.word r)) (matVec (intWordProd cert.A cert.word) cert.v) i =
              cert.eig * matVec (intWordProd cert.A (repeatWord cert.word r)) cert.v i := by
      have hv_eq : matVec (intWordProd cert.A cert.word) cert.v = fun j => cert.eig * cert.v j := by
        funext j; exact heig j
      rw [hv_eq, matVec_scaleVec]
    rw [h1, h2, ih i, Int.pow_succ]
    ac_rfl

/-- **MAIN SOUNDNESS META-THEOREM 4 (Exact Periodic Eigen-Witness JSR Lower Bound):**
    If `checkPeriodicEigenCert cert = true`, then for EVERY `k : Nat`, the `k`-fold repeated
    word `w_0^k` (length `|w_0| * k`) attains exact `ℓ_∞` operator norm at least
    `(|eig| / 2^(s * |w_0|))^k`! -/
theorem periodic_eigen_sound {d m : Nat} (cert : PeriodicEigenCert d m)
    (hchk : checkPeriodicEigenCert cert = true) (k : Nat) :
    ∃ p : Fin d,
      Dyad.le (Dyad.pow ⟨iabs cert.eig, cert.scaleShift * cert.word.length⟩ k)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b))
                                  (repeatWord cert.word k)) p) := by
  have hchk' := hchk
  unfold checkPeriodicEigenCert at hchk'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk'
  rcases hchk' with ⟨⟨_, hvpos⟩, _⟩
  have hex : ∀ (n : Nat) (v : Vec n), 0 < vecMaxAbs v → ∃ p : Fin n, iabs (v p) = vecMaxAbs v := by
    intro n
    induction n with
    | zero => intro v h; simp [vecMaxAbs] at h
    | succ r ih =>
      intro v h
      simp only [vecMaxAbs] at h ⊢
      by_cases hm : vecMaxAbs (fun i : Fin r => v i.castSucc) ≤ iabs (v (Fin.last r))
      · exact ⟨Fin.last r, (int_max_eq_right hm).symm⟩
      · have hlt : iabs (v (Fin.last r)) < vecMaxAbs (fun i : Fin r => v i.castSucc) :=
          Int.lt_of_not_ge hm
        have hpos' : 0 < vecMaxAbs (fun i : Fin r => v i.castSucc) := by
          have := iabs_nonneg (v (Fin.last r)); omega
        rcases ih (fun i => v i.castSucc) hpos' with ⟨p', hp'⟩
        exact ⟨p'.castSucc, by rw [int_max_eq_left (Int.le_of_lt hlt)]; exact hp'⟩
  rcases hex d cert.v hvpos with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  have hpow := periodic_eigen_pow cert hchk k p
  have hineq : (iabs cert.eig) ^ k * vecMaxAbs cert.v ≤
      rowAbsSum (intWordProd cert.A (repeatWord cert.word k)) p * vecMaxAbs cert.v := by
    calc (iabs cert.eig) ^ k * vecMaxAbs cert.v
        = iabs (cert.eig ^ k) * iabs (cert.v p) := by rw [iabs_pow, hp]
      _ = iabs (cert.eig ^ k * cert.v p) := (iabs_mul _ _).symm
      _ = iabs (matVec (intWordProd cert.A (repeatWord cert.word k)) cert.v p) := by rw [hpow]
      _ ≤ rowAbsSum (intWordProd cert.A (repeatWord cert.word k)) p * vecMaxAbs cert.v :=
            iabs_matVec_le _ _ p
  have hrow_ge : (iabs cert.eig) ^ k ≤ rowAbsSum (intWordProd cert.A (repeatWord cert.word k)) p :=
    Int.le_of_mul_le_mul_right hineq hvpos
  have heqv : Dyad.eqv
      (dyadicRowAbsSum
        (dyadicWordProd (fun b => scaleDyadicMat cert.scaleShift (cert.A b)) (repeatWord cert.word k)) p)
      ⟨rowAbsSum (intWordProd cert.A (repeatWord cert.word k)) p,
        cert.scaleShift * (repeatWord cert.word k).length⟩ :=
    dyadicRowAbsSum_scaled_eqv _ _ _ (dyadicWordProd_eqv cert.scaleShift cert.A (repeatWord cert.word k)) p
  apply Dyad.le_of_eqv_right _ (Dyad.eqv_symm heqv)
  unfold Dyad.le
  rw [Dyad.pow_num, Dyad.pow_shift, repeatWord_length, ← Nat.mul_assoc]
  exact Int.mul_le_mul_of_nonneg_right hrow_ge (pow2Int_nonneg _)

end DyadicMonoidEngine
namespace CertifiedApplications
open DyadicMonoidEngine

theorem freeStep_all {m : Nat} (b : Fin m) : freeStep (m := m) 0 b = some 0 := rfl

-- ----------------------------------------------------------------------------
-- FLAGSHIP THEOREM 1: Non-Ellipsoidal 2D Binary Matrix Monoid
--   M0 = (1/4) [[3, 3], [-1, 0]],  M1 = (1/4) [[0, 1], [-3, 3]]
--   * Naive norms fail: ||M0||_∞ = ||M1||_∞ = 3/2 > 1, ||M0||_2 = ||M1||_2 > 1.
--   * NO quadratic (ellipsoidal) Lyapunov norm Q > 0 exists even for rate <= 1!
--   * YET our 4-facet exact Z[1/2] polytope cert proves JSR <= 15/16 < 1 for ALL
--     infinite words AND ALL infinite time-varying dyadic convex combinations!
--   * Two-sided kernel-certified JSR sandwich: 3/4 <= rho(M0, M1) <= 15/16 < 1 < rho_quad.
-- ----------------------------------------------------------------------------

/-- Kernel-checked finite certificate verification for Theorem 1 (`by decide`, zero `native_decide`). -/
theorem thm1_cert_valid : checkSwitchedPolytopeCert cert1 = true := by decide

/-- **THEOREM 1A (Unconstrained Infinite Contraction):**
    For EVERY finite binary word `w` of ANY length `n : Nat`,
    `‖(dyadicWordProd M w)_p‖_1 ≤_{Z[1/2]} 4 * (15/16)^|w|`. -/
theorem thm1_unconstrained_contraction (w : List (Fin 2)) (p : Fin 2) :
    Dyad.le (dyadicRowAbsSum (dyadicWordProd (fun b => scaleDyadicMat 2 (thm1_A b)) w) p)
              (Dyad.mul (Dyad.ofNat 4) (Dyad.pow ⟨15, 4⟩ w.length)) :=
  unconstrained_polytope_sound cert1 thm1_cert_valid freeStep_all w p

/-- **THEOREM 1A-RL (Right-to-Left Product `M_{b_1} * ... * M_{b_n}` Contraction):** -/
theorem thm1_unconstrained_contraction_RL (w : List (Fin 2)) (p : Fin 2) :
    Dyad.le (dyadicRowAbsSum (dyadicWordProdRL (fun b => scaleDyadicMat 2 (thm1_A b)) w) p)
              (Dyad.mul (Dyad.ofNat 4) (Dyad.pow ⟨15, 4⟩ w.length)) :=
  unconstrained_polytope_sound_RL cert1 thm1_cert_valid freeStep_all w p

/-- **THEOREM 1B (Uniform Exponential Decay to 0 in Z[1/2]):**
    For EVERY precision `2^{-k}`, there exists `N` such that ALL binary words of length `≥ N`
    have exact operator norm strictly `< 2^{-k}`. -/
theorem thm1_uniform_decay (k : Nat) :
    ∃ N : Nat, ∀ (w : List (Fin 2)), N ≤ w.length → ∀ p : Fin 2,
      Dyad.lt (dyadicRowAbsSum (dyadicWordProd (fun b => scaleDyadicMat 2 (thm1_A b)) w) p)
                ⟨1, k⟩ := by
  rcases Dyad.strict_contraction_decay 4 15 4 k (by omega) with ⟨N, hN⟩
  refine ⟨N, fun w hw p => Dyad.lt_of_le_of_lt (thm1_unconstrained_contraction w p) (hN w.length hw)⟩

/-- **THEOREM 1C (Infinite-Alphabet Dyadic Convex-Hull Contraction):**
    Every arbitrary-length sequence of time-varying dyadic convex combinations of `M0, M1`
    contracts at the exact same rate `4 * (15/16)^n`. -/
theorem thm1_convex_hull_contraction (ws : List (DyadicConvexStep 2))
    (hvals : ∀ st ∈ ws, st.valid) (p : Fin 2) :
    Dyad.le (dyadicRowAbsSum (convexDyadicProd 2 thm1_A ws) p)
              (Dyad.mul (Dyad.ofNat 4) (Dyad.pow ⟨15, 4⟩ ws.length)) :=
  convex_hull_infinite_alphabet_sound cert1 thm1_cert_valid freeStep_all ws hvals p

theorem thm1_lower_valid : checkPeriodicEigenCert cert1_lower = true := by decide

theorem thm1_jsr_lower_bound (k : Nat) :
    ∃ p : Fin 2,
      Dyad.le (Dyad.pow ⟨9, 4⟩ k)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat 2 (thm1_A b))
                                  (repeatWord cert1_lower.word k)) p) :=
  periodic_eigen_sound cert1_lower thm1_lower_valid k

theorem thm1_no_quadratic_lyapunov (a b c : Int) (ha : 0 < a) (hc : 0 < c) :
    ¬ ((∀ x : Vec 2, quadForm2 a b c (matVec (thm1_A 0) x) ≤ 16 * quadForm2 a b c x) ∧
       (∀ x : Vec 2, quadForm2 a b c (matVec (thm1_A 1) x) ≤ 16 * quadForm2 a b c x)) := by
  rintro ⟨h0, h1⟩
  have hv0 := h0 (vecOfList 2 [1, 1])
  have hv1 := h1 (vecOfList 2 [1, -1])
  have heval0 : matVec (thm1_A 0) (vecOfList 2 [1, 1]) 0 = 6 ∧
                matVec (thm1_A 0) (vecOfList 2 [1, 1]) 1 = -1 := by decide
  have heval1 : matVec (thm1_A 1) (vecOfList 2 [1, -1]) 0 = -1 ∧
                matVec (thm1_A 1) (vecOfList 2 [1, -1]) 1 = -6 := by decide
  unfold quadForm2 at hv0 hv1
  rw [heval0.1, heval0.2] at hv0
  rw [heval1.1, heval1.2] at hv1
  have hvec0 : vecOfList 2 [1, 1] 0 = 1 ∧ vecOfList 2 [1, 1] 1 = 1 := by decide
  have hvec1 : vecOfList 2 [1, -1] 0 = 1 ∧ vecOfList 2 [1, -1] 1 = -1 := by decide
  rw [hvec0.1, hvec0.2] at hv0
  rw [hvec1.1, hvec1.2] at hv1
  omega

theorem thm1_sharp_valid : checkPeriodicEigenCert cert1_sharp = true := by decide

theorem thm1_sharpness_unbounded (B : Nat) :
    ∃ (k : Nat) (p : Fin 2),
      Dyad.lt (Dyad.ofNat B)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat 2 (thm1_sharp_A b))
                                  (repeatWord cert1_sharp.word k)) p) := by
  rcases Dyad.strict_explosion_unbounded 25 4 B (by omega) with ⟨k, hk⟩
  rcases periodic_eigen_sound cert1_sharp thm1_sharp_valid k with ⟨p, hp⟩
  have hlt : Dyad.lt (Dyad.ofNat B) (dyadicRowAbsSum
      (dyadicWordProd (fun b => scaleDyadicMat 2 (thm1_sharp_A b)) (repeatWord cert1_sharp.word k)) p) := by
    unfold Dyad.lt Dyad.le at *
    have hpos1 := pow2Int_pos (Dyad.pow ⟨25, 4⟩ k).shift
    have hpos2 := pow2Int_pos (Dyad.ofNat B).shift
    have hpos3 := pow2Int_pos (dyadicRowAbsSum
      (dyadicWordProd (fun b => scaleDyadicMat 2 (thm1_sharp_A b)) (repeatWord cert1_sharp.word k)) p).shift
    have h1 := Int.mul_lt_mul_of_pos_right hk hpos3
    have h2 := Int.mul_le_mul_of_nonneg_right hp (by omega : 0 ≤ pow2Int (Dyad.ofNat B).shift)
    have hmid : (Dyad.ofNat B).num * pow2Int (dyadicRowAbsSum
        (dyadicWordProd (fun b => scaleDyadicMat 2 (thm1_sharp_A b)) (repeatWord cert1_sharp.word k)) p).shift *
        pow2Int (Dyad.pow ⟨25, 4⟩ k).shift <
      (dyadicRowAbsSum
        (dyadicWordProd (fun b => scaleDyadicMat 2 (thm1_sharp_A b)) (repeatWord cert1_sharp.word k)) p).num *
        pow2Int (Dyad.ofNat B).shift * pow2Int (Dyad.pow ⟨25, 4⟩ k).shift := by
      calc (Dyad.ofNat B).num * pow2Int _ * pow2Int (Dyad.pow ⟨25, 4⟩ k).shift
          = ((Dyad.ofNat B).num * pow2Int (Dyad.pow ⟨25, 4⟩ k).shift) * pow2Int _ := by ac_rfl
        _ < ((Dyad.pow ⟨25, 4⟩ k).num * pow2Int (Dyad.ofNat B).shift) * pow2Int _ := h1
        _ = ((Dyad.pow ⟨25, 4⟩ k).num * pow2Int _) * pow2Int (Dyad.ofNat B).shift := by ac_rfl
        _ ≤ ((dyadicRowAbsSum _ p).num * pow2Int (Dyad.pow ⟨25, 4⟩ k).shift) * pow2Int (Dyad.ofNat B).shift := h2
        _ = (dyadicRowAbsSum _ p).num * pow2Int (Dyad.ofNat B).shift * pow2Int (Dyad.pow ⟨25, 4⟩ k).shift := by ac_rfl
    exact Int.lt_of_mul_lt_mul_right hmid (by omega)
  exact ⟨k, p, hlt⟩

-- ----------------------------------------------------------------------------
-- FLAGSHIP THEOREM 2: Infinite-Parameter Dubuc-Deslauriers 4-Point Dyadic Subdivision
--   Certifies uniform C^1 second-difference contraction `2 * T_b(ω)` across the ENTIRE
--   infinite dyadic tension interval `ω ∈ [1/32, 5/32] ∩ Z[1/2]` (including classical
--   Dubuc-Deslauriers `ω = 1/16` AND `ω = 5/32` where `||2 T_b(5/32)||_∞ = 5/4 > 1`!),
--   even for arbitrary non-stationary time-varying sequences `(ω_1, ..., ω_n)`!
--   Single 10-facet exact integer polytope (`D = 3`, `Lambda = 90`, exact rate `15/16`).
-- ----------------------------------------------------------------------------

/-- Kernel-checked finite certificate verification for Theorem 2 (`by decide`). -/
theorem thm2_cert_valid : checkSwitchedPolytopeCert cert2 = true := by decide

theorem ddStep_valid (b : Fin 2) (q p : Nat) (hp : p ≤ 2 ^ q) : (ddStep b q p).valid := by
  unfold DyadicConvexStep.valid ddStep
  by_cases hb : b.val = 0
  · simp only [hb, ↓reduceIte, finSumNat, Fin.val_last, Fin.val_castSucc]
    omega
  · simp only [hb, ↓reduceIte, finSumNat, Fin.val_last, Fin.val_castSucc]
    omega

/-- **THEOREM 2A (Doubly-Infinite Dubuc-Deslauriers 4-Point Dyadic Subdivision C^1 Contraction):**
    For EVERY arbitrary-length sequence of binary subdivision bits `b_j ∈ {0, 1}` AND arbitrary
    (possibly non-stationary / time-varying!) dyadic tension parameters `ω_j ∈ [1/32, 5/32] ∩ Z[1/2]`
    (parameterized by `q_j : Nat` and `p_j ≤ 2^{q_j}`), the 4D second-difference cascade satisfies:
    `‖(2 T_{b_n}(ω_n) ··· 2 T_{b_1}(ω_1))_r‖_1 ≤_{Z[1/2]} 2 * (15/16)^n`. -/
theorem thm2_dd_infinite_interval_contraction
    (steps : List (Fin 2 × Nat × Nat))
    (hvalid : ∀ s ∈ steps, s.2.2 ≤ 2 ^ s.2.1) (r : Fin 4) :
    Dyad.le
      (dyadicRowAbsSum (convexDyadicProd 5 dd_A (steps.map (fun s => ddStep s.1 s.2.1 s.2.2))) r)
      (Dyad.mul (Dyad.ofNat 2) (Dyad.pow ⟨15, 4⟩ steps.length)) := by
  have hmap_len : (steps.map (fun s => ddStep s.1 s.2.1 s.2.2)).length = steps.length := List.length_map _
  rw [← hmap_len]
  apply convex_hull_infinite_alphabet_sound cert2 thm2_cert_valid freeStep_all
  intro st hst
  rcases List.mem_map.mp hst with ⟨⟨b, q, p⟩, hmem, rfl⟩
  exact ddStep_valid b q p (hvalid ⟨b, q, p⟩ hmem)

theorem thm2_sharp_valid : checkPeriodicEigenCert cert2_sharp = true := by decide

theorem thm2_sharpness_no_contraction_at_quarter (k : Nat) :
    ∃ p : Fin 4,
      Dyad.le (Dyad.pow ⟨2, 1⟩ k)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat 1 (dd_quarter_A b))
                                  (repeatWord cert2_sharp.word k)) p) :=
  periodic_eigen_sound cert2_sharp thm2_sharp_valid k

-- ----------------------------------------------------------------------------
-- FLAGSHIP THEOREM 3: Signed-Entry 3×3 Non-Simplicial Invariant-Cone Strict Positivity
--   M0 = (1/4) [[7, -1, -1], [-2, 3, -1], [1, -2, 2]]
--   M1 = (1/4) [[7, -1, -1], [2, -2, 1], [-1, -1, 2]]
--   EVERY SINGLE ROW of BOTH matrices contains negative entries!
--   YET our 4-facet Lorentz ℓ_∞ pyramid cone cert proves:
--     ∀ w : List (Fin 2), (5/4)^|w| ≤_{Z[1/2]} u · (M_{w_n} ··· M_{w_1} · x0),
--   certifying BOTH strict positivity AND joint spectral subradius >= 5/4!
-- ----------------------------------------------------------------------------

/-- Kernel-checked finite certificate verification for Theorem 3 (`by decide`). -/
theorem thm3_cert_valid : checkSwitchedConeCert cert3 = true := by decide

/-- **THEOREM 3A (Strict Positivity & Exponential Subradius `≥ 5/4` for Signed-Entry Matrices):** -/
theorem thm3_signed_cone_subradius (w : List (Fin 2)) :
    Dyad.le
      (Dyad.mul ⟨1, 0⟩ (Dyad.pow ⟨5, 2⟩ w.length))
      (dyadicVecDot (fun i => Dyad.ofInt (cert3.u i))
        (dyadicMatVec (dyadicWordProd (fun b => scaleDyadicMat 2 (thm3_A b)) w)
                      (fun j => Dyad.ofInt (cert3.x0 j)))) :=
  unconstrained_cone_sound cert3 thm3_cert_valid freeStep_all w

/-- **THEOREM 3B (Strict Positivity `> 0` for ALL Infinite Binary Words):** -/
theorem thm3_strict_positivity (w : List (Fin 2)) :
    Dyad.lt Dyad.zero
      (dyadicVecDot (fun i => Dyad.ofInt (cert3.u i))
        (dyadicMatVec (dyadicWordProd (fun b => scaleDyadicMat 2 (thm3_A b)) w)
                      (fun j => Dyad.ofInt (cert3.x0 j)))) := by
  have hge := thm3_signed_cone_subradius w
  have hpos : Dyad.lt Dyad.zero (Dyad.mul ⟨1, 0⟩ (Dyad.pow ⟨5, 2⟩ w.length)) := by
    unfold Dyad.lt Dyad.zero Dyad.mul
    rw [Dyad.pow_num, Dyad.pow_shift, pow2Int_zero, Int.zero_mul, Int.mul_one, Int.one_mul]
    dsimp only
    induction w.length with
    | zero => simp [Int.pow_zero]
    | succ k ih => rw [Int.pow_succ]; exact Int.mul_pos ih (by omega)
  exact Dyad.lt_of_lt_of_le hpos hge

/-- **THEOREM 3C (Sharpness — Outside Cone `x_bad = [1, 4, 4]` Turns Negative in 1 Step):** -/
theorem thm3_sharpness_outside_cone :
    vecDot cert3.u (matVec (thm3_A 0) (vecOfList 3 [1, 4, 4])) = -1 := by decide

-- ----------------------------------------------------------------------------
-- FLAGSHIP THEOREM 4: Automaton-Switched NAF / No-`11` Binary Subshift Phase Transition
--   M0 = (1/4) [[1, 4], [-1, 1]],  M1 = (1/4) [[5, 0], [1, 1]]
--   * Both generators exceed 1 in ℓ_∞ norm (`||M0||_∞ = ||M1||_∞ = 5/4 > 1`).
--   * Unconstrained monoid EXPLODES exponentially: `||M1^k||_∞ >= (5/4)^k -> ∞`.
--   * ALL NAF / Fibonacci (no adjacent `11`) binary words CONTRACT exponentially to 0:
--       `noAdjacentOnes w = true -> ||P(w)||_∞ <= 3 * (7/8)^|w| -> 0`!
--   * Sharpness: perturbing `A0[0][1]` from `4 -> 16` makes the valid no-`11` periodic
--     word `(1, 0)^k` explode exponentially at rate `(17/16)^k -> ∞`!
-- ----------------------------------------------------------------------------

/-- Bridge lemma: any word with `noAdjacentOnes w = true` is accepted by `nafStep` from state 0
    (and from state 1 if it does not begin with `1`). -/
theorem noAdjacentOnes_runDFA :
    ∀ w : List (Fin 2), noAdjacentOnes w = true →
      (∃ qn : Fin 2, runDFA nafStep 0 w = some qn) ∧
      ((∀ rest, w ≠ ⟨1, by omega⟩ :: rest) → ∃ qn : Fin 2, runDFA nafStep 1 w = some qn) := by
  intro w
  induction w with
  | nil =>
    intro _
    exact ⟨⟨0, rfl⟩, fun _ => ⟨1, rfl⟩⟩
  | cons a rest ih =>
    intro hno
    cases rest with
    | nil =>
      constructor
      · match a with
        | ⟨0, _⟩ => exact ⟨0, rfl⟩
        | ⟨1, _⟩ => exact ⟨1, rfl⟩
      · intro hnot1
        match a with
        | ⟨0, _⟩ => exact ⟨0, rfl⟩
        | ⟨1, _⟩ => exact False.elim (hnot1 [] rfl)
    | cons b bs =>
      simp only [noAdjacentOnes, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
                 decide_eq_false_iff_not] at hno
      rcases hno with ⟨hab, hrest⟩
      rcases ih hrest with ⟨⟨qn0, hrun0⟩, hrun1⟩
      constructor
      · match a with
        | ⟨0, _⟩ => exact ⟨qn0, by simpa [runDFA, nafStep] using hrun0⟩
        | ⟨1, _⟩ =>
          have hb0 : b ≠ ⟨1, by omega⟩ := by
            intro hb1; subst hb1
            cases hab with
            | inl h => exact h rfl
            | inr h => exact h rfl
          have hnot1' : ∀ r, b :: bs ≠ ⟨1, by omega⟩ :: r := by
            intro r heq; exact hb0 (List.cons.inj heq).1
          rcases hrun1 hnot1' with ⟨qn1, hqn1⟩
          exact ⟨qn1, by simpa [runDFA, nafStep] using hqn1⟩
      · intro hnot1
        match a with
        | ⟨0, _⟩ => exact ⟨qn0, by simpa [runDFA, nafStep] using hrun0⟩
        | ⟨1, _⟩ => exact False.elim (hnot1 (b :: bs) rfl)

/-- Kernel-checked finite certificate verification for Theorem 4 (`by decide`). -/
theorem thm4_cert_valid : checkSwitchedPolytopeCert cert4 = true := by decide

/-- **THEOREM 4A (NAF / No-`11` Binary Subshift Exponential Contraction):**
    For EVERY binary word `w` of arbitrary length with NO adjacent `11` (`noAdjacentOnes w = true`),
    `‖(dyadicWordProd M w)_p‖_1 ≤_{Z[1/2]} 3 * (7/8)^|w|`. -/
theorem thm4_naf_contraction (w : List (Fin 2)) (hno : noAdjacentOnes w = true) (p : Fin 2) :
    Dyad.le (dyadicRowAbsSum (dyadicWordProd (fun b => scaleDyadicMat 2 (thm4_A b)) w) p)
              (Dyad.mul (Dyad.ofNat 3) (Dyad.pow ⟨7, 3⟩ w.length)) := by
  rcases (noAdjacentOnes_runDFA w hno).1 with ⟨qn, hrun⟩
  exact switched_polytope_sound cert4 thm4_cert_valid 0 qn w hrun p

theorem thm4_explode_valid : checkPeriodicEigenCert cert4_explode = true := by decide

theorem thm4_unconstrained_lower (k : Nat) :
    ∃ p : Fin 2,
      Dyad.le (Dyad.pow ⟨5, 2⟩ k)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat 2 (thm4_A b))
                                  (repeatWord cert4_explode.word k)) p) :=
  periodic_eigen_sound cert4_explode thm4_explode_valid k

theorem thm4_sharp_valid : checkPeriodicEigenCert cert4_sharp = true := by decide

theorem repeat_10_noAdjacentOnes : ∀ k : Nat, noAdjacentOnes (repeatWord [⟨1, by omega⟩, ⟨0, by omega⟩] k) = true
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    have ih := repeat_10_noAdjacentOnes (k + 1)
    simpa [repeatWord, noAdjacentOnes] using ih

theorem thm4_sharpness_naf_explosion (k : Nat) :
    noAdjacentOnes (repeatWord cert4_sharp.word k) = true ∧
    ∃ p : Fin 2,
      Dyad.le (Dyad.pow ⟨17, 4⟩ k)
                (dyadicRowAbsSum
                  (dyadicWordProd (fun b => scaleDyadicMat 2 (thm4_sharp_A b))
                                  (repeatWord cert4_sharp.word k)) p) :=
  ⟨repeat_10_noAdjacentOnes k, periodic_eigen_sound cert4_sharp thm4_sharp_valid k⟩

-- ----------------------------------------------------------------------------
-- SECTION 5E: Non-Vacuity Witnesses & 9 Kernel-Checked Adversarial Mutation Tests
-- ----------------------------------------------------------------------------

/-- Non-vacuity witness 1: concrete classical Dubuc-Deslauriers parameter `ω = 1/16` (`q=2, p=1`)
    and `ω = 5/32` (`q=0, p=1`) genuinely inhabit Theorem 2's infinite interval hypothesis. -/
example :
    let seq : List (Fin 2 × Nat × Nat) := [(0, 2, 1), (1, 0, 1), (0, 3, 5)]
    ∀ s ∈ seq, s.2.2 ≤ 2 ^ s.2.1 := by decide

/-- Non-vacuity witness 2: concrete length-6 no-`11` binary word inhabits Theorem 4's hypothesis. -/
example : noAdjacentOnes [0, 1, 0, 1, 0, 0] = true := by decide

/-- Non-vacuity witness 3: Theorem 3's matrices genuinely have negative entries in EVERY row! -/
example :
    thm3_A 0 0 1 < 0 ∧ thm3_A 0 1 0 < 0 ∧ thm3_A 0 2 1 < 0 ∧
    thm3_A 1 0 1 < 0 ∧ thm3_A 1 1 1 < 0 ∧ thm3_A 1 2 0 < 0 := by decide

/-- Non-vacuity witness 4: Theorem 1's naive norms exceed 1 (`rowAbsSum > 4` at scale 4). -/
example : rowAbsSum (thm1_A 0) 0 = 6 ∧ rowAbsSum (thm1_A 1) 1 = 6 := by decide

-- 9 Kernel-Checked Adversarial Mutation Tests (`checkCert bad = false`) --

theorem mut1_bad_intertwining_rejected : checkSwitchedPolytopeCert bad_cert1_intertwining = false := by decide

theorem mut2_bad_lambda_rejected : checkSwitchedPolytopeCert bad_cert1_lambda = false := by decide

theorem mut3_bad_coercivity_rejected : checkSwitchedPolytopeCert bad_cert1_coercivity = false := by decide

theorem mut4_bad_rate_rejected : checkSwitchedPolytopeCert bad_cert1_rate = false := by decide

theorem mut5_bad_dd_endpoint_rejected : checkSwitchedPolytopeCert bad_cert2_endpoint = false := by decide

theorem mut6_bad_cone_neg_rejected : checkSwitchedConeCert bad_cert3_negative_C = false := by decide

theorem mut7_bad_cone_subradius_rejected : checkSwitchedConeCert bad_cert3_subradius = false := by decide

theorem mut8_bad_naf_dfa_rejected : checkSwitchedPolytopeCert bad_cert4_unconstrained_dfa = false := by decide

theorem mut9_bad_eigen_rejected : checkPeriodicEigenCert bad_cert4_eigen = false := by decide

end CertifiedApplications
