import ArxFibonacciIsospectrality.Defs

namespace ArxFibonacciIsospectrality

/-! ### Part 1: General iteration and divisibility lemmas -/

private theorem iter_add {α : Type} (F : α → α) (m n : Nat) (x : α) :
    iter F (m + n) x = iter F n (iter F m x) := by
  induction m generalizing x with
  | zero => simp [iter]
  | succ m ih =>
    rw [Nat.succ_add]
    exact ih (F x)

private theorem iter_mul_fixed {α : Type} (F : α → α) (p : α) (a k : Nat)
    (ha : iter F a p = p) : iter F (a * k) p = p := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [Nat.mul_succ, iter_add, ih, ha]

private theorem iter_dvd_fixed {α : Type} (F : α → α) (p : α) (a b : Nat)
    (ha : iter F a p = p) (hdvd : a ∣ b) : iter F b p = p := by
  rcases hdvd with ⟨k, rfl⟩
  exact iter_mul_fixed F p a k ha

private theorem iter_mod_fixed {α : Type} (F : α → α) (p : α) (a b : Nat)
    (ha : iter F a p = p) (hb : iter F b p = p) : iter F (b % a) p = p := by
  have hmul : iter F (a * (b / a)) p = p := iter_mul_fixed F p a (b / a) ha
  calc iter F (b % a) p
      = iter F (b % a) (iter F (a * (b / a)) p) := by rw [hmul]
    _ = iter F (a * (b / a) + b % a) p := by rw [← iter_add]
    _ = iter F b p := by rw [Nat.div_add_mod]
    _ = p := hb

private theorem iter_gcd_fixed {α : Type} (F : α → α) (p : α) (a b : Nat)
    (ha : iter F a p = p) (hb : iter F b p = p) : iter F (Nat.gcd a b) p = p := by
  suffices h : ∀ n a b : Nat, a ≤ n → iter F a p = p → iter F b p = p → iter F (Nat.gcd a b) p = p from
    h a a b (Nat.le_refl a) ha hb
  intro n
  induction n with
  | zero =>
    intro a b hle _ hb'
    have ha0 : a = 0 := by omega
    subst ha0
    simpa [Nat.gcd_zero_left] using hb'
  | succ n ih =>
    intro a b hle ha' hb'
    cases a with
    | zero => simpa [Nat.gcd_zero_left] using hb'
    | succ a' =>
      rw [Nat.gcd_rec]
      have hlt : b % (a' + 1) < a' + 1 := Nat.mod_lt b (by omega)
      exact ih (b % (a' + 1)) (a' + 1) (by omega) (iter_mod_fixed F p (a' + 1) b ha' hb') ha'

private theorem minPeriod_unique {α : Type} {F : α → α} {p : α} {L1 L2 : Nat}
    (h1 : IsMinPeriod F p L1) (h2 : IsMinPeriod F p L2) : L1 = L2 := by
  rcases h1 with ⟨hpos1, heq1, hmin1⟩
  rcases h2 with ⟨hpos2, heq2, hmin2⟩
  by_cases hlt : L1 < L2
  · exact False.elim (hmin2 L1 hpos1 hlt heq1)
  · by_cases hgt : L2 < L1
    · exact False.elim (hmin1 L2 hpos2 hgt heq2)
    · omega

private theorem pow_two_mod_three_ne_zero (s : Nat) : 2 ^ s % 3 = 1 ∨ 2 ^ s % 3 = 2 := by
  induction s with
  | zero => left; decide
  | succ s ih =>
    rw [Nat.pow_succ]
    rcases ih with h | h <;> omega

private theorem gcd_pow_two_three (s : Nat) : Nat.gcd (2 ^ s) 3 = 1 := by
  have hmod := pow_two_mod_three_ne_zero s
  rw [Nat.gcd_comm, Nat.gcd_rec]
  rcases hmod with h | h
  · rw [h]; decide
  · rw [h]; decide

private theorem dvd_pow_two_of_lt {q s : Nat} (hdvd : q ∣ 2 ^ (s + 1)) (hlt : q < 2 ^ (s + 1)) :
    q ∣ 2 ^ s := by
  rcases hdvd with ⟨t, ht⟩
  have hpos : 0 < 2 ^ (s + 1) := by have := @Nat.one_le_two_pow (s + 1); omega
  have ht2 : 2 ≤ t := by
    by_cases ht0 : t = 0
    · rw [ht0, Nat.mul_zero] at ht; omega
    · by_cases ht1 : t = 1
      · rw [ht1, Nat.mul_one] at ht; omega
      · omega
  have ht_even : t % 2 = 0 := by
    have h2 : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [Nat.pow_succ, Nat.mul_comm]
    have hcop : Nat.gcd t 2 = 2 := by
      have hdvd_t : t ∣ 2 ^ (s + 1) := ⟨q, by rw [Nat.mul_comm]; exact ht⟩
      -- If `t` were odd, `gcd t (2^(s+1)) = 1`, contradicting `t ≥ 2` and `t ∣ 2^(s+1)`.
      by_cases hodd : t % 2 = 1
      · exfalso
        have hcop_pow : ∀ k : Nat, Nat.gcd t (2 ^ k) = 1 := by
          intro k
          induction k with
          | zero => simp
          | succ k ihk =>
            rw [Nat.pow_succ, Nat.mul_comm]
            have hcop2 : Nat.Coprime t 2 := by
              unfold Nat.Coprime
              rw [Nat.gcd_comm, Nat.gcd_rec, hodd]; decide
            exact Nat.Coprime.mul_right hcop2 ihk
        have hg := hcop_pow (s + 1)
        rw [Nat.gcd_eq_left hdvd_t] at hg
        omega
      · have hev : t % 2 = 0 := by omega
        rw [Nat.gcd_comm, Nat.gcd_rec, hev]; simp
    have h2t : 2 ∣ t := by
      rw [← hcop]
      exact Nat.gcd_dvd_left t 2
    exact Nat.mod_eq_zero_of_dvd h2t
  refine ⟨t / 2, ?_⟩
  have h2s : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [Nat.pow_succ, Nat.mul_comm]
  have ht_eq : t = 2 * (t / 2) := by omega
  have hmul : 2 * 2 ^ s = 2 * (q * (t / 2)) := by
    calc 2 * 2 ^ s = 2 ^ (s + 1) := h2s.symm
      _ = q * t := ht
      _ = q * (2 * (t / 2)) := congrArg (q * ·) ht_eq
      _ = 2 * (q * (t / 2)) := by rw [Nat.mul_left_comm]
  omega

/-! ### Part 2: Bitwise / power-of-two decomposition helpers & Theorem 1 -/

private theorem xor_mod_two_pow (a b k : Nat) : (a ^^^ b) % 2 ^ k = (a % 2 ^ k) ^^^ (b % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < k <;> simp [hi]

private theorem xor_lt_two_pow {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  have heq : a ^^^ b = (a ^^^ b) % 2 ^ k := by
    apply Nat.eq_of_testBit_eq
    intro u
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
    by_cases hu : u < k
    · simp [hu]
    · have hle : 2 ^ k ≤ 2 ^ u := Nat.pow_le_pow_right (by omega) (by omega)
      have ha' : a.testBit u = false := Nat.testBit_lt_two_pow (by omega)
      have hb' : b.testBit u = false := Nat.testBit_lt_two_pow (by omega)
      simp [hu, ha', hb']
  rw [heq]
  have hpos : 0 < 2 ^ k := by have := @Nat.one_le_two_pow k; omega
  exact Nat.mod_lt _ hpos

private theorem testBit_add_mul_two_pow (r a b u : Nat) (ha : a < 2 ^ r) :
    (a + b * 2 ^ r).testBit u = if u < r then a.testBit u else b.testBit (u - r) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hu : u < r
  · simp only [hu, ↓reduceIte]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hsplit : 2 ^ r = 2 ^ u * 2 ^ (r - u) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
    have hpos_u : 0 < 2 ^ u := by have := @Nat.one_le_two_pow u; omega
    have hdiv : (a + b * 2 ^ r) / 2 ^ u = a / 2 ^ u + b * 2 ^ (r - u) := by
      rw [hsplit, ← Nat.mul_assoc, Nat.mul_right_comm, Nat.add_mul_div_right _ _ hpos_u]
    have heven : 2 ^ (r - u) % 2 = 0 := by
      have hge : 1 ≤ r - u := by omega
      have hrew : r - u = (r - u - 1) + 1 := by omega
      rw [hrew, Nat.pow_succ]
      omega
    rw [hdiv]
    congr 1
    rw [Nat.add_mod, Nat.mul_mod, heven, Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
  · simp only [hu, ↓reduceIte]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hsplit : 2 ^ u = 2 ^ r * 2 ^ (u - r) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
    have hpos_r : 0 < 2 ^ r := by have := @Nat.one_le_two_pow r; omega
    have hdiv1 : (a + b * 2 ^ r) / 2 ^ r = b := by
      rw [Nat.add_mul_div_right _ _ hpos_r, Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [hsplit, ← Nat.div_div_eq_div_mul, hdiv1]

private theorem xor_split_two_pow (r a b d e : Nat) (ha : a < 2 ^ r) (hd : d < 2 ^ r) :
    (a + b * 2 ^ r) ^^^ (d + e * 2 ^ r) = (a ^^^ d) + (b ^^^ e) * 2 ^ r := by
  apply Nat.eq_of_testBit_eq
  intro u
  have had : a ^^^ d < 2 ^ r := xor_lt_two_pow ha hd
  rw [Nat.testBit_xor, testBit_add_mul_two_pow r a b u ha,
      testBit_add_mul_two_pow r d e u hd,
      testBit_add_mul_two_pow r (a ^^^ d) (b ^^^ e) u had]
  by_cases hu : u < r
  · simp [hu, Nat.testBit_xor]
  · simp [hu, Nat.testBit_xor]

private theorem add_mul_mod_four_pow (r lo X : Nat) (hlo : lo < 2 ^ r) :
    (lo + X * 2 ^ r) % 2 ^ (r + 2) = lo + (X % 4) * 2 ^ r := by
  have h4 : 2 ^ (r + 2) = 4 * 2 ^ r := by
    rw [Nat.pow_add, Nat.mul_comm]
  rw [h4]
  have hdecomp : lo + X * 2 ^ r = (lo + (X % 4) * 2 ^ r) + (X / 4) * (4 * 2 ^ r) := by
    have hX : X = X % 4 + 4 * (X / 4) := by omega
    have hmul : (4 * (X / 4)) * 2 ^ r = (X / 4) * (4 * 2 ^ r) := by
      rw [Nat.mul_comm 4 (X / 4), Nat.mul_assoc]
    calc lo + X * 2 ^ r
        = lo + (X % 4 + 4 * (X / 4)) * 2 ^ r := by rw [← hX]
      _ = lo + ((X % 4) * 2 ^ r + (4 * (X / 4)) * 2 ^ r) := by rw [Nat.add_mul]
      _ = (lo + (X % 4) * 2 ^ r) + (X / 4) * (4 * 2 ^ r) := by rw [Nat.add_assoc, hmul]
  rw [hdecomp, Nat.add_mul_mod_self_right]
  have hlt : lo + (X % 4) * 2 ^ r < 4 * 2 ^ r := by
    have hX4 : X % 4 ≤ 3 := by omega
    have hmul : (X % 4) * 2 ^ r ≤ 3 * 2 ^ r := Nat.mul_le_mul_right (2 ^ r) hX4
    omega
  exact Nat.mod_eq_of_lt hlt

private theorem xor_succ_mod4 (q e : Nat) :
    ((q + 1) ^^^ e) % 4 = ((q ^^^ e) + (if e % 2 = 1 then 3 else 1)) % 4 := by
  have h4 : (4 : Nat) = 2 ^ 2 := rfl
  rw [h4, xor_mod_two_pow (q + 1) e 2, Nat.add_mod q 1 (2 ^ 2),
      Nat.add_mod (q ^^^ e) _ (2 ^ 2), xor_mod_two_pow q e 2]
  change (((q % 4 + 1 % 4) % 4) ^^^ (e % 4)) =
    (((q % 4) ^^^ (e % 4)) + (if e % 2 = 1 then 3 else 1) % 4) % 4
  have hq : q % 4 < 4 := Nat.mod_lt q (by omega)
  have he : e % 4 < 4 := Nat.mod_lt e (by omega)
  have he2 : e % 2 = (e % 4) % 2 := by omega
  rw [he2]
  match hq_eq : q % 4, he_eq : e % 4 with
  | 0, 0 => decide
  | 0, 1 => decide
  | 0, 2 => decide
  | 0, 3 => decide
  | 1, 0 => decide
  | 1, 1 => decide
  | 1, 2 => decide
  | 1, 3 => decide
  | 2, 0 => decide
  | 2, 1 => decide
  | 2, 2 => decide
  | 2, 3 => decide
  | 3, 0 => decide
  | 3, 1 => decide
  | 3, 2 => decide
  | 3, 3 => decide
  | _ + 4, _ => omega
  | _, _ + 4 => omega

/-- Theorem 1 (Exact finite-level 2-adic perturbation law for `y ↦ y ^^^ c`):
adding `2^r` to `y` before XORing with `c` shifts `y ^^^ c` modulo `2^(r+2)` by
`σ * 2^r` where `σ = 3` if bit `r` of `c` is `1` and `σ = 1` otherwise. -/
theorem xor_add_pow_two_mod (r y c : Nat) :
    ((y + 2 ^ r) ^^^ c) % 2 ^ (r + 2) =
      ((y ^^^ c) + (if c.testBit r then 3 else 1) * 2 ^ r) % 2 ^ (r + 2) := by
  have hpos : 0 < 2 ^ r := by have := @Nat.one_le_two_pow r; omega
  have hy_lt : y % 2 ^ r < 2 ^ r := Nat.mod_lt y hpos
  have hc_lt : c % 2 ^ r < 2 ^ r := Nat.mod_lt c hpos
  have hy_eq : y = y % 2 ^ r + (y / 2 ^ r) * 2 ^ r := by
    have := Nat.div_add_mod y (2 ^ r)
    rw [Nat.mul_comm] at this
    omega
  have hc_eq : c = c % 2 ^ r + (c / 2 ^ r) * 2 ^ r := by
    have := Nat.div_add_mod c (2 ^ r)
    rw [Nat.mul_comm] at this
    omega
  have hy1 : y + 2 ^ r = y % 2 ^ r + (y / 2 ^ r + 1) * 2 ^ r := by
    calc y + 2 ^ r = (y % 2 ^ r + (y / 2 ^ r) * 2 ^ r) + 2 ^ r := by rw [← hy_eq]
      _ = y % 2 ^ r + ((y / 2 ^ r) * 2 ^ r + 1 * 2 ^ r) := by rw [Nat.add_assoc, Nat.one_mul]
      _ = y % 2 ^ r + (y / 2 ^ r + 1) * 2 ^ r := by rw [← Nat.add_mul]
  have hbit : c.testBit r = decide ((c / 2 ^ r) % 2 = 1) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
  have hlhs_xor : (y + 2 ^ r) ^^^ c =
      (y % 2 ^ r ^^^ c % 2 ^ r) + ((y / 2 ^ r + 1) ^^^ (c / 2 ^ r)) * 2 ^ r := by
    conv => lhs; rw [hy1, hc_eq]
    exact xor_split_two_pow r (y % 2 ^ r) (y / 2 ^ r + 1) (c % 2 ^ r) (c / 2 ^ r) hy_lt hc_lt
  have hrhs_xor : y ^^^ c =
      (y % 2 ^ r ^^^ c % 2 ^ r) + ((y / 2 ^ r) ^^^ (c / 2 ^ r)) * 2 ^ r := by
    conv => lhs; rw [hy_eq, hc_eq]
    exact xor_split_two_pow r (y % 2 ^ r) (y / 2 ^ r) (c % 2 ^ r) (c / 2 ^ r) hy_lt hc_lt
  have hlo_lt : y % 2 ^ r ^^^ c % 2 ^ r < 2 ^ r := xor_lt_two_pow hy_lt hc_lt
  let σ : Nat := if c.testBit r then 3 else 1
  have hrhs_add : (y ^^^ c) + σ * 2 ^ r =
      (y % 2 ^ r ^^^ c % 2 ^ r) + (((y / 2 ^ r) ^^^ (c / 2 ^ r)) + σ) * 2 ^ r := by
    rw [hrhs_xor, Nat.add_assoc, ← Nat.add_mul]
  change ((y + 2 ^ r) ^^^ c) % 2 ^ (r + 2) = ((y ^^^ c) + σ * 2 ^ r) % 2 ^ (r + 2)
  rw [hlhs_xor, hrhs_add,
      add_mul_mod_four_pow r _ _ hlo_lt,
      add_mul_mod_four_pow r _ _ hlo_lt]
  congr 2
  have hσ_eq : σ = if (c / 2 ^ r) % 2 = 1 then 3 else 1 := by
    change (if c.testBit r then 3 else 1) = _
    rw [hbit]
    by_cases h1 : (c / 2 ^ r) % 2 = 1 <;> simp [h1]
  rw [hσ_eq]
  exact xor_succ_mod4 (y / 2 ^ r) (c / 2 ^ r)

private theorem xor_add_mul_pow_two_mod (r y c b : Nat) :
    ((y + b * 2 ^ r) ^^^ c) % 2 ^ (r + 2) =
      ((y ^^^ c) + (if c.testBit r then 3 else 1) * b * 2 ^ r) % 2 ^ (r + 2) := by
  let σ : Nat := if c.testBit r then 3 else 1
  change ((y + b * 2 ^ r) ^^^ c) % 2 ^ (r + 2) = ((y ^^^ c) + σ * b * 2 ^ r) % 2 ^ (r + 2)
  induction b with
  | zero => simp
  | succ b ih =>
    have hstep : y + (b + 1) * 2 ^ r = (y + b * 2 ^ r) + 2 ^ r := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [hstep, xor_add_pow_two_mod r (y + b * 2 ^ r) c]
    change (((y + b * 2 ^ r) ^^^ c) + σ * 2 ^ r) % 2 ^ (r + 2) =
      ((y ^^^ c) + σ * (b + 1) * 2 ^ r) % 2 ^ (r + 2)
    rw [Nat.add_mod, ih, ← Nat.add_mod]
    congr 1
    rw [Nat.mul_succ, Nat.add_mul, Nat.add_assoc]

/-! ### Part 3: Causality of `arxFibRaw` / `arxFibStep` and Theorem 2 -/

private theorem arxFibRaw_mod_input (c k x1 y1 x2 y2 : Nat)
    (hx : x1 % 2 ^ k = x2 % 2 ^ k) (hy : y1 % 2 ^ k = y2 % 2 ^ k) :
    (arxFibRaw c (x1, y1)).1 % 2 ^ k = (arxFibRaw c (x2, y2)).1 % 2 ^ k ∧
    (arxFibRaw c (x1, y1)).2 % 2 ^ k = (arxFibRaw c (x2, y2)).2 % 2 ^ k := by
  simp only [arxFibRaw]
  refine ⟨hy, ?_⟩
  rw [Nat.add_mod x1, Nat.add_mod x2, hx, xor_mod_two_pow y1 c k, xor_mod_two_pow y2 c k, hy]

private theorem arxFibRaw_iter_mod_input (c k n x1 y1 x2 y2 : Nat)
    (hx : x1 % 2 ^ k = x2 % 2 ^ k) (hy : y1 % 2 ^ k = y2 % 2 ^ k) :
    (iter (arxFibRaw c) n (x1, y1)).1 % 2 ^ k = (iter (arxFibRaw c) n (x2, y2)).1 % 2 ^ k ∧
    (iter (arxFibRaw c) n (x1, y1)).2 % 2 ^ k = (iter (arxFibRaw c) n (x2, y2)).2 % 2 ^ k := by
  induction n generalizing x1 y1 x2 y2 with
  | zero => exact ⟨hx, hy⟩
  | succ n ih =>
    simp only [iter]
    have h1 := arxFibRaw_mod_input c k x1 y1 x2 y2 hx hy
    exact ih (arxFibRaw c (x1, y1)).1 (arxFibRaw c (x1, y1)).2
      (arxFibRaw c (x2, y2)).1 (arxFibRaw c (x2, y2)).2 h1.1 h1.2

private theorem arxFibStep_iter_eq_mod (c m n x y : Nat) (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    iter (arxFibStep c m) n (x, y) =
      ((iter (arxFibRaw c) n (x, y)).1 % 2 ^ m, (iter (arxFibRaw c) n (x, y)).2 % 2 ^ m) := by
  induction n generalizing x y with
  | zero =>
    simp only [iter, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  | succ n ih =>
    simp only [iter]
    have hpos : 0 < 2 ^ m := by have := @Nat.one_le_two_pow m; omega
    have hstep : arxFibStep c m (x, y) =
        ((arxFibRaw c (x, y)).1 % 2 ^ m, (arxFibRaw c (x, y)).2 % 2 ^ m) := rfl
    rw [hstep, ih _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)]
    have hmod := arxFibRaw_iter_mod_input c m n
      ((arxFibRaw c (x, y)).1 % 2 ^ m) ((arxFibRaw c (x, y)).2 % 2 ^ m)
      (arxFibRaw c (x, y)).1 (arxFibRaw c (x, y)).2
      (Nat.mod_mod _ _) (Nat.mod_mod _ _)
    exact Prod.ext hmod.1 hmod.2

private theorem arxFibRaw_fixed_cc (c n : Nat) : iter (arxFibRaw c) n (c, c) = (c, c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iter, arxFibRaw, Nat.xor_self, Nat.add_zero]
    exact ih

/-- Theorem 2 (Unique fixed point of `arxFibStep c m` on `{0, ..., 2^m - 1}^2`):
for `m ≥ 1`, `(c % 2^m, c % 2^m)` is the unique fixed point of `G_{c,m}`. -/
theorem arxFibStep_fixed_point_iff (c m x y : Nat) (_hm : 1 ≤ m)
    (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    arxFibStep c m (x, y) = (x, y) ↔ x = c % 2 ^ m ∧ y = c % 2 ^ m := by
  constructor
  · intro hfix
    have h1 : y % 2 ^ m = x := congrArg Prod.fst hfix
    have h2 : (x + (y ^^^ c)) % 2 ^ m = y := congrArg Prod.snd hfix
    rw [Nat.mod_eq_of_lt hy] at h1
    subst h1
    have hxor_mod : (y ^^^ c) % 2 ^ m = 0 := by
      have hsub : (y + (y ^^^ c) % 2 ^ m) % 2 ^ m = y := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        exact h2
      have hlt_m : (y ^^^ c) % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by have := @Nat.one_le_two_pow m; omega)
      by_cases hsum : y + (y ^^^ c) % 2 ^ m < 2 ^ m
      · rw [Nat.mod_eq_of_lt hsum] at hsub; omega
      · have hlt2 : y + (y ^^^ c) % 2 ^ m - 2 ^ m < 2 ^ m := by omega
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at hsub
        omega
    rw [xor_mod_two_pow y c m, Nat.mod_eq_of_lt hy] at hxor_mod
    have hyc : y = c % 2 ^ m := by
      have h := congrArg (fun z => z ^^^ (c % 2 ^ m)) hxor_mod
      simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using h
    exact ⟨hyc, hyc⟩
  · rintro ⟨rfl, rfl⟩
    have hxor0 : ((c % 2 ^ m) ^^^ c) % 2 ^ m = 0 := by
      rw [xor_mod_two_pow, Nat.mod_mod, Nat.xor_self]
    simp only [arxFibStep]
    refine Prod.ext (Nat.mod_mod c (2 ^ m)) ?_
    rw [Nat.add_mod, hxor0, Nat.add_zero, Nat.mod_mod, Nat.mod_mod]

/-! ### Part 4: Linearized 2-adic Jacobian & exact 2-adic lifting -/

/-- Linearized Jacobian map `J_σ(a, b) = (b, a + σ * b)` for `σ ∈ {1, 3}`. -/
def jacStep (σ : Nat) (v : Nat × Nat) : Nat × Nat :=
  (v.2, v.1 + σ * v.2)

private theorem arxFibRaw_iter_perturb (c r n x y a b : Nat) :
    let σ := if c.testBit r then 3 else 1
    (iter (arxFibRaw c) n (x + a * 2 ^ r, y + b * 2 ^ r)).1 % 2 ^ (r + 2) =
      ((iter (arxFibRaw c) n (x, y)).1 + (iter (jacStep σ) n (a, b)).1 * 2 ^ r) % 2 ^ (r + 2) ∧
    (iter (arxFibRaw c) n (x + a * 2 ^ r, y + b * 2 ^ r)).2 % 2 ^ (r + 2) =
      ((iter (arxFibRaw c) n (x, y)).2 + (iter (jacStep σ) n (a, b)).2 * 2 ^ r) % 2 ^ (r + 2) := by
  intro σ
  induction n generalizing x y a b with
  | zero => simp [iter]
  | succ n ih =>
    simp only [iter]
    have h2 : (x + a * 2 ^ r + ((y + b * 2 ^ r) ^^^ c)) % 2 ^ (r + 2) =
        ((x + (y ^^^ c)) + (a + σ * b) * 2 ^ r) % 2 ^ (r + 2) := by
      rw [Nat.add_mod (x + a * 2 ^ r), xor_add_mul_pow_two_mod r y c b]
      change (((x + a * 2 ^ r) % 2 ^ (r + 2) +
        ((y ^^^ c) + σ * b * 2 ^ r) % 2 ^ (r + 2)) % 2 ^ (r + 2)) = _
      rw [← Nat.add_mod]
      congr 1
      rw [Nat.add_mul]
      omega
    have hstep_mod := arxFibRaw_iter_mod_input c (r + 2) n
      (y + b * 2 ^ r) (x + a * 2 ^ r + ((y + b * 2 ^ r) ^^^ c))
      (y + b * 2 ^ r) ((x + (y ^^^ c)) + (a + σ * b) * 2 ^ r)
      rfl h2
    have hih := ih y (x + (y ^^^ c)) b (a + σ * b)
    exact ⟨hstep_mod.1.trans hih.1, hstep_mod.2.trans hih.2⟩

private theorem exists_mod4_shift (r u v : Nat) (hmod : u % 2 ^ r = v % 2 ^ r) :
    ∃ a : Nat, a < 4 ∧ u % 2 ^ (r + 2) = (v + a * 2 ^ r) % 2 ^ (r + 2) ∧
      (u % 2 ^ (r + 1) = v % 2 ^ (r + 1) ↔ a % 2 = 0) := by
  have hpos : 0 < 2 ^ r := by have := @Nat.one_le_two_pow r; omega
  have hu_lt : u % 2 ^ r < 2 ^ r := Nat.mod_lt u hpos
  have hv_lt : v % 2 ^ r < 2 ^ r := Nat.mod_lt v hpos
  have hu_eq : u = u % 2 ^ r + (u / 2 ^ r) * 2 ^ r := by
    have := Nat.div_add_mod u (2 ^ r); rw [Nat.mul_comm] at this; omega
  have hv_eq : v = v % 2 ^ r + (v / 2 ^ r) * 2 ^ r := by
    have := Nat.div_add_mod v (2 ^ r); rw [Nat.mul_comm] at this; omega
  let qu := (u / 2 ^ r) % 4
  let qv := (v / 2 ^ r) % 4
  let a := (4 + qu - qv) % 4
  refine ⟨a, Nat.mod_lt _ (by omega), ?_, ?_⟩
  · have hu4 : u % 2 ^ (r + 2) = u % 2 ^ r + qu * 2 ^ r := by
      conv => lhs; rw [hu_eq]
      exact add_mul_mod_four_pow r (u % 2 ^ r) (u / 2 ^ r) hu_lt
    have hva : v + a * 2 ^ r = v % 2 ^ r + (v / 2 ^ r + a) * 2 ^ r := by
      calc v + a * 2 ^ r = (v % 2 ^ r + (v / 2 ^ r) * 2 ^ r) + a * 2 ^ r := by rw [← hv_eq]
        _ = v % 2 ^ r + (v / 2 ^ r + a) * 2 ^ r := by rw [Nat.add_assoc, ← Nat.add_mul]
    have hv4 : (v + a * 2 ^ r) % 2 ^ (r + 2) = v % 2 ^ r + ((v / 2 ^ r + a) % 4) * 2 ^ r := by
      rw [hva]
      exact add_mul_mod_four_pow r (v % 2 ^ r) (v / 2 ^ r + a) hv_lt
    have hq_eq : (v / 2 ^ r + a) % 4 = qu := by
      change (v / 2 ^ r + (4 + (u / 2 ^ r) % 4 - (v / 2 ^ r) % 4) % 4) % 4 = (u / 2 ^ r) % 4
      omega
    rw [hu4, hv4, hmod, hq_eq]
  · have h2 : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ, Nat.mul_comm]
    have hmod2 : ∀ w : Nat, w % (2 * 2 ^ r) = w % 2 ^ r + ((w / 2 ^ r) % 2) * 2 ^ r := by
      intro w
      have hw_lt : w % 2 ^ r < 2 ^ r := Nat.mod_lt w hpos
      have hw_eq : w = (w % 2 ^ r + ((w / 2 ^ r) % 2) * 2 ^ r) + (w / 2 ^ r / 2) * (2 * 2 ^ r) := by
        have h1 : w = w % 2 ^ r + (w / 2 ^ r) * 2 ^ r := by
          have := Nat.div_add_mod w (2 ^ r); rw [Nat.mul_comm] at this; omega
        have h2' : w / 2 ^ r = (w / 2 ^ r) % 2 + 2 * (w / 2 ^ r / 2) := by omega
        have hmul : (2 * (w / 2 ^ r / 2)) * 2 ^ r = (w / 2 ^ r / 2) * (2 * 2 ^ r) := by
          rw [Nat.mul_comm 2, Nat.mul_assoc]
        calc w = w % 2 ^ r + ((w / 2 ^ r) % 2 + 2 * (w / 2 ^ r / 2)) * 2 ^ r := by
                conv => lhs; rw [h1, h2']
          _ = w % 2 ^ r + (((w / 2 ^ r) % 2) * 2 ^ r + (2 * (w / 2 ^ r / 2)) * 2 ^ r) := by
                rw [Nat.add_mul]
          _ = (w % 2 ^ r + ((w / 2 ^ r) % 2) * 2 ^ r) + (w / 2 ^ r / 2) * (2 * 2 ^ r) := by
                rw [Nat.add_assoc, hmul]
      conv => lhs; rw [hw_eq, Nat.add_mul_mod_self_right]
      have hlt : w % 2 ^ r + ((w / 2 ^ r) % 2) * 2 ^ r < 2 * 2 ^ r := by
        have hle : ((w / 2 ^ r) % 2) * 2 ^ r ≤ 1 * 2 ^ r := Nat.mul_le_mul_right (2 ^ r) (by omega)
        omega
      exact Nat.mod_eq_of_lt hlt
    rw [h2, hmod2 u, hmod2 v, hmod]
    constructor
    · intro heq
      have hmul : ((u / 2 ^ r) % 2) * 2 ^ r = ((v / 2 ^ r) % 2) * 2 ^ r := by omega
      have hpar : (u / 2 ^ r) % 2 = (v / 2 ^ r) % 2 := Nat.eq_of_mul_eq_mul_right hpos hmul
      change ((4 + (u / 2 ^ r) % 4 - (v / 2 ^ r) % 4) % 4) % 2 = 0
      omega
    · intro ha0
      have ha0' : ((4 + (u / 2 ^ r) % 4 - (v / 2 ^ r) % 4) % 4) % 2 = 0 := ha0
      have hpar : (u / 2 ^ r) % 2 = (v / 2 ^ r) % 2 := by omega
      rw [hpar]

private theorem mod_pow_two_of_mod_pow_two_succ {a b k : Nat}
    (h : a % 2 ^ (k + 1) = b % 2 ^ (k + 1)) : a % 2 ^ k = b % 2 ^ k := by
  have hdvd : 2 ^ k ∣ 2 ^ (k + 1) := ⟨2, by rw [Nat.pow_succ]⟩
  calc a % 2 ^ k = (a % 2 ^ (k + 1)) % 2 ^ k := (Nat.mod_mod_of_dvd a hdvd).symm
    _ = (b % 2 ^ (k + 1)) % 2 ^ k := by rw [h]
    _ = b % 2 ^ k := Nat.mod_mod_of_dvd b hdvd

private theorem add_mul_pow_two_mod4_iff (r v u1 u2 : Nat) :
    (v + u1 * 2 ^ r) % 2 ^ (r + 2) = (v + u2 * 2 ^ r) % 2 ^ (r + 2) ↔ u1 % 4 = u2 % 4 := by
  have hpos : 0 < 2 ^ r := by have := @Nat.one_le_two_pow r; omega
  have hv_lt : v % 2 ^ r < 2 ^ r := Nat.mod_lt v hpos
  have hv_eq : v = v % 2 ^ r + (v / 2 ^ r) * 2 ^ r := by
    have := Nat.div_add_mod v (2 ^ r); rw [Nat.mul_comm] at this; omega
  have hrew : ∀ u : Nat, (v + u * 2 ^ r) % 2 ^ (r + 2) =
      v % 2 ^ r + ((v / 2 ^ r + u) % 4) * 2 ^ r := by
    intro u
    have h1 : v + u * 2 ^ r = v % 2 ^ r + (v / 2 ^ r + u) * 2 ^ r := by
      calc v + u * 2 ^ r = (v % 2 ^ r + (v / 2 ^ r) * 2 ^ r) + u * 2 ^ r := by rw [← hv_eq]
        _ = v % 2 ^ r + (v / 2 ^ r + u) * 2 ^ r := by rw [Nat.add_assoc, ← Nat.add_mul]
    rw [h1]
    exact add_mul_mod_four_pow r (v % 2 ^ r) (v / 2 ^ r + u) hv_lt
  rw [hrew u1, hrew u2]
  constructor
  · intro heq
    have hmul : ((v / 2 ^ r + u1) % 4) * 2 ^ r = ((v / 2 ^ r + u2) % 4) * 2 ^ r := by omega
    have hm := Nat.eq_of_mul_eq_mul_right hpos hmul
    omega
  · intro hu
    have hm : (v / 2 ^ r + u1) % 4 = (v / 2 ^ r + u2) % 4 := by omega
    rw [hm]

private theorem add_mul_pow_two_mod2_iff (r v u1 u2 : Nat) :
    (v + u1 * 2 ^ r) % 2 ^ (r + 1) = (v + u2 * 2 ^ r) % 2 ^ (r + 1) ↔ u1 % 2 = u2 % 2 := by
  have hpos : 0 < 2 ^ r := by have := @Nat.one_le_two_pow r; omega
  have hv_lt : v % 2 ^ r < 2 ^ r := Nat.mod_lt v hpos
  have h2 : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ, Nat.mul_comm]
  have hrew : ∀ u : Nat, (v + u * 2 ^ r) % (2 * 2 ^ r) =
      v % 2 ^ r + ((v / 2 ^ r + u) % 2) * 2 ^ r := by
    intro u
    have hv_eq : v = v % 2 ^ r + (v / 2 ^ r) * 2 ^ r := by
      have := Nat.div_add_mod v (2 ^ r); rw [Nat.mul_comm] at this; omega
    have h1 : v + u * 2 ^ r =
        (v % 2 ^ r + ((v / 2 ^ r + u) % 2) * 2 ^ r) + ((v / 2 ^ r + u) / 2) * (2 * 2 ^ r) := by
      have hq : v / 2 ^ r + u = (v / 2 ^ r + u) % 2 + 2 * ((v / 2 ^ r + u) / 2) := by omega
      have hmul : (2 * ((v / 2 ^ r + u) / 2)) * 2 ^ r = ((v / 2 ^ r + u) / 2) * (2 * 2 ^ r) := by
        rw [Nat.mul_comm 2, Nat.mul_assoc]
      calc v + u * 2 ^ r = (v % 2 ^ r + (v / 2 ^ r) * 2 ^ r) + u * 2 ^ r := by rw [← hv_eq]
        _ = v % 2 ^ r + (v / 2 ^ r + u) * 2 ^ r := by rw [Nat.add_assoc, ← Nat.add_mul]
        _ = v % 2 ^ r + ((v / 2 ^ r + u) % 2 + 2 * ((v / 2 ^ r + u) / 2)) * 2 ^ r := by rw [← hq]
        _ = (v % 2 ^ r + ((v / 2 ^ r + u) % 2) * 2 ^ r) + ((v / 2 ^ r + u) / 2) * (2 * 2 ^ r) := by
              rw [Nat.add_mul, Nat.add_assoc, hmul]
    rw [h1, Nat.add_mul_mod_self_right]
    have hlt : v % 2 ^ r + ((v / 2 ^ r + u) % 2) * 2 ^ r < 2 * 2 ^ r := by
      have hle : ((v / 2 ^ r + u) % 2) * 2 ^ r ≤ 1 * 2 ^ r := Nat.mul_le_mul_right (2 ^ r) (by omega)
      omega
    exact Nat.mod_eq_of_lt hlt
  rw [h2, hrew u1, hrew u2]
  constructor
  · intro heq
    have hmul : ((v / 2 ^ r + u1) % 2) * 2 ^ r = ((v / 2 ^ r + u2) % 2) * 2 ^ r := by omega
    have hm := Nat.eq_of_mul_eq_mul_right hpos hmul
    omega
  · intro hu
    have hm : (v / 2 ^ r + u1) % 2 = (v / 2 ^ r + u2) % 2 := by omega
    rw [hm]

private theorem jacStep_iter_mod4 (σ n a1 b1 a2 b2 : Nat)
    (ha : a1 % 4 = a2 % 4) (hb : b1 % 4 = b2 % 4) :
    (iter (jacStep σ) n (a1, b1)).1 % 4 = (iter (jacStep σ) n (a2, b2)).1 % 4 ∧
    (iter (jacStep σ) n (a1, b1)).2 % 4 = (iter (jacStep σ) n (a2, b2)).2 % 4 := by
  induction n generalizing a1 b1 a2 b2 with
  | zero => exact ⟨ha, hb⟩
  | succ n ih =>
    simp only [iter, jacStep]
    have h2 : (a1 + σ * b1) % 4 = (a2 + σ * b2) % 4 := by
      rw [Nat.add_mod a1, Nat.add_mod a2, ha, Nat.mul_mod σ b1, Nat.mul_mod σ b2, hb]
    exact ih b1 (a1 + σ * b1) b2 (a2 + σ * b2) hb h2

private theorem jacStep_iter_six_mod4 (σ a b : Nat) (hσ : σ = 1 ∨ σ = 3) :
    (iter (jacStep σ) 6 (a, b)).1 % 4 = a % 4 ∧
    (iter (jacStep σ) 6 (a, b)).2 % 4 = b % 4 := by
  rcases hσ with rfl | rfl
  · simp only [iter, jacStep]; constructor <;> omega
  · simp only [iter, jacStep]; constructor <;> omega

private theorem jacStep_iter_six_mul_mod4 (σ q a b : Nat) (hσ : σ = 1 ∨ σ = 3) :
    (iter (jacStep σ) (6 * q) (a, b)).1 % 4 = a % 4 ∧
    (iter (jacStep σ) (6 * q) (a, b)).2 % 4 = b % 4 := by
  induction q with
  | zero => simp [iter]
  | succ q ih =>
    rw [Nat.mul_succ, iter_add]
    have h6 := jacStep_iter_six_mod4 σ (iter (jacStep σ) (6 * q) (a, b)).1
      (iter (jacStep σ) (6 * q) (a, b)).2 hσ
    exact ⟨h6.1.trans ih.1, h6.2.trans ih.2⟩

/-- Step 1 of `arxFibRaw c` never fixes `(x, y)` modulo `2^(r0+1)` when `(x, y)` first differs
from `(c, c)` at bit `r0`. -/
private theorem arxFibRaw_step1_ne_mod (c x y r0 : Nat)
    (hmatch : x % 2 ^ r0 = c % 2 ^ r0 ∧ y % 2 ^ r0 = c % 2 ^ r0)
    (hdiff : ¬(x % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1) ∧ y % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1))) :
    ¬((iter (arxFibRaw c) 1 (x, y)).1 % 2 ^ (r0 + 1) = x % 2 ^ (r0 + 1) ∧
      (iter (arxFibRaw c) 1 (x, y)).2 % 2 ^ (r0 + 1) = y % 2 ^ (r0 + 1)) := by
  rcases exists_mod4_shift r0 x c hmatch.1 with ⟨a, _, hxa, ha_iff⟩
  rcases exists_mod4_shift r0 y c hmatch.2 with ⟨b, _, hyb, hb_iff⟩
  have hab_odd : a % 2 = 1 ∨ b % 2 = 1 := by
    by_cases ha0 : a % 2 = 0
    · by_cases hb0 : b % 2 = 0
      · exact False.elim (hdiff ⟨ha_iff.mpr ha0, hb_iff.mpr hb0⟩)
      · right; omega
    · left; omega
  let σ : Nat := if c.testBit r0 then 3 else 1
  have hσ_odd : σ % 2 = 1 := by
    change (if c.testBit r0 then 3 else 1) % 2 = 1
    cases c.testBit r0 <;> decide
  have h1_mod4 := arxFibRaw_iter_mod_input c (r0 + 2) 1 x y (c + a * 2 ^ r0) (c + b * 2 ^ r0) hxa hyb
  have hpert := arxFibRaw_iter_perturb c r0 1 c c a b
  rw [arxFibRaw_fixed_cc] at hpert
  have h1x : (iter (arxFibRaw c) 1 (x, y)).1 % 2 ^ (r0 + 1) = (c + b * 2 ^ r0) % 2 ^ (r0 + 1) :=
    mod_pow_two_of_mod_pow_two_succ (h1_mod4.1.trans hpert.1)
  have h1y : (iter (arxFibRaw c) 1 (x, y)).2 % 2 ^ (r0 + 1) =
      (c + (a + σ * b) * 2 ^ r0) % 2 ^ (r0 + 1) :=
    mod_pow_two_of_mod_pow_two_succ (h1_mod4.2.trans hpert.2)
  have hx1 : x % 2 ^ (r0 + 1) = (c + a * 2 ^ r0) % 2 ^ (r0 + 1) :=
    mod_pow_two_of_mod_pow_two_succ hxa
  have hy1 : y % 2 ^ (r0 + 1) = (c + b * 2 ^ r0) % 2 ^ (r0 + 1) :=
    mod_pow_two_of_mod_pow_two_succ hyb
  intro hfix
  rw [h1x, hx1, add_mul_pow_two_mod2_iff] at hfix
  rw [h1y, hy1, add_mul_pow_two_mod2_iff] at hfix
  have hmul_odd : (σ * b) % 2 = b % 2 := by
    rw [Nat.mul_mod, hσ_odd, Nat.one_mul, Nat.mod_mod]
  omega

/-- Exact 2-adic lifting theorem for `arxFibRaw c`:
if `(x, y)` agrees with `(c, c)` modulo `2^r0` and differs modulo `2^(r0+1)`, then for every
`k : Nat`, `G_c^{3 * 2^k}(x, y)` agrees with `(x, y)` modulo `2^(r0 + k + 1)` and strictly differs
modulo `2^(r0 + k + 2)`. -/
private theorem arxFibRaw_lift (c x y r0 k : Nat)
    (hmatch : x % 2 ^ r0 = c % 2 ^ r0 ∧ y % 2 ^ r0 = c % 2 ^ r0)
    (hdiff : ¬(x % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1) ∧ y % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1))) :
    ((iter (arxFibRaw c) (3 * 2 ^ k) (x, y)).1 % 2 ^ (r0 + k + 1) = x % 2 ^ (r0 + k + 1) ∧
     (iter (arxFibRaw c) (3 * 2 ^ k) (x, y)).2 % 2 ^ (r0 + k + 1) = y % 2 ^ (r0 + k + 1)) ∧
    ¬((iter (arxFibRaw c) (3 * 2 ^ k) (x, y)).1 % 2 ^ (r0 + k + 2) = x % 2 ^ (r0 + k + 2) ∧
      (iter (arxFibRaw c) (3 * 2 ^ k) (x, y)).2 % 2 ^ (r0 + k + 2) = y % 2 ^ (r0 + k + 2)) := by
  induction k with
  | zero =>
    simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
    rcases exists_mod4_shift r0 x c hmatch.1 with ⟨a, _, hxa, ha_iff⟩
    rcases exists_mod4_shift r0 y c hmatch.2 with ⟨b, _, hyb, hb_iff⟩
    have hab_odd : a % 2 = 1 ∨ b % 2 = 1 := by
      by_cases ha0 : a % 2 = 0
      · by_cases hb0 : b % 2 = 0
        · exact False.elim (hdiff ⟨ha_iff.mpr ha0, hb_iff.mpr hb0⟩)
        · right; omega
      · left; omega
    let σ : Nat := if c.testBit r0 then 3 else 1
    have hσ_cases : σ = 1 ∨ σ = 3 := by
      change (if c.testBit r0 then 3 else 1) = 1 ∨ (if c.testBit r0 then 3 else 1) = 3
      cases c.testBit r0
      · left; rfl
      · right; rfl
    have h3_mod4 := arxFibRaw_iter_mod_input c (r0 + 2) 3 x y (c + a * 2 ^ r0) (c + b * 2 ^ r0) hxa hyb
    have hpert := arxFibRaw_iter_perturb c r0 3 c c a b
    rw [arxFibRaw_fixed_cc] at hpert
    have h3x : (iter (arxFibRaw c) 3 (x, y)).1 % 2 ^ (r0 + 2) =
        (c + (iter (jacStep σ) 3 (a, b)).1 * 2 ^ r0) % 2 ^ (r0 + 2) :=
      h3_mod4.1.trans hpert.1
    have h3y : (iter (arxFibRaw c) 3 (x, y)).2 % 2 ^ (r0 + 2) =
        (c + (iter (jacStep σ) 3 (a, b)).2 * 2 ^ r0) % 2 ^ (r0 + 2) :=
      h3_mod4.2.trans hpert.2
    have hJ3_mod2 : (iter (jacStep σ) 3 (a, b)).1 % 2 = a % 2 ∧
        (iter (jacStep σ) 3 (a, b)).2 % 2 = b % 2 := by
      rcases hσ_cases with hσ1 | hσ3
      · rw [hσ1]; simp only [iter, jacStep]; constructor <;> omega
      · rw [hσ3]; simp only [iter, jacStep]; constructor <;> omega
    have hJ3_ne4 : ¬((iter (jacStep σ) 3 (a, b)).1 % 4 = a % 4 ∧
        (iter (jacStep σ) 3 (a, b)).2 % 4 = b % 4) := by
      rcases hσ_cases with hσ1 | hσ3
      · rw [hσ1]; simp only [iter, jacStep]; intro ⟨h1, h2⟩; omega
      · rw [hσ3]; simp only [iter, jacStep]; intro ⟨h1, h2⟩; omega
    constructor
    · constructor
      · rw [mod_pow_two_of_mod_pow_two_succ h3x, mod_pow_two_of_mod_pow_two_succ hxa,
            add_mul_pow_two_mod2_iff]
        exact hJ3_mod2.1
      · rw [mod_pow_two_of_mod_pow_two_succ h3y, mod_pow_two_of_mod_pow_two_succ hyb,
            add_mul_pow_two_mod2_iff]
        exact hJ3_mod2.2
    · intro ⟨hx4, hy4⟩
      rw [h3x, hxa, add_mul_pow_two_mod4_iff] at hx4
      rw [h3y, hyb, add_mul_pow_two_mod4_iff] at hy4
      exact hJ3_ne4 ⟨hx4, hy4⟩
  | succ k ih =>
    let r := r0 + k + 1
    let L := 3 * 2 ^ k
    have h2L : 3 * 2 ^ (k + 1) = L + L := by
      change 3 * 2 ^ (k + 1) = 3 * 2 ^ k + 3 * 2 ^ k
      rw [Nat.pow_succ]; omega
    have hr1 : r0 + (k + 1) + 1 = r + 1 := by omega
    have hr2 : r0 + (k + 1) + 2 = r + 2 := by omega
    rw [h2L, hr1, hr2, iter_add]
    let p' := iter (arxFibRaw c) L (x, y)
    have hp'_match : p'.1 % 2 ^ r = x % 2 ^ r ∧ p'.2 % 2 ^ r = y % 2 ^ r := ih.1
    have hp'_diff : ¬(p'.1 % 2 ^ (r + 1) = x % 2 ^ (r + 1) ∧
        p'.2 % 2 ^ (r + 1) = y % 2 ^ (r + 1)) := ih.2
    rcases exists_mod4_shift r p'.1 x hp'_match.1 with ⟨a, _, hxa, ha_iff⟩
    rcases exists_mod4_shift r p'.2 y hp'_match.2 with ⟨b, _, hyb, hb_iff⟩
    have hab_odd : a % 2 = 1 ∨ b % 2 = 1 := by
      by_cases ha0 : a % 2 = 0
      · by_cases hb0 : b % 2 = 0
        · exact False.elim (hp'_diff ⟨ha_iff.mpr ha0, hb_iff.mpr hb0⟩)
        · right; omega
      · left; omega
    let σ : Nat := if c.testBit r then 3 else 1
    have hσ_cases : σ = 1 ∨ σ = 3 := by
      change (if c.testBit r then 3 else 1) = 1 ∨ (if c.testBit r then 3 else 1) = 3
      cases c.testBit r
      · left; rfl
      · right; rfl
    have hL_mod4 := arxFibRaw_iter_mod_input c (r + 2) L p'.1 p'.2 (x + a * 2 ^ r) (y + b * 2 ^ r) hxa hyb
    have hpert := arxFibRaw_iter_perturb c r L x y a b
    have hp_eta : p' = (p'.1, p'.2) := rfl
    have h2Lx : (iter (arxFibRaw c) L p').1 % 2 ^ (r + 2) =
        (x + (a + (iter (jacStep σ) L (a, b)).1) * 2 ^ r) % 2 ^ (r + 2) := by
      rw [hp_eta, hL_mod4.1, hpert.1]
      change (p'.1 + (iter (jacStep σ) L (a, b)).1 * 2 ^ r) % 2 ^ (r + 2) = _
      rw [Nat.add_mod p'.1, hxa, ← Nat.add_mod]
      congr 1
      rw [Nat.add_mul, Nat.add_assoc]
    have h2Ly : (iter (arxFibRaw c) L p').2 % 2 ^ (r + 2) =
        (y + (b + (iter (jacStep σ) L (a, b)).2) * 2 ^ r) % 2 ^ (r + 2) := by
      rw [hp_eta, hL_mod4.2, hpert.2]
      change (p'.2 + (iter (jacStep σ) L (a, b)).2 * 2 ^ r) % 2 ^ (r + 2) = _
      rw [Nat.add_mod p'.2, hyb, ← Nat.add_mod]
      congr 1
      rw [Nat.add_mul, Nat.add_assoc]
    have hsum_props :
        ((a + (iter (jacStep σ) L (a, b)).1) % 2 = 0 ∧
         (b + (iter (jacStep σ) L (a, b)).2) % 2 = 0) ∧
        ¬((a + (iter (jacStep σ) L (a, b)).1) % 4 = 0 ∧
          (b + (iter (jacStep σ) L (a, b)).2) % 4 = 0) := by
      cases k with
      | zero =>
        change ((a + (iter (jacStep σ) 3 (a, b)).1) % 2 = 0 ∧
                (b + (iter (jacStep σ) 3 (a, b)).2) % 2 = 0) ∧
               ¬((a + (iter (jacStep σ) 3 (a, b)).1) % 4 = 0 ∧
                 (b + (iter (jacStep σ) 3 (a, b)).2) % 4 = 0)
        rcases hσ_cases with hσ1 | hσ3
        · rw [hσ1]; simp only [iter, jacStep]; exact ⟨⟨by omega, by omega⟩, by omega⟩
        · rw [hσ3]; simp only [iter, jacStep]; exact ⟨⟨by omega, by omega⟩, by omega⟩
      | succ k' =>
        have hL6 : L = 6 * 2 ^ k' := by
          change 3 * 2 ^ (k' + 1) = 6 * 2 ^ k'
          rw [Nat.pow_succ]; omega
        rw [hL6]
        have h6 := jacStep_iter_six_mul_mod4 σ (2 ^ k') a b hσ_cases
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        intro ⟨h1, h2⟩
        omega
    have hx_zero : x = x + 0 * 2 ^ r := by simp
    have hy_zero : y = y + 0 * 2 ^ r := by simp
    constructor
    · constructor
      · rw [mod_pow_two_of_mod_pow_two_succ h2Lx]
        conv => rhs; rw [hx_zero]
        rw [add_mul_pow_two_mod2_iff]
        exact hsum_props.1.1
      · rw [mod_pow_two_of_mod_pow_two_succ h2Ly]
        conv => rhs; rw [hy_zero]
        rw [add_mul_pow_two_mod2_iff]
        exact hsum_props.1.2
    · intro ⟨hx4, hy4⟩
      rw [h2Lx] at hx4
      rw [h2Ly] at hy4
      conv at hx4 => rhs; rw [hx_zero]
      conv at hy4 => rhs; rw [hy_zero]
      rw [add_mul_pow_two_mod4_iff] at hx4
      rw [add_mul_pow_two_mod4_iff] at hy4
      exact hsum_props.2 ⟨hx4, hy4⟩

/-! ### Part 5: Theorem 3 (Exact closed-form minimal period) -/

/-- Theorem 3 (Exact closed-form minimal period of every non-fixed state):
if `(x, y)` agrees with `(c, c)` modulo `2^r0` and differs modulo `2^(r0+1)` with `r0 < m`,
then its exact minimal period under `G_{c,m}` is `3 * 2^(m - 1 - r0)`. -/
theorem arxFibStep_exact_minPeriod (c m x y r0 : Nat)
    (_hm : 1 ≤ m) (hx : x < 2 ^ m) (hy : y < 2 ^ m) (hr0 : r0 < m)
    (hmatch : x % 2 ^ r0 = c % 2 ^ r0 ∧ y % 2 ^ r0 = c % 2 ^ r0)
    (hdiff : ¬(x % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1) ∧ y % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1))) :
    IsMinPeriod (arxFibStep c m) (x, y) (3 * 2 ^ (m - 1 - r0)) := by
  generalize hs_def : m - 1 - r0 = s
  have hms : r0 + s + 1 = m := by omega
  have hlift := arxFibRaw_lift c x y r0 s hmatch hdiff
  have hperiod : iter (arxFibStep c m) (3 * 2 ^ s) (x, y) = (x, y) := by
    rw [arxFibStep_iter_eq_mod c m (3 * 2 ^ s) x y hx hy]
    have h1 := hlift.1.1
    have h2 := hlift.1.2
    rw [hms, Nat.mod_eq_of_lt hx] at h1
    rw [hms, Nat.mod_eq_of_lt hy] at h2
    exact Prod.ext h1 h2
  refine ⟨by have := @Nat.one_le_two_pow s; omega, hperiod, ?_⟩
  intro k hk_pos hk_lt hk_eq
  let g := Nat.gcd k (3 * 2 ^ s)
  have hg_eq : iter (arxFibStep c m) g (x, y) = (x, y) :=
    iter_gcd_fixed (arxFibStep c m) (x, y) k (3 * 2 ^ s) hk_eq hperiod
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left (3 * 2 ^ s) hk_pos
  have hg_lt : g < 3 * 2 ^ s := by
    have hle : g ≤ k := Nat.gcd_le_left (3 * 2 ^ s) hk_pos
    omega
  have hg_dvd : g ∣ 3 * 2 ^ s := Nat.gcd_dvd_right k (3 * 2 ^ s)
  by_cases h3g : g % 3 = 0
  · -- `3 ∣ g`: then `g ∣ 3 * 2^(s - 1)`, contradicting the non-lift at level `s - 1`.
    have hs_pos : 1 ≤ s := by
      by_cases hs0 : s = 0
      · rw [hs0, Nat.pow_zero, Nat.mul_one] at hg_lt
        omega
      · omega
    let q := g / 3
    have hg3q : g = 3 * q := by omega
    have hq_dvd : q ∣ 2 ^ s := by
      rcases hg_dvd with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hg3q, Nat.mul_assoc] at ht
      omega
    have hq_lt : q < 2 ^ s := by omega
    have hs_eq : s = (s - 1) + 1 := by omega
    rw [hs_eq] at hq_dvd hq_lt
    have hq_dvd_prev : q ∣ 2 ^ (s - 1) := dvd_pow_two_of_lt hq_dvd hq_lt
    have hg_dvd_prev : g ∣ 3 * 2 ^ (s - 1) := by
      rcases hq_dvd_prev with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hg3q, ht, Nat.mul_assoc]
    have hprev_eq : iter (arxFibStep c m) (3 * 2 ^ (s - 1)) (x, y) = (x, y) :=
      iter_dvd_fixed (arxFibStep c m) (x, y) g (3 * 2 ^ (s - 1)) hg_eq hg_dvd_prev
    rw [arxFibStep_iter_eq_mod c m (3 * 2 ^ (s - 1)) x y hx hy] at hprev_eq
    have hlift_prev := arxFibRaw_lift c x y r0 (s - 1) hmatch hdiff
    have hm_prev : r0 + (s - 1) + 2 = m := by omega
    rw [hm_prev] at hlift_prev
    have hx_eq : (iter (arxFibRaw c) (3 * 2 ^ (s - 1)) (x, y)).1 % 2 ^ m = x % 2 ^ m := by
      rw [Nat.mod_eq_of_lt hx]
      exact congrArg Prod.fst hprev_eq
    have hy_eq : (iter (arxFibRaw c) (3 * 2 ^ (s - 1)) (x, y)).2 % 2 ^ m = y % 2 ^ m := by
      rw [Nat.mod_eq_of_lt hy]
      exact congrArg Prod.snd hprev_eq
    exact hlift_prev.2 ⟨hx_eq, hy_eq⟩
  · -- `¬(3 ∣ g)`: then `Nat.Coprime g 3`, so `g ∣ 2^s`, hence `iter (2^s)` fixes `(x, y)` mod `2^(r0+1)`.
    have hcop3 : Nat.Coprime g 3 := by
      unfold Nat.Coprime
      rw [Nat.gcd_comm, Nat.gcd_rec]
      have hmod3 : g % 3 = 1 ∨ g % 3 = 2 := by omega
      rcases hmod3 with h | h
      · rw [h]; decide
      · rw [h]; decide
    have hg_dvd_pow : g ∣ 2 ^ s := hcop3.dvd_of_dvd_mul_left hg_dvd
    have hpow_eq : iter (arxFibStep c m) (2 ^ s) (x, y) = (x, y) :=
      iter_dvd_fixed (arxFibStep c m) (x, y) g (2 ^ s) hg_eq hg_dvd_pow
    -- Reduce both `iter (2^s)` and `iter 3` modulo `2^(r0+1)` using `arxFibStep c (r0 + 1)`.
    have hdvd_r0 : 2 ^ (r0 + 1) ∣ 2 ^ m := by
      refine ⟨2 ^ s, ?_⟩
      rw [← Nat.pow_add, show r0 + 1 + s = m by omega]
    let p0 := (x % 2 ^ (r0 + 1), y % 2 ^ (r0 + 1))
    have hpos_r0 : 0 < 2 ^ (r0 + 1) := by have := @Nat.one_le_two_pow (r0 + 1); omega
    have hstep_r0 : ∀ n : Nat,
        iter (arxFibStep c (r0 + 1)) n p0 =
          ((iter (arxFibRaw c) n (x, y)).1 % 2 ^ (r0 + 1),
           (iter (arxFibRaw c) n (x, y)).2 % 2 ^ (r0 + 1)) := by
      intro n
      rw [arxFibStep_iter_eq_mod c (r0 + 1) n (x % 2 ^ (r0 + 1)) (y % 2 ^ (r0 + 1))
            (Nat.mod_lt x hpos_r0) (Nat.mod_lt y hpos_r0)]
      have hm := arxFibRaw_iter_mod_input c (r0 + 1) n
        (x % 2 ^ (r0 + 1)) (y % 2 ^ (r0 + 1)) x y (Nat.mod_mod _ _) (Nat.mod_mod _ _)
      exact Prod.ext hm.1 hm.2
    have hfix_pow : iter (arxFibStep c (r0 + 1)) (2 ^ s) p0 = p0 := by
      rw [hstep_r0 (2 ^ s)]
      rw [arxFibStep_iter_eq_mod c m (2 ^ s) x y hx hy] at hpow_eq
      have h1 : (iter (arxFibRaw c) (2 ^ s) (x, y)).1 % 2 ^ m = x := congrArg Prod.fst hpow_eq
      have h2 : (iter (arxFibRaw c) (2 ^ s) (x, y)).2 % 2 ^ m = y := congrArg Prod.snd hpow_eq
      refine Prod.ext ?_ ?_
      · dsimp only [p0]; rw [← Nat.mod_mod_of_dvd _ hdvd_r0, h1]
      · dsimp only [p0]; rw [← Nat.mod_mod_of_dvd _ hdvd_r0, h2]
    have hfix_3 : iter (arxFibStep c (r0 + 1)) 3 p0 = p0 := by
      rw [hstep_r0 3]
      have hlift0 := arxFibRaw_lift c x y r0 0 hmatch hdiff
      simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero] at hlift0
      exact Prod.ext hlift0.1.1 hlift0.1.2
    have hfix_1 : iter (arxFibStep c (r0 + 1)) 1 p0 = p0 := by
      have hg1 := iter_gcd_fixed (arxFibStep c (r0 + 1)) p0 (2 ^ s) 3 hfix_pow hfix_3
      rw [gcd_pow_two_three s] at hg1
      exact hg1
    rw [hstep_r0 1] at hfix_1
    exact arxFibRaw_step1_ne_mod c x y r0 hmatch hdiff
      ⟨congrArg Prod.fst hfix_1, congrArg Prod.snd hfix_1⟩

/-! ### Part 6: Theorem 4 (Exact key-invariant cycle spectrum via involution) -/

private theorem exists_first_diff_bit (m x y c : Nat)
    (hne : ¬(x % 2 ^ m = c % 2 ^ m ∧ y % 2 ^ m = c % 2 ^ m)) :
    ∃ r0 : Nat, r0 < m ∧
      (x % 2 ^ r0 = c % 2 ^ r0 ∧ y % 2 ^ r0 = c % 2 ^ r0) ∧
      ¬(x % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1) ∧ y % 2 ^ (r0 + 1) = c % 2 ^ (r0 + 1)) := by
  induction m with
  | zero =>
    exfalso
    exact hne ⟨by simp [Nat.mod_one], by simp [Nat.mod_one]⟩
  | succ m ih =>
    by_cases hm : x % 2 ^ m = c % 2 ^ m ∧ y % 2 ^ m = c % 2 ^ m
    · exact ⟨m, by omega, hm, hne⟩
    · rcases ih hm with ⟨r0, hr0, hmatch, hdiff⟩
      exact ⟨r0, by omega, hmatch, hdiff⟩

private theorem mod_pow_two_xor_zero_iff (c m x k : Nat) (hk : k ≤ m) :
    (x ^^^ (c % 2 ^ m)) % 2 ^ k = 0 % 2 ^ k ↔ x % 2 ^ k = c % 2 ^ k := by
  have hdvd : 2 ^ k ∣ 2 ^ m := by
    refine ⟨2 ^ (m - k), ?_⟩
    rw [← Nat.pow_add, Nat.add_sub_of_le hk]
  rw [xor_mod_two_pow, Nat.mod_mod_of_dvd c hdvd, Nat.zero_mod]
  constructor
  · intro h
    have h' := congrArg (fun z => z ^^^ (c % 2 ^ k)) h
    simpa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using h'
  · intro h
    rw [h, Nat.xor_self]

private theorem minPeriod_fixed_iff {α : Type} (F : α → α) (p : α) (L : Nat)
    (hfix : F p = p) : IsMinPeriod F p L ↔ L = 1 := by
  constructor
  · rintro ⟨hpos, _, hmin⟩
    by_cases h1 : L = 1
    · exact h1
    · exact False.elim (hmin 1 (by omega) (by omega) hfix)
  · rintro rfl
    exact ⟨by omega, hfix, fun k hk1 hk2 => by omega⟩

/-- Theorem 4 (Exact key-invariant cycle spectrum via period-preserving involution):
for every `m ≥ 1`, every key `c`, every period `L`, and every `(x, y) ∈ {0, ..., 2^m - 1}^2`,
the involution `(x, y) ↦ (x ^^^ (c % 2^m), y ^^^ (c % 2^m))` preserves exact minimal periods
between `G_{c,m}` and unkeyed linear Fibonacci `G_{0,m}`. -/
theorem arxFibStep_isospectral_bijection (c m x y L : Nat)
    (hm : 1 ≤ m) (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    IsMinPeriod (arxFibStep c m) (x, y) L ↔
      IsMinPeriod (arxFibStep 0 m) (x ^^^ (c % 2 ^ m), y ^^^ (c % 2 ^ m)) L := by
  have hpos : 0 < 2 ^ m := by have := @Nat.one_le_two_pow m; omega
  have hcm_lt : c % 2 ^ m < 2 ^ m := Nat.mod_lt c hpos
  have hx' : x ^^^ (c % 2 ^ m) < 2 ^ m := xor_lt_two_pow hx hcm_lt
  have hy' : y ^^^ (c % 2 ^ m) < 2 ^ m := xor_lt_two_pow hy hcm_lt
  by_cases hfix : x = c % 2 ^ m ∧ y = c % 2 ^ m
  · rcases hfix with ⟨rfl, rfl⟩
    rw [Nat.xor_self]
    have hf1 : arxFibStep c m (c % 2 ^ m, c % 2 ^ m) = (c % 2 ^ m, c % 2 ^ m) :=
      (arxFibStep_fixed_point_iff c m (c % 2 ^ m) (c % 2 ^ m) hm hcm_lt hcm_lt).mpr ⟨rfl, rfl⟩
    have hf2 : arxFibStep 0 m (0, 0) = (0, 0) :=
      (arxFibStep_fixed_point_iff 0 m 0 0 hm hpos hpos).mpr ⟨by simp, by simp⟩
    rw [minPeriod_fixed_iff _ _ L hf1, minPeriod_fixed_iff _ _ L hf2]
  · have hne_mod : ¬(x % 2 ^ m = c % 2 ^ m ∧ y % 2 ^ m = c % 2 ^ m) := by
      rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
      exact hfix
    rcases exists_first_diff_bit m x y c hne_mod with ⟨r0, hr0, hmatch, hdiff⟩
    have hmatch0 : (x ^^^ (c % 2 ^ m)) % 2 ^ r0 = 0 % 2 ^ r0 ∧
        (y ^^^ (c % 2 ^ m)) % 2 ^ r0 = 0 % 2 ^ r0 :=
      ⟨(mod_pow_two_xor_zero_iff c m x r0 (by omega)).mpr hmatch.1,
       (mod_pow_two_xor_zero_iff c m y r0 (by omega)).mpr hmatch.2⟩
    have hdiff0 : ¬((x ^^^ (c % 2 ^ m)) % 2 ^ (r0 + 1) = 0 % 2 ^ (r0 + 1) ∧
        (y ^^^ (c % 2 ^ m)) % 2 ^ (r0 + 1) = 0 % 2 ^ (r0 + 1)) := by
      intro ⟨h1, h2⟩
      exact hdiff ⟨(mod_pow_two_xor_zero_iff c m x (r0 + 1) (by omega)).mp h1,
                   (mod_pow_two_xor_zero_iff c m y (r0 + 1) (by omega)).mp h2⟩
    have hp_c := arxFibStep_exact_minPeriod c m x y r0 hm hx hy hr0 hmatch hdiff
    have hp_0 := arxFibStep_exact_minPeriod 0 m (x ^^^ (c % 2 ^ m)) (y ^^^ (c % 2 ^ m)) r0
      hm hx' hy' hr0 hmatch0 hdiff0
    constructor
    · intro hL
      have heq := minPeriod_unique hL hp_c
      rwa [heq]
    · intro hL
      have heq := minPeriod_unique hL hp_0
      rwa [heq]

/-! ### Part 7: Theorem 5 (Contrast witness for `3 * x + (y ^^^ c)`) -/

/-- Theorem 5 (Sharpness contrast witness for `3 * x + (y ^^^ c)`):
changing `1 * x` to `3 * x` destroys key-invariance already at `m = 2`:
for `c = 1` every 2-bit state satisfies `H_{1,2}^3(x, y) = (x, y)` (zero period-6 states),
whereas for `c = 0` the state `(0, 1)` has exact minimal period `6`. -/
theorem arxFibStep3_breaks_isospectrality :
    (∀ x y : Nat, x < 4 → y < 4 → iter (arxFibStep3 1 2) 3 (x, y) = (x, y)) ∧
    IsMinPeriod (arxFibStep3 0 2) (0, 1) 6 := by
  constructor
  · intro x y hx hy
    match x, y with
    | 0, 0 => decide
    | 0, 1 => decide
    | 0, 2 => decide
    | 0, 3 => decide
    | 1, 0 => decide
    | 1, 1 => decide
    | 1, 2 => decide
    | 1, 3 => decide
    | 2, 0 => decide
    | 2, 1 => decide
    | 2, 2 => decide
    | 2, 3 => decide
    | 3, 0 => decide
    | 3, 1 => decide
    | 3, 2 => decide
    | 3, 3 => decide
    | _ + 4, _ => omega
    | _, _ + 4 => omega
  · refine ⟨by decide, by decide, ?_⟩
    intro k hk1 hk6
    match k with
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | 0 => omega
    | _ + 6 => omega

end ArxFibonacciIsospectrality
