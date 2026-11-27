import CirculantCarryBitSplittingCones.Defs

set_option autoImplicit false

namespace Adic16
theorem popcountFuel_eq (fuel1 fuel2 n : Nat) (h1 : n ≤ fuel1) (h2 : n ≤ fuel2) :
    popcountFuel fuel1 n = popcountFuel fuel2 n := by
  induction fuel1 generalizing fuel2 n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    cases fuel2 <;> rfl
  | succ f1 ih =>
    cases fuel2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [popcountFuel]
    | succ f2 =>
      simp only [popcountFuel]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ite_false]
        congr 1
        exact ih f2 (n / 2) (by omega) (by omega)

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_step (n : Nat) : popcount n = n % 2 + popcount (n / 2) := by
  by_cases hn : n = 0
  · subst hn; rfl
  · unfold popcount
    cases n with
    | zero => exact absurd rfl hn
    | succ k =>
      simp only [popcountFuel, Nat.succ_ne_zero, ite_false]
      congr 1
      exact popcountFuel_eq k ((k + 1) / 2) ((k + 1) / 2) (by omega) (Nat.le_refl _)

theorem popcount_two_mul (n : Nat) : popcount (2 * n) = popcount n := by
  rw [popcount_step]
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  rw [h1, h2, Nat.zero_add]

theorem popcount_two_mul_add_one (n : Nat) : popcount (2 * n + 1) = 1 + popcount n := by
  rw [popcount_step]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]

theorem popcount_two_mul_add_bit (n b : Nat) (hb : b < 2) :
    popcount (2 * n + b) = b + popcount n := by
  have : b = 0 ∨ b = 1 := by omega
  rcases this with rfl | rfl
  · simp [popcount_two_mul]
  · exact popcount_two_mul_add_one n

theorem popcount_mul_pow2_add (m : Nat) :
    ∀ (q r : Nat), r < 2 ^ m → popcount (q * 2 ^ m + r) = popcount q + popcount r := by
  induction m with
  | zero =>
    intro q r hr
    have hr0 : r = 0 := by simp at hr; omega
    subst hr0
    simp [popcount_zero]
  | succ m ih =>
    intro q r hr
    have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
    have hr_div : r / 2 < 2 ^ m := by omega
    have hmul : q * (2 ^ m * 2) = 2 * (q * 2 ^ m) := by
      rw [Nat.mul_comm (2 ^ m) 2, ← Nat.mul_assoc, Nat.mul_comm q 2, Nat.mul_assoc]
    have hdecomp : q * 2 ^ (m + 1) + r = 2 * (q * 2 ^ m + r / 2) + r % 2 := by
      rw [hpow, hmul]; omega
    rw [hdecomp, popcount_two_mul_add_bit _ _ (by omega)]
    rw [ih q (r / 2) hr_div]
    conv => rhs; rw [popcount_step r]
    omega

theorem popcount_complement (m : Nat) :
    ∀ u : Nat, u < 2 ^ m → popcount (2 ^ m - 1 - u) + popcount u = m := by
  induction m with
  | zero =>
    intro u hu
    have hu0 : u = 0 := by simp at hu; omega
    subst hu0
    simp [popcount_zero]
  | succ m ih =>
    intro u hu
    have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
    have hu_div : u / 2 < 2 ^ m := by omega
    have h1 : 2 ^ (m + 1) - 1 - u = 2 * (2 ^ m - 1 - u / 2) + (1 - u % 2) := by
      have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      rw [hpow]; omega
    rw [h1, popcount_two_mul_add_bit _ _ (by omega)]
    rw [popcount_step u]
    have hih := ih (u / 2) hu_div
    omega

/-- Bitwise-OR binary splitting lemma: `(2*x + b) ||| (2*y + a) = 2*(x ||| y) + (b ||| a)`. -/
theorem lor_two_mul_add_bit (x y b a : Nat) (hb : b < 2) (ha : a < 2) :
    (2 * x + b) ||| (2 * y + a) = 2 * (x ||| y) + (b ||| a) := by
  have hba : b ||| a < 2 := by
    have hb2 : b = 0 ∨ b = 1 := by omega
    have ha2 : a = 0 ∨ a = 1 := by omega
    rcases hb2 with rfl | rfl <;> rcases ha2 with rfl | rfl <;> decide
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero =>
    rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    have h1 : (2 * x + b) % 2 = b := by omega
    have h2 : (2 * y + a) % 2 = a := by omega
    have h3 : (2 * (x ||| y) + (b ||| a)) % 2 = b ||| a := by omega
    rw [h1, h2, h3]
    have hb2 : b = 0 ∨ b = 1 := by omega
    have ha2 : a = 0 ∨ a = 1 := by omega
    rcases hb2 with rfl | rfl <;> rcases ha2 with rfl | rfl <;> decide
  | succ k =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1 : (2 * x + b) / 2 = x := by omega
    have h2 : (2 * y + a) / 2 = y := by omega
    have h3 : (2 * (x ||| y) + (b ||| a)) / 2 = x ||| y := by omega
    rw [h1, h2, h3, Nat.testBit_or]

theorem sumRange_congr {N : Nat} {f g : Nat → Int} (h : ∀ k, k < N → f k = g k) :
    sumRange N f = sumRange N g := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [sumRange]
    rw [ih (fun k hk => h k (by omega)), h N (by omega)]

theorem sumRange_add_fn (N : Nat) (f g : Nat → Int) :
    sumRange N (fun k => f k + g k) = sumRange N f + sumRange N g := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih => simp only [sumRange, ih]; omega

theorem sumRange_mul_left (N : Nat) (c : Int) (f : Nat → Int) :
    sumRange N (fun k => c * f k) = c * sumRange N f := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih => simp only [sumRange, ih, Int.mul_add]

theorem sumRange_mul_right (N : Nat) (f : Nat → Int) (c : Int) :
    sumRange N (fun k => f k * c) = sumRange N f * c := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih => simp only [sumRange, ih, Int.add_mul]

theorem sumRange_zero_fn (N : Nat) : sumRange N (fun _ => 0) = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => simp [sumRange, ih]

theorem sumRange_add (A B : Nat) (f : Nat → Int) :
    sumRange (A + B) f = sumRange A f + sumRange B (fun i => f (A + i)) := by
  induction B with
  | zero => simp [sumRange]
  | succ B ih =>
    have h : A + (B + 1) = (A + B) + 1 := by omega
    rw [h, sumRange, sumRange, ih]
    omega

theorem sumRange_succ_left (N : Nat) (f : Nat → Int) :
    sumRange (N + 1) f = f 0 + sumRange N (fun i => f (i + 1)) := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih =>
    rw [sumRange, ih, sumRange]
    omega

theorem sumRange_swap (A B : Nat) (f : Nat → Nat → Int) :
    sumRange A (fun i => sumRange B (fun j => f i j)) =
    sumRange B (fun j => sumRange A (fun i => f i j)) := by
  induction A with
  | zero => simp [sumRange, sumRange_zero_fn]
  | succ A ih =>
    simp only [sumRange, ih]
    rw [← sumRange_add_fn]

theorem sumRange_mul_block (Q B : Nat) (f : Nat → Int) :
    sumRange (Q * B) f = sumRange B (fun d => sumRange Q (fun q => f (q * B + d))) := by
  induction Q with
  | zero => simp [sumRange, sumRange_zero_fn]
  | succ Q ih =>
    have h : (Q + 1) * B = Q * B + B := Nat.succ_mul Q B
    rw [h, sumRange_add, ih, ← sumRange_add_fn]
    apply sumRange_congr
    intro d _
    simp only [sumRange]

theorem sumRange_two_mul (N : Nat) (f : Nat → Int) :
    sumRange (2 * N) f = sumRange N (fun k => f (2 * k)) + sumRange N (fun k => f (2 * k + 1)) := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih =>
    have h : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
    rw [h, sumRange, sumRange, ih, sumRange, sumRange]
    omega

theorem sumRange_two_mul_add_one (N : Nat) (f : Nat → Int) :
    sumRange (2 * N + 1) f =
    sumRange (N + 1) (fun k => f (2 * k)) + sumRange N (fun k => f (2 * k + 1)) := by
  rw [sumRange, sumRange_two_mul, sumRange]
  omega

theorem sumRange_paritySign_eq_count_diff (N : Nat) (f : Nat → Nat) :
    sumRange N (fun n => paritySign (f n)) =
    (countMod N 2 0 f : Int) - (countMod N 2 1 f : Int) := by
  induction N with
  | zero => simp [sumRange, countMod]
  | succ N ih =>
    rw [sumRange, ih, countMod, countMod]
    unfold paritySign
    by_cases h : f N % 2 = 0
    · simp [h]; omega
    · have h1 : f N % 2 = 1 % 2 := by omega
      simp [h1]; omega

theorem countMod_eq_sumRange (N m r : Nat) (f : Nat → Nat) :
    (countMod N m r f : Int) =
    sumRange N (fun n => if f n % m = r % m then 1 else 0) := by
  induction N with
  | zero => simp [countMod, sumRange]
  | succ N ih =>
    rw [countMod, sumRange, ← ih]
    split <;> omega

theorem sumFin_congr {d : Nat} {f g : Fin d → Int} (h : ∀ i, f i = g i) :
    sumFin d f = sumFin d g := by
  unfold sumFin
  apply sumRange_congr
  intro k hk
  simp [hk, h]

theorem sumFin_add (d : Nat) (f g : Fin d → Int) :
    sumFin d (fun i => f i + g i) = sumFin d f + sumFin d g := by
  unfold sumFin
  rw [← sumRange_add_fn]
  apply sumRange_congr
  intro k hk
  simp [hk]

theorem sumFin_zero (d : Nat) : sumFin d (fun _ => 0) = 0 := by
  unfold sumFin
  have h : sumRange d (fun i => if _ : i < d then (0 : Int) else 0) = sumRange d (fun _ => 0) := by
    apply sumRange_congr; intro k hk; simp [hk]
  rw [h, sumRange_zero_fn]

theorem sumFin_mul_left (d : Nat) (c : Int) (f : Fin d → Int) :
    sumFin d (fun i => c * f i) = c * sumFin d f := by
  unfold sumFin
  rw [← sumRange_mul_left]
  apply sumRange_congr
  intro k hk; simp [hk]

theorem sumFin_mul_right (d : Nat) (f : Fin d → Int) (c : Int) :
    sumFin d (fun i => f i * c) = sumFin d f * c := by
  unfold sumFin
  rw [← sumRange_mul_right]
  apply sumRange_congr
  intro k hk; simp [hk]

theorem sumFin_swap (a b : Nat) (f : Fin a → Fin b → Int) :
    sumFin a (fun i => sumFin b (fun j => f i j)) =
    sumFin b (fun j => sumFin a (fun i => f i j)) := by
  unfold sumFin
  have h1 : sumRange a (fun i => if hi : i < a then sumRange b (fun j => if hj : j < b then f ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0) =
            sumRange a (fun i => sumRange b (fun j => if hi : i < a then if hj : j < b then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0)) := by
    apply sumRange_congr; intro i hi; simp [hi]
  have h2 : sumRange b (fun j => if hj : j < b then sumRange a (fun i => if hi : i < a then f ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0) =
            sumRange b (fun j => sumRange a (fun i => if hi : i < a then if hj : j < b then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0)) := by
    apply sumRange_congr; intro j hj
    simp only [hj, dite_true]
  rw [h1, h2, sumRange_swap]

theorem sumFin_single {d : Nat} (k : Fin d) (f : Fin d → Int) :
    sumFin d (fun i => if i = k then f i else 0) = f k := by
  unfold sumFin
  have aux : ∀ N, N ≤ d →
      sumRange N (fun i => if h : i < d then (if (⟨i, h⟩ : Fin d) = k then f ⟨i, h⟩ else 0) else 0) =
      if k.val < N then f k else 0 := by
    intro N hN
    induction N with
    | zero => simp [sumRange]
    | succ N ih =>
      simp only [sumRange]
      rw [ih (by omega)]
      have hNd : N < d := by omega
      simp only [hNd, dite_true]
      by_cases hEq : N = k.val
      · have hfin : (⟨N, hNd⟩ : Fin d) = k := Fin.ext hEq
        have hlt1 : ¬ (k.val < N) := by omega
        have hlt2 : k.val < N + 1 := by omega
        simp [hfin, hlt1, hlt2]
      · have hfin : (⟨N, hNd⟩ : Fin d) ≠ k := fun hc => hEq (congrArg Fin.val hc)
        by_cases hlt : k.val < N
        · have hlt2 : k.val < N + 1 := by omega
          simp [hfin, hlt, hlt2]
        · have hlt2 : ¬ (k.val < N + 1) := by omega
          simp [hfin, hlt, hlt2]
  have h := aux d (Nat.le_refl d)
  simp [k.isLt] at h
  exact h

theorem sumFin_le_sumFin {d : Nat} {f g : Fin d → Int} (hfg : ∀ i, f i ≤ g i) :
    sumFin d f ≤ sumFin d g := by
  unfold sumFin
  have aux : ∀ N, N ≤ d →
      sumRange N (fun i => if h : i < d then f ⟨i, h⟩ else 0) ≤
      sumRange N (fun i => if h : i < d then g ⟨i, h⟩ else 0) := by
    intro N hN
    induction N with
    | zero => simp [sumRange]
    | succ N ih =>
      simp only [sumRange]
      have h1 := ih (by omega)
      have hNd : N < d := by omega
      have h2 := hfg ⟨N, hNd⟩
      simp only [hNd, dite_true]
      omega
  exact aux d (Nat.le_refl d)

/-- Reversing `sumRange k`. -/
theorem sumRange_reverse (k : Nat) (g : Nat → Int) :
    sumRange k (fun j => g (k - 1 - j)) = sumRange k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sumRange_succ_left]
    have h0 : k + 1 - 1 - 0 = k := by omega
    rw [h0]
    have htail : sumRange k (fun i => g (k + 1 - 1 - (i + 1))) = sumRange k (fun i => g (k - 1 - i)) := by
      apply sumRange_congr; intro i _
      have : k + 1 - 1 - (i + 1) = k - 1 - i := by omega
      rw [this]
    rw [htail, ih, sumRange]
    omega

/-- Reindexing `sumFin m` by negation `i ↦ (m - i) % m`. -/
theorem sumFin_neg {m : Nat} (hm : 0 < m) (f : Fin m → Int) :
    sumFin m (fun i => f ⟨(m - i.val) % m, Nat.mod_lt _ hm⟩) = sumFin m f := by
  unfold sumFin
  cases m with
  | zero => omega
  | succ m =>
    rw [sumRange_succ_left, sumRange_succ_left]
    have h0L : (if h : 0 < m + 1 then f ⟨(m + 1 - 0) % (m + 1), Nat.mod_lt _ hm⟩ else 0) = f ⟨0, hm⟩ := by
      simp only [hm, dite_true]
      congr 1; exact Fin.ext (Nat.mod_self (m + 1))
    have h0R : (if h : 0 < m + 1 then f ⟨0, h⟩ else 0) = f ⟨0, hm⟩ := by
      simp [hm]
    rw [h0L, h0R]
    congr 1
    let g : Nat → Int := fun j => if hj : j < m then f ⟨j + 1, by omega⟩ else 0
    have hL : sumRange m (fun j => if h : j + 1 < m + 1 then f ⟨(m + 1 - (j + 1)) % (m + 1), Nat.mod_lt _ hm⟩ else 0) =
              sumRange m (fun j => g (m - 1 - j)) := by
      apply sumRange_congr; intro j hj
      have h1 : j + 1 < m + 1 := by omega
      have h2 : m - 1 - j < m := by omega
      simp only [h1, h2, dite_true, g]
      congr 1; apply Fin.ext; dsimp only
      have hsub : m + 1 - (j + 1) = m - 1 - j + 1 := by omega
      rw [hsub, Nat.mod_eq_of_lt (by omega)]
    have hR : sumRange m (fun j => if h : j + 1 < m + 1 then f ⟨j + 1, h⟩ else 0) =
              sumRange m g := by
      apply sumRange_congr; intro j hj
      have h1 : j + 1 < m + 1 := by omega
      simp only [h1, hj, dite_true, g]
    rw [hL, hR, sumRange_reverse]

/-- Reindexing `sumFin m` by cyclic shift `i ↦ (i + s) % m`. -/
theorem sumFin_shift {m : Nat} (hm : 0 < m) (s : Nat) (f : Fin m → Int) :
    sumFin m (fun i => f ⟨(i.val + s) % m, Nat.mod_lt _ hm⟩) = sumFin m f := by
  have hstep : ∀ g : Fin m → Int,
      sumFin m (fun i => g ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩) = sumFin m g := by
    intro g
    unfold sumFin
    cases m with
    | zero => omega
    | succ m =>
      rw [sumRange, sumRange_succ_left]
      have hlast : (if h : m < m + 1 then g ⟨(m + 1) % (m + 1), Nat.mod_lt _ hm⟩ else 0) = g ⟨0, hm⟩ := by
        have hlt : m < m + 1 := by omega
        simp only [hlt, dite_true]
        congr 1; exact Fin.ext (Nat.mod_self (m + 1))
      have hfirst : (if h : 0 < m + 1 then g ⟨0, h⟩ else 0) = g ⟨0, hm⟩ := by
        simp [hm]
      have hmid : sumRange m (fun i => if h : i < m + 1 then g ⟨(i + 1) % (m + 1), Nat.mod_lt _ hm⟩ else 0) =
                  sumRange m (fun i => if h : i + 1 < m + 1 then g ⟨i + 1, h⟩ else 0) := by
        apply sumRange_congr; intro i hi
        have h1 : i < m + 1 := by omega
        have h2 : i + 1 < m + 1 := by omega
        simp only [h1, h2, dite_true]
        congr 1; exact Fin.ext (Nat.mod_eq_of_lt h2)
      rw [hlast, hfirst, hmid]
      omega
  induction s with
  | zero =>
    apply sumFin_congr; intro i
    congr 1; exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  | succ s ih =>
    have heq : sumFin m (fun i => f ⟨(i.val + (s + 1)) % m, Nat.mod_lt _ hm⟩) =
               sumFin m (fun i => f ⟨((i.val + 1) % m + s) % m, Nat.mod_lt _ hm⟩) := by
      apply sumFin_congr; intro i
      congr 1; apply Fin.ext; dsimp only
      have hadd : i.val + (s + 1) = (i.val + 1) + s := by omega
      rw [hadd, Nat.add_mod (i.val + 1) s, Nat.add_mod ((i.val + 1) % m) s, Nat.mod_mod]
    rw [heq, hstep (fun i => f ⟨(i.val + s) % m, Nat.mod_lt _ hm⟩), ih]

-- ============================================================================
-- SECTION 1: ENGINE I — INVOLUTIVE RING BASE-2^m CIRCULANT CARRY-TRANSFER
-- ============================================================================

theorem grRev_involutive {m : Nat} (hm : 0 < m) (a : GR m) :
    grRev hm (grRev hm a) = a := by
  funext r
  unfold grRev
  congr 1
  apply Fin.ext; dsimp only
  have hr := r.isLt
  by_cases h0 : r.val = 0
  · simp [h0]
  · have h1 : (m - r.val) % m = m - r.val := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h2 : m - (m - r.val) = r.val := by omega
    rw [h2, Nat.mod_eq_of_lt hr]

theorem grRev_add {m : Nat} (hm : 0 < m) (a b : GR m) :
    grRev hm (grAdd a b) = grAdd (grRev hm a) (grRev hm b) := rfl

theorem grRev_zero {m : Nat} (hm : 0 < m) : grRev hm (grZero m) = grZero m := rfl

theorem grRev_unit {m : Nat} (hm : 0 < m) (s : Nat) :
    grRev hm (grUnit s) = grUnit (m - s % m) := by
  funext r
  unfold grRev grUnit
  have hr := r.isLt
  have hs := Nat.mod_lt s hm
  have hiff : (m - r.val) % m = s % m ↔ r.val = (m - s % m) % m := by
    by_cases h0 : r.val = 0
    · by_cases hs0 : s % m = 0
      · simp [h0, hs0]
      · have h1 : (m - s % m) % m = m - s % m := Nat.mod_eq_of_lt (by omega)
        simp [h0, h1]; omega
    · have h1 : (m - r.val) % m = m - r.val := Nat.mod_eq_of_lt (by omega)
      by_cases hs0 : s % m = 0
      · simp [h1, hs0]; omega
      · have h2 : (m - s % m) % m = m - s % m := Nat.mod_eq_of_lt (by omega)
        rw [h1, h2]; omega
  by_cases h : (m - r.val) % m = s % m
  · have h2 : r.val = (m - s % m) % m := hiff.mp h
    simp only [h, ite_true]
    simp only [h2, ite_true]
  · have h2 : r.val ≠ (m - s % m) % m := fun hc => h (hiff.mpr hc)
    simp only [h, ite_false]
    simp only [h2, ite_false]

theorem grMul_comm {m : Nat} (hm : 0 < m) (a b : GR m) :
    grMul hm a b = grMul hm b a := by
  funext r
  unfold grMul
  have h1 := sumFin_neg hm (fun j => b j * a ⟨(r.val + m - j.val) % m, Nat.mod_lt _ hm⟩)
  rw [← h1]
  have h2 := sumFin_shift hm (m - r.val) (fun i =>
    b ⟨(m - i.val) % m, Nat.mod_lt _ hm⟩ *
    a ⟨(r.val + m - (m - i.val) % m) % m, Nat.mod_lt _ hm⟩)
  rw [← h2]
  apply sumFin_congr
  intro i
  have hi := i.isLt
  have hr := r.isLt
  have hidx1 : (m - (i.val + (m - r.val)) % m) % m = (r.val + m - i.val) % m := by
    by_cases hxy : i.val ≤ r.val
    · by_cases heq : i.val = r.val
      · have hsum : i.val + (m - r.val) = m := by omega
        have hsub : r.val + m - i.val = m := by omega
        rw [hsum, hsub, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
      · have hlt : i.val + (m - r.val) < m := by omega
        rw [Nat.mod_eq_of_lt hlt]
        have : m - (i.val + (m - r.val)) = r.val - i.val := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
        have : r.val + m - i.val = (r.val - i.val) + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have hmod : (i.val + (m - r.val)) % m = i.val - r.val := by
        have : i.val + (m - r.val) = (i.val - r.val) + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      have : m - (i.val - r.val) = r.val + m - i.val := by omega
      rw [this]
  have hidx2 : (r.val + m - (m - (i.val + (m - r.val)) % m) % m) % m = i.val := by
    rw [hidx1]
    by_cases hir : i.val ≤ r.val
    · have hmod : (r.val + m - i.val) % m = r.val - i.val := by
        have : r.val + m - i.val = (r.val - i.val) + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      have : r.val + m - (r.val - i.val) = i.val + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    · have hmod : (r.val + m - i.val) % m = r.val + m - i.val := Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      have : r.val + m - (r.val + m - i.val) = i.val := by omega
      rw [this, Nat.mod_eq_of_lt hi]
  have hf1 : (⟨(m - (i.val + (m - r.val)) % m) % m, Nat.mod_lt _ hm⟩ : Fin m) =
             ⟨(r.val + m - i.val) % m, Nat.mod_lt _ hm⟩ := Fin.ext hidx1
  have hf2 : (⟨(r.val + m - (m - (i.val + (m - r.val)) % m) % m) % m, Nat.mod_lt _ hm⟩ : Fin m) = i :=
    Fin.ext hidx2
  rw [hf1, hf2, Int.mul_comm]

theorem grMul_unit_left {m : Nat} (hm : 0 < m) (s : Nat) (a : GR m) :
    grMul hm (grUnit s) a = fun r => a ⟨(r.val + m - s % m) % m, Nat.mod_lt _ hm⟩ := by
  funext r
  unfold grMul grUnit
  let k : Fin m := ⟨s % m, Nat.mod_lt s hm⟩
  have h : sumFin m (fun i => (if i.val = s % m then (1 : Int) else 0) *
                              a ⟨(r.val + m - i.val) % m, Nat.mod_lt _ hm⟩) =
           sumFin m (fun i => if i = k then a ⟨(r.val + m - i.val) % m, Nat.mod_lt _ hm⟩ else 0) := by
    apply sumFin_congr; intro i
    by_cases heq : i = k
    · subst heq; simp [k]
    · have hne : i.val ≠ s % m := fun hc => heq (Fin.ext hc)
      simp [heq, hne]
  rw [h, sumFin_single k]

theorem grMul_unit_zero_left {m : Nat} (hm : 0 < m) (a : GR m) :
    grMul hm (grUnit 0) a = a := by
  rw [grMul_unit_left]
  funext r
  congr 1; apply Fin.ext
  simp only [Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]

theorem grMul_add_right {m : Nat} (hm : 0 < m) (a b c : GR m) :
    grMul hm a (grAdd b c) = grAdd (grMul hm a b) (grMul hm a c) := by
  funext r; unfold grMul grAdd
  rw [← sumFin_add]
  apply sumFin_congr; intro i; exact Int.mul_add _ _ _

theorem grMul_add_left {m : Nat} (hm : 0 < m) (a b c : GR m) :
    grMul hm (grAdd a b) c = grAdd (grMul hm a c) (grMul hm b c) := by
  rw [grMul_comm, grMul_add_right, grMul_comm hm c a, grMul_comm hm c b]

theorem grMul_zero_left {m : Nat} (hm : 0 < m) (a : GR m) :
    grMul hm (grZero m) a = grZero m := by
  funext r; unfold grMul grZero
  have : sumFin m (fun i => (0 : Int) * a ⟨(r.val + m - i.val) % m, Nat.mod_lt _ hm⟩) =
         sumFin m (fun _ => 0) := by
    apply sumFin_congr; intro i; simp
  rw [this, sumFin_zero]

theorem grMul_zero_right {m : Nat} (hm : 0 < m) (a : GR m) :
    grMul hm a (grZero m) = grZero m := by
  rw [grMul_comm, grMul_zero_left]

theorem grRev_mul {m : Nat} (hm : 0 < m) (a b : GR m) :
    grRev hm (grMul hm a b) = grMul hm (grRev hm a) (grRev hm b) := by
  funext r
  unfold grRev grMul
  rw [← sumFin_neg hm]
  apply sumFin_congr
  intro i
  congr 1
  congr 1
  apply Fin.ext; dsimp only
  have hi := i.isLt
  have hr := r.isLt
  by_cases hr0 : r.val = 0
  · by_cases hi0 : i.val = 0
    · simp [hr0, hi0]
    · have hmi : (m - i.val) % m = m - i.val := Nat.mod_eq_of_lt (by omega)
      have h1 : m - (m - i.val) = i.val := by omega
      simp only [hr0, Nat.sub_zero, Nat.mod_self, Nat.zero_add, hmi, h1, Nat.mod_eq_of_lt hi]
  · have hmr : (m - r.val) % m = m - r.val := Nat.mod_eq_of_lt (by omega)
    rw [hmr]
    by_cases hi0 : i.val = 0
    · simp only [hi0, Nat.sub_zero, Nat.mod_self, Nat.add_mod_right, Nat.mod_eq_of_lt hr, hmr]
    · have hmi : (m - i.val) % m = m - i.val := Nat.mod_eq_of_lt (by omega)
      rw [hmi]
      by_cases hri : i.val ≤ r.val
      · have hsub1 : (r.val + m - i.val) % m = r.val - i.val := by
          have : r.val + m - i.val = (r.val - i.val) + m := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hsub1]
        have hsub2 : m - r.val + m - (m - i.val) = m - (r.val - i.val) := by omega
        rw [hsub2]
      · have hsub1 : (r.val + m - i.val) % m = r.val + m - i.val := Nat.mod_eq_of_lt (by omega)
        rw [hsub1]
        have hsub2 : m - r.val + m - (m - i.val) = (i.val - r.val) + m := by omega
        have hsub3 : m - (r.val + m - i.val) = i.val - r.val := by omega
        rw [hsub2, hsub3, Nat.add_mod_right]

theorem grMul_assoc {m : Nat} (hm : 0 < m) (a b c : GR m) :
    grMul hm (grMul hm a b) c = grMul hm a (grMul hm b c) := by
  funext r
  unfold grMul
  have hL : sumFin m (fun i => sumFin m (fun j => a j * b ⟨(i.val + m - j.val) % m, Nat.mod_lt _ hm⟩) *
                               c ⟨(r.val + m - i.val) % m, Nat.mod_lt _ hm⟩) =
            sumFin m (fun j => a j * sumFin m (fun i => b ⟨(i.val + m - j.val) % m, Nat.mod_lt _ hm⟩ *
                                                        c ⟨(r.val + m - i.val) % m, Nat.mod_lt _ hm⟩)) := by
    have h1 : sumFin m (fun i => sumFin m (fun j => a j * b ⟨(i.val + m - j.val) % m, Nat.mod_lt _ hm⟩) *
                                 c ⟨(r.val + m - i.val) % m, Nat.mod_lt _ hm⟩) =
              sumFin m (fun i => sumFin m (fun j => (a j * b ⟨(i.val + m - j.val) % m, Nat.mod_lt _ hm⟩) *
                                                    c ⟨(r.val + m - i.val) % m, Nat.mod_lt _ hm⟩)) := by
      apply sumFin_congr; intro i; rw [← sumFin_mul_right]
    rw [h1, sumFin_swap]
    apply sumFin_congr; intro j
    rw [← sumFin_mul_left]
    apply sumFin_congr; intro i
    exact Int.mul_assoc _ _ _
  rw [hL]
  apply sumFin_congr
  intro j
  congr 1
  rw [← sumFin_shift hm j.val (fun i => b ⟨(i.val + m - j.val) % m, Nat.mod_lt _ hm⟩ *
                                       c ⟨(r.val + m - i.val) % m, Nat.mod_lt _ hm⟩)]
  apply sumFin_congr
  intro k
  have hk := k.isLt
  have hj := j.isLt
  have hr := r.isLt
  have h1 : ((k.val + j.val) % m + m - j.val) % m = k.val := by
    by_cases hkj : k.val + j.val < m
    · rw [Nat.mod_eq_of_lt hkj]
      have : k.val + j.val + m - j.val = k.val + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
    · have hmod : (k.val + j.val) % m = k.val + j.val - m := by
        have hsum : k.val + j.val = (k.val + j.val - m) + m := by omega
        conv => lhs; rw [hsum]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      have : k.val + j.val - m + m - j.val = k.val := by omega
      rw [this, Nat.mod_eq_of_lt hk]
  have h2 : (r.val + m - (k.val + j.val) % m) % m = ((r.val + m - j.val) % m + m - k.val) % m := by
    have hL2 : (r.val + m - (k.val + j.val) % m) % m = (r.val + 2 * m - j.val - k.val) % m := by
      by_cases hkj : k.val + j.val < m
      · rw [Nat.mod_eq_of_lt hkj]
        have : r.val + 2 * m - j.val - k.val = (r.val + m - (k.val + j.val)) + m := by omega
        rw [this, Nat.add_mod_right]
      · have hmod : (k.val + j.val) % m = k.val + j.val - m := by
          have hsum : k.val + j.val = (k.val + j.val - m) + m := by omega
          conv => lhs; rw [hsum]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        congr 1; omega
    have hR2 : ((r.val + m - j.val) % m + m - k.val) % m = (r.val + 2 * m - j.val - k.val) % m := by
      by_cases hrg : j.val ≤ r.val
      · have hmod : (r.val + m - j.val) % m = r.val - j.val := by
          have : r.val + m - j.val = (r.val - j.val) + m := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        have : r.val + 2 * m - j.val - k.val = (r.val - j.val + m - k.val) + m := by omega
        rw [this, Nat.add_mod_right]
      · have hmod : (r.val + m - j.val) % m = r.val + m - j.val := Nat.mod_eq_of_lt (by omega)
        rw [hmod]
        congr 1; omega
    rw [hL2, hR2]
  have hf1 : (⟨((k.val + j.val) % m + m - j.val) % m, Nat.mod_lt _ hm⟩ : Fin m) = k := Fin.ext h1
  have hf2 : (⟨(r.val + m - (k.val + j.val) % m) % m, Nat.mod_lt _ hm⟩ : Fin m) =
             ⟨((r.val + m - j.val) % m + m - k.val) % m, Nat.mod_lt _ hm⟩ := Fin.ext h2
  rw [hf1, hf2]

theorem grRev_sumFin {m d : Nat} (hm : 0 < m) (f : Fin d → GR m) :
    grRev hm (grSumFin d f) = grSumFin d (fun i => grRev hm (f i)) := rfl

theorem grMul_sumFin_right {m d : Nat} (hm : 0 < m) (a : GR m) (f : Fin d → GR m) :
    grMul hm a (grSumFin d f) = grSumFin d (fun i => grMul hm a (f i)) := by
  funext r
  unfold grMul grSumFin
  have h1 : sumFin m (fun k => a k * sumFin d (fun i => f i ⟨(r.val + m - k.val) % m, Nat.mod_lt _ hm⟩)) =
            sumFin m (fun k => sumFin d (fun i => a k * f i ⟨(r.val + m - k.val) % m, Nat.mod_lt _ hm⟩)) := by
    apply sumFin_congr; intro k; rw [← sumFin_mul_left]
  rw [h1, sumFin_swap]

theorem grMul_sumFin_left {m d : Nat} (hm : 0 < m) (f : Fin d → GR m) (a : GR m) :
    grMul hm (grSumFin d f) a = grSumFin d (fun i => grMul hm (f i) a) := by
  rw [grMul_comm, grMul_sumFin_right]
  funext r; unfold grSumFin
  apply sumFin_congr; intro i; dsimp only; rw [grMul_comm]

theorem grSumFin_add {m d : Nat} (f g : Fin d → GR m) :
    grSumFin d (fun i => grAdd (f i) (g i)) = grAdd (grSumFin d f) (grSumFin d g) := by
  funext r; unfold grSumFin grAdd; exact sumFin_add d _ _

theorem grSumFin_swap {m a b : Nat} (f : Fin a → Fin b → GR m) :
    grSumFin a (fun i => grSumFin b (fun j => f i j)) =
    grSumFin b (fun j => grSumFin a (fun i => f i j)) := by
  funext r; unfold grSumFin; exact sumFin_swap a b _

theorem grSumFin_single {m d : Nat} (k : Fin d) (f : Fin d → GR m) :
    grSumFin d (fun i => if i = k then f i else grZero m) = f k := by
  funext r; unfold grSumFin grZero
  have h : sumFin d (fun i => (if i = k then f i else fun _ => 0) r) =
           sumFin d (fun i => if i = k then f i r else 0) := by
    apply sumFin_congr; intro i; split <;> rfl
  rw [h, sumFin_single k]

theorem grMatVec_id {d m : Nat} (hm : 0 < m) (v : GRVec d m) :
    grMatVec hm grMatId v = v := by
  funext i; unfold grMatVec grMatId
  have h : grSumFin d (fun j => grMul hm (if i = j then grUnit 0 else grZero m) (v j)) =
           grSumFin d (fun j => if j = i then v j else grZero m) := by
    funext r; unfold grSumFin
    apply sumFin_congr; intro j
    by_cases hij : j = i
    · subst hij; simp [grMul_unit_zero_left]
    · have hne : i ≠ j := fun hc => hij hc.symm
      simp [hij, hne, grMul_zero_left]
  rw [h, grSumFin_single i]

theorem grMatVec_mul {d m : Nat} (hm : 0 < m) (A B : GRMat d m) (v : GRVec d m) :
    grMatVec hm (grMatMul hm A B) v = grMatVec hm A (grMatVec hm B v) := by
  funext i; unfold grMatVec grMatMul
  have h1 : grSumFin d (fun k => grMul hm (grSumFin d (fun j => grMul hm (A i j) (B j k))) (v k)) =
            grSumFin d (fun k => grSumFin d (fun j => grMul hm (grMul hm (A i j) (B j k)) (v k))) := by
    funext r; unfold grSumFin
    apply sumFin_congr; intro k; exact congrFun (grMul_sumFin_left hm _ _) r
  rw [h1, grSumFin_swap]
  funext r; unfold grSumFin
  apply sumFin_congr; intro j
  have h2 : grSumFin d (fun k => grMul hm (grMul hm (A i j) (B j k)) (v k)) =
            grMul hm (A i j) (grSumFin d (fun k => grMul hm (B j k) (v k))) := by
    rw [grMul_sumFin_right]
    funext r'; unfold grSumFin
    apply sumFin_congr; intro k; exact congrFun (grMul_assoc hm _ _ _) r'
  exact congrFun h2 r

theorem grMatMul_assoc {d m : Nat} (hm : 0 < m) (A B C : GRMat d m) :
    grMatMul hm (grMatMul hm A B) C = grMatMul hm A (grMatMul hm B C) := by
  funext i l
  exact congrFun (grMatVec_mul hm A B (fun k => C k l)) i

theorem grMatMul_id_right {d m : Nat} (hm : 0 < m) (A : GRMat d m) :
    grMatMul hm A grMatId = A := by
  funext i k; unfold grMatMul grMatId
  have h : grSumFin d (fun j => grMul hm (A i j) (if j = k then grUnit 0 else grZero m)) =
           grSumFin d (fun j => if j = k then A i j else grZero m) := by
    funext r; unfold grSumFin
    apply sumFin_congr; intro j
    by_cases hjk : j = k
    · subst hjk; simp only [ite_true]; rw [grMul_comm, grMul_unit_zero_left]
    · simp only [hjk, ite_false]; rw [grMul_zero_right]
  rw [h, grSumFin_single k]

theorem grMatMul_id_left {d m : Nat} (hm : 0 < m) (A : GRMat d m) :
    grMatMul hm grMatId A = A := by
  funext i k
  exact congrFun (grMatVec_id hm (fun j => A j k)) i

theorem grMatPow_comm {d m : Nat} (hm : 0 < m) (A : GRMat d m) (k : Nat) :
    grMatMul hm A (grMatPow hm A k) = grMatMul hm (grMatPow hm A k) A := by
  induction k with
  | zero => simp [grMatPow, grMatMul_id_right, grMatMul_id_left]
  | succ k ih =>
    simp only [grMatPow]
    rw [grMatMul_assoc, ← ih]

theorem grMatId_isRevHermitian {d m : Nat} (hm : 0 < m) :
    IsRevHermitian hm (grMatId (d := d) (m := m)) := by
  intro i j
  unfold grMatId
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    rw [grRev_unit]
    funext r; unfold grUnit; simp only [Nat.zero_mod, Nat.sub_zero, Nat.mod_self]
    rfl
  · have hji : j ≠ i := fun hc => hij hc.symm
    simp [hij, hji, grRev_zero]

theorem grMatPow_isRevHermitian {d m : Nat} (hm : 0 < m) (H : GRMat d m)
    (hH : IsRevHermitian hm H) (k : Nat) :
    IsRevHermitian hm (grMatPow hm H k) := by
  induction k with
  | zero => exact grMatId_isRevHermitian hm
  | succ k ih =>
    intro i j
    simp only [grMatPow]
    conv => lhs; rw [grMatPow_comm hm H k]
    unfold grMatMul
    rw [grRev_sumFin]
    funext r; unfold grSumFin
    apply sumFin_congr; intro t
    have heq : grMul hm (grMatPow hm H k j t) (H t i) =
               grRev hm (grMul hm (H i t) (grMatPow hm H k t j)) := by
      rw [grRev_mul, ← hH i t, ← ih t j, grMul_comm]
    exact congrFun heq r

theorem grRev_quadForm {d m : Nat} (hm : 0 < m) (v : GRVec d m) (A : GRMat d m)
    (hA : IsRevHermitian hm A) :
    grRev hm (grQuadForm hm v A) = grQuadForm hm v A := by
  unfold grQuadForm
  rw [grRev_sumFin]
  have h1 : grSumFin d (fun i => grRev hm (grSumFin d (fun j => grMul hm (grRev hm (v i)) (grMul hm (A i j) (v j))))) =
            grSumFin d (fun i => grSumFin d (fun j => grMul hm (grRev hm (v j)) (grMul hm (A j i) (v i)))) := by
    funext r; unfold grSumFin
    apply sumFin_congr; intro i
    change grRev hm (grSumFin d (fun j => grMul hm (grRev hm (v i)) (grMul hm (A i j) (v j)))) r =
           grSumFin d (fun j => grMul hm (grRev hm (v j)) (grMul hm (A j i) (v i))) r
    rw [grRev_sumFin]
    unfold grSumFin
    apply sumFin_congr; intro j
    have hterm : grRev hm (grMul hm (grRev hm (v i)) (grMul hm (A i j) (v j))) =
                 grMul hm (grRev hm (v j)) (grMul hm (A j i) (v i)) := by
      rw [grRev_mul, grRev_involutive, grRev_mul, ← hA i j]
      rw [grMul_comm hm (A j i) (grRev hm (v j)), ← grMul_assoc,
          grMul_comm hm (v i) (grRev hm (v j)), grMul_assoc, grMul_comm hm (v i) (A j i)]
    exact congrFun hterm r
  rw [h1, grSumFin_swap]

/-- **REUSABLE MECHANISM I (General Involutive Row-0 Telescoping & Palindromy Theorem):**
    If `H` is `rev`-Hermitian over `Z[Z/mZ]`, `v 0 = e_0`, and row 0 of `H` satisfies
    `H 0 j = delta_{0,j} e_0 + rev(v j)`, then:
      1. `(H^(k+1) v)_0 = (H^k v)_0 + quadForm(v, H^k)` for all `k : Nat`,
      2. `rev((H^k v)_0) = (H^k v)_0` for all `k : Nat`. -/
theorem hermitian_row0_telescope_symm {d m : Nat} (hd : 0 < d) (hm : 0 < m)
    (H : GRMat d m) (v : GRVec d m)
    (hH : IsRevHermitian hm H)
    (hv0 : v ⟨0, hd⟩ = grUnit 0)
    (hrow0 : ∀ j : Fin d, H ⟨0, hd⟩ j =
      grAdd (if j = ⟨0, hd⟩ then grUnit 0 else grZero m) (grRev hm (v j))) :
    (∀ k : Nat,
      grMatVec hm (grMatPow hm H (k + 1)) v ⟨0, hd⟩ =
      grAdd (grMatVec hm (grMatPow hm H k) v ⟨0, hd⟩) (grQuadForm hm v (grMatPow hm H k))) ∧
    (∀ k : Nat,
      grRev hm (grMatVec hm (grMatPow hm H k) v ⟨0, hd⟩) =
      grMatVec hm (grMatPow hm H k) v ⟨0, hd⟩) := by
  have htele : ∀ k : Nat,
      grMatVec hm (grMatPow hm H (k + 1)) v ⟨0, hd⟩ =
      grAdd (grMatVec hm (grMatPow hm H k) v ⟨0, hd⟩) (grQuadForm hm v (grMatPow hm H k)) := by
    intro k
    simp only [grMatPow]
    rw [grMatVec_mul]
    unfold grMatVec
    have hsplit : grSumFin d (fun i => grMul hm (H ⟨0, hd⟩ i) (grSumFin d (fun j => grMul hm (grMatPow hm H k i j) (v j)))) =
                  grAdd
                    (grSumFin d (fun i => grMul hm (if i = ⟨0, hd⟩ then grUnit 0 else grZero m)
                                                   (grSumFin d (fun j => grMul hm (grMatPow hm H k i j) (v j)))))
                    (grSumFin d (fun i => grMul hm (grRev hm (v i))
                                                   (grSumFin d (fun j => grMul hm (grMatPow hm H k i j) (v j))))) := by
      rw [← grSumFin_add]
      funext r; unfold grSumFin
      apply sumFin_congr; intro i
      exact congrFun (by rw [hrow0 i, grMul_add_left]) r
    rw [hsplit]
    congr 1
    · have hsing : grSumFin d (fun i => grMul hm (if i = ⟨0, hd⟩ then grUnit 0 else grZero m)
                                                  (grSumFin d (fun j => grMul hm (grMatPow hm H k i j) (v j)))) =
                   grSumFin d (fun i => if i = ⟨0, hd⟩ then grSumFin d (fun j => grMul hm (grMatPow hm H k i j) (v j))
                                        else grZero m) := by
        funext r; unfold grSumFin
        apply sumFin_congr; intro i
        by_cases hi : i = ⟨0, hd⟩
        · subst hi; simp [grMul_unit_zero_left]
        · simp [hi, grMul_zero_left]
      rw [hsing, grSumFin_single ⟨0, hd⟩]
    · unfold grQuadForm
      funext r; unfold grSumFin
      apply sumFin_congr; intro i
      exact congrFun (grMul_sumFin_right hm _ _) r
  refine ⟨htele, ?_⟩
  intro k
  induction k with
  | zero =>
    simp only [grMatPow, grMatVec_id, hv0]
    rw [grRev_unit]
    funext r; unfold grUnit; simp only [Nat.zero_mod, Nat.sub_zero, Nat.mod_self]; rfl
  | succ k ih =>
    rw [htele k, grRev_add, ih, grRev_quadForm hm v (grMatPow hm H k) (grMatPow_isRevHermitian hm H hH k)]

-- ============================================================================
-- SECTION 1B: INSTANTIATION TO ALL-m MERSENNE BIT-WEIGHT CLASSES (2^m - 1)*n
-- ============================================================================

theorem two_pow_sub_one_pos {m : Nat} (hm : 0 < m) : 0 < 2 ^ m - 1 := by
  have : 2 ≤ 2 ^ m := by
    cases m with
    | zero => omega
    | succ m =>
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      rw [Nat.pow_succ]; omega
  omega

theorem mersenneH_isRevHermitian (m : Nat) (hm : 0 < m) :
    IsRevHermitian hm (mersenneH m) := by
  intro g gp
  unfold mersenneH
  by_cases hEq : g = gp
  · subst hEq
    simp only [ite_true]
    rw [grRev_add, grRev_unit]
    funext r; unfold grAdd grUnit; simp only [Nat.zero_mod, Nat.sub_zero, Nat.mod_self]; rfl
  · have hne : gp ≠ g := fun hc => hEq hc.symm
    simp only [hEq, hne, ite_false]
    rw [grRev_unit]
    have hD : 0 < 2 ^ m - 1 := two_pow_sub_one_pos hm
    have hg := g.isLt
    have hgp := gp.isLt
    let u := (g.val + (2 ^ m - 1) - gp.val) % (2 ^ m - 1)
    let w := (gp.val + (2 ^ m - 1) - g.val) % (2 ^ m - 1)
    have hcomp : w = 2 ^ m - 1 - u := by
      have hgne : g.val ≠ gp.val := fun hc => hEq (Fin.ext hc)
      by_cases hlt : gp.val < g.val
      · have hu : u = g.val - gp.val := by
          show (g.val + (2 ^ m - 1) - gp.val) % (2 ^ m - 1) = g.val - gp.val
          have : g.val + (2 ^ m - 1) - gp.val = (g.val - gp.val) + (2 ^ m - 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hw : w = gp.val + (2 ^ m - 1) - g.val := by
          show (gp.val + (2 ^ m - 1) - g.val) % (2 ^ m - 1) = gp.val + (2 ^ m - 1) - g.val
          exact Nat.mod_eq_of_lt (by omega)
        omega
      · have hgt : g.val < gp.val := by omega
        have hu : u = g.val + (2 ^ m - 1) - gp.val := by
          show (g.val + (2 ^ m - 1) - gp.val) % (2 ^ m - 1) = g.val + (2 ^ m - 1) - gp.val
          exact Nat.mod_eq_of_lt (by omega)
        have hw : w = gp.val - g.val := by
          show (gp.val + (2 ^ m - 1) - g.val) % (2 ^ m - 1) = gp.val - g.val
          have : gp.val + (2 ^ m - 1) - g.val = (gp.val - g.val) + (2 ^ m - 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    have hu_lt : u < 2 ^ m := by
      have : u < 2 ^ m - 1 := Nat.mod_lt _ hD
      omega
    have hpc := popcount_complement m u hu_lt
    rw [← hcomp] at hpc
    funext r; unfold grUnit
    have hmod_eq : popcount w % m = (m - popcount u % m) % m := by
      by_cases h0 : popcount u = 0
      · have hpw : popcount w = m := by omega
        simp [h0, hpw]
      · by_cases hm_eq : popcount u = m
        · have hpw : popcount w = 0 := by omega
          simp [hm_eq, hpw]
        · have hlt_u : popcount u < m := by omega
          have hpw : popcount w = m - popcount u := by omega
          rw [hpw, Nat.mod_eq_of_lt hlt_u]
    rw [hmod_eq]

theorem mersenneH_row0 (m : Nat) (hm : 0 < m) :
    ∀ j : Fin (2 ^ m - 1),
      mersenneH m ⟨0, two_pow_sub_one_pos hm⟩ j =
      grAdd (if j = ⟨0, two_pow_sub_one_pos hm⟩ then grUnit 0 else grZero m)
            (grRev hm (mersenneV0 m j)) := by
  intro j
  unfold mersenneH mersenneV0
  by_cases hj : j = ⟨0, two_pow_sub_one_pos hm⟩
  · subst hj
    simp only [ite_true, popcount_zero]
    rw [grRev_unit]
    funext r; unfold grAdd grUnit; simp only [Nat.zero_mod, Nat.sub_zero, Nat.mod_self]; rfl
  · have hne : (⟨0, two_pow_sub_one_pos hm⟩ : Fin (2 ^ m - 1)) ≠ j := fun hc => hj hc.symm
    simp only [hj, hne, ite_false]
    rw [grRev_unit]
    have hD : 0 < 2 ^ m - 1 := two_pow_sub_one_pos hm
    have hj_pos : 0 < j.val := Nat.pos_of_ne_zero (fun h0 => hj (Fin.ext h0))
    have hmod_j : (0 + (2 ^ m - 1) - j.val) % (2 ^ m - 1) = 2 ^ m - 1 - j.val := by
      have : 0 + (2 ^ m - 1) - j.val = 2 ^ m - 1 - j.val := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [hmod_j]
    have hpc := popcount_complement m j.val (by have := j.isLt; omega)
    funext r; unfold grAdd grZero grUnit
    simp only [Int.zero_add]
    have hmod_eq : popcount (2 ^ m - 1 - j.val) % m = (m - popcount j.val % m) % m := by
      by_cases h0 : popcount j.val = 0
      · have : popcount (2 ^ m - 1 - j.val) = m := by omega
        simp [h0, this]
      · by_cases hm_eq : popcount j.val = m
        · have : popcount (2 ^ m - 1 - j.val) = 0 := by omega
          simp [hm_eq, this]
        · have hlt : popcount j.val < m := by omega
          have hpw : popcount (2 ^ m - 1 - j.val) = m - popcount j.val := by omega
          rw [hpw, Nat.mod_eq_of_lt hlt]
    rw [hmod_eq]

/-- Helper for modular addition equivalence in `mersenneHist_eq_matPow`. -/
theorem mod_add_iff_sub {m A B r : Nat} (hm : 0 < m) (hr : r < m) :
    (A + B) % m = r % m ↔ A % m = ((r + m - B % m) % m) % m := by
  rw [Nat.mod_mod, Nat.mod_eq_of_lt hr, Nat.add_mod]
  have hA := Nat.mod_lt A hm
  have hB := Nat.mod_lt B hm
  constructor
  · intro heq
    by_cases hsum : A % m + B % m < m
    · rw [Nat.mod_eq_of_lt hsum] at heq
      have : r + m - B % m = A % m + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hA]
    · have hmod : (A % m + B % m) % m = A % m + B % m - m := by
        have hsum2 : A % m + B % m = (A % m + B % m - m) + m := by omega
        conv => lhs; rw [hsum2]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod] at heq
      have : r + m - B % m = A % m := by omega
      rw [this, Nat.mod_eq_of_lt hA]
  · intro heq
    by_cases hbr : B % m ≤ r
    · have hmod : (r + m - B % m) % m = r - B % m := by
        have : r + m - B % m = (r - B % m) + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod] at heq
      have : A % m + B % m = r := by omega
      rw [this, Nat.mod_eq_of_lt hr]
    · have hmod : (r + m - B % m) % m = r + m - B % m := Nat.mod_eq_of_lt (by omega)
      rw [hmod] at heq
      have : A % m + B % m = r + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hr]

/-- Exact Base-2^m Carry Compilation Theorem:
    For ALL `m >= 1`, `k >= 0`, carry `g < 2^m - 1`, and residue `r < m`,
    the histogram `countMod (2^(m*k)) m r (n ↦ popcount ((2^m - 1)*n + g))`
    equals `((mersenneH m)^k * mersenneV0 m)_g (r)`. -/
theorem mersenneHist_eq_matPow (m : Nat) (hm : 0 < m) :
    ∀ (k : Nat) (g : Fin (2 ^ m - 1)) (r : Fin m),
      (countMod (2 ^ (m * k)) m r.val (fun n => popcount ((2 ^ m - 1) * n + g.val)) : Int) =
      grMatVec hm (grMatPow hm (mersenneH m) k) (mersenneV0 m) g r := by
  intro k
  induction k with
  | zero =>
    intro g r
    simp only [Nat.mul_zero, Nat.pow_zero, grMatPow, grMatVec_id, mersenneV0, grUnit]
    unfold countMod countMod
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt r.isLt]
    by_cases h : popcount g.val % m = r.val
    · simp [h]
    · have h' : r.val ≠ popcount g.val % m := fun hc => h hc.symm
      simp [h, h']
  | succ k ih =>
    intro g r
    have hD : 0 < 2 ^ m - 1 := two_pow_sub_one_pos hm
    have hpow_split : 2 ^ (m * (k + 1)) = 2 ^ (m * k) * 2 ^ m := by
      rw [Nat.mul_succ, Nat.pow_add]
    rw [countMod_eq_sumRange, hpow_split, sumRange_mul_block]
    let V : GRVec (2 ^ m - 1) m := grMatVec hm (grMatPow hm (mersenneH m) k) (mersenneV0 m)
    let digitTerm (d : Nat) : Int :=
      if hd_lt : d < 2 ^ m then
        if hd : d ≤ g.val then
          V ⟨d, by have := g.isLt; omega⟩ ⟨(r.val + m - popcount (g.val - d) % m) % m, Nat.mod_lt _ hm⟩
        else
          V ⟨d - 1, by omega⟩ ⟨(r.val + m - popcount (2 ^ m - 1 - (d - 1 - g.val)) % m) % m, Nat.mod_lt _ hm⟩
      else 0
    have hdigit : ∀ d : Nat, d < 2 ^ m →
        sumRange (2 ^ (m * k))
          (fun q => if popcount ((2 ^ m - 1) * (q * 2 ^ m + d) + g.val) % m = r.val % m then 1 else 0) =
        digitTerm d := by
      intro d hd_lt
      simp only [digitTerm, hd_lt, dite_true]
      by_cases hd : d ≤ g.val
      · simp only [hd, dite_true]
        have hstep_arith : ∀ q : Nat,
            (2 ^ m - 1) * (q * 2 ^ m + d) + g.val =
            ((2 ^ m - 1) * q + d) * 2 ^ m + (g.val - d) := by
          intro q
          have hp1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
          have hmul : (2 ^ m - 1) * d + d = d * 2 ^ m := by
            have : (2 ^ m - 1) * d + 1 * d = 2 ^ m * d := by
              rw [← Nat.add_mul, Nat.sub_add_cancel hp1]
            rw [Nat.one_mul, Nat.mul_comm (2 ^ m) d] at this
            exact this
          have h1 : (2 ^ m - 1) * (q * 2 ^ m + d) = ((2 ^ m - 1) * q) * 2 ^ m + (2 ^ m - 1) * d := by
            rw [Nat.mul_add, Nat.mul_assoc]
          have h2 : ((2 ^ m - 1) * q + d) * 2 ^ m = ((2 ^ m - 1) * q) * 2 ^ m + d * 2 ^ m := by
            rw [Nat.add_mul]
          rw [h1, h2]; omega
        have hgd_lt : g.val - d < 2 ^ m := by have := g.isLt; omega
        have hrew : sumRange (2 ^ (m * k))
              (fun q => if popcount ((2 ^ m - 1) * (q * 2 ^ m + d) + g.val) % m = r.val % m then 1 else 0) =
            sumRange (2 ^ (m * k))
              (fun q => if popcount ((2 ^ m - 1) * q + d) % m =
                           ((r.val + m - popcount (g.val - d) % m) % m) % m then 1 else 0) := by
          apply sumRange_congr; intro q _
          rw [hstep_arith q, popcount_mul_pow2_add m _ _ hgd_lt]
          have hiff := mod_add_iff_sub (A := popcount ((2 ^ m - 1) * q + d))
                                       (B := popcount (g.val - d)) hm r.isLt
          by_cases h : (popcount ((2 ^ m - 1) * q + d) + popcount (g.val - d)) % m = r.val % m
          · have h2 := hiff.mp h; simp only [h, h2, ite_true]
          · have h2 : popcount ((2 ^ m - 1) * q + d) % m ≠ ((r.val + m - popcount (g.val - d) % m) % m) % m :=
              fun hc => h (hiff.mpr hc)
            simp only [h, h2, ite_false]
        rw [hrew, ← countMod_eq_sumRange]
        exact ih ⟨d, by have := g.isLt; omega⟩ ⟨(r.val + m - popcount (g.val - d) % m) % m, Nat.mod_lt _ hm⟩
      · simp only [hd, dite_false]
        have hstep_arith : ∀ q : Nat,
            (2 ^ m - 1) * (q * 2 ^ m + d) + g.val =
            ((2 ^ m - 1) * q + (d - 1)) * 2 ^ m + (2 ^ m - 1 - (d - 1 - g.val)) := by
          intro q
          have hp1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
          have h1 : (2 ^ m - 1) * (q * 2 ^ m + d) = ((2 ^ m - 1) * q) * 2 ^ m + (2 ^ m - 1) * d := by
            rw [Nat.mul_add, Nat.mul_assoc]
          have h2 : ((2 ^ m - 1) * q + (d - 1)) * 2 ^ m = ((2 ^ m - 1) * q) * 2 ^ m + (d - 1) * 2 ^ m := by
            rw [Nat.add_mul]
          have hd1 : d = (d - 1) + 1 := by omega
          have hmul : (2 ^ m - 1) * d + d = d * 2 ^ m := by
            have : (2 ^ m - 1) * d + 1 * d = 2 ^ m * d := by
              rw [← Nat.add_mul, Nat.sub_add_cancel hp1]
            rw [Nat.one_mul, Nat.mul_comm (2 ^ m) d] at this
            exact this
          have hmul2 : d * 2 ^ m = (d - 1) * 2 ^ m + 2 ^ m := by
            conv => lhs; rw [hd1, Nat.add_mul, Nat.one_mul]
          rw [h1, h2]; omega
        have hrem_lt : 2 ^ m - 1 - (d - 1 - g.val) < 2 ^ m := by omega
        have hrew : sumRange (2 ^ (m * k))
              (fun q => if popcount ((2 ^ m - 1) * (q * 2 ^ m + d) + g.val) % m = r.val % m then 1 else 0) =
            sumRange (2 ^ (m * k))
              (fun q => if popcount ((2 ^ m - 1) * q + (d - 1)) % m =
                           ((r.val + m - popcount (2 ^ m - 1 - (d - 1 - g.val)) % m) % m) % m then 1 else 0) := by
          apply sumRange_congr; intro q _
          rw [hstep_arith q, popcount_mul_pow2_add m _ _ hrem_lt]
          have hiff := mod_add_iff_sub (A := popcount ((2 ^ m - 1) * q + (d - 1)))
                                       (B := popcount (2 ^ m - 1 - (d - 1 - g.val))) hm r.isLt
          by_cases h : (popcount ((2 ^ m - 1) * q + (d - 1)) + popcount (2 ^ m - 1 - (d - 1 - g.val))) % m = r.val % m
          · have h2 := hiff.mp h; simp only [h, h2, ite_true]
          · have h2 : popcount ((2 ^ m - 1) * q + (d - 1)) % m ≠
                      ((r.val + m - popcount (2 ^ m - 1 - (d - 1 - g.val)) % m) % m) % m :=
              fun hc => h (hiff.mpr hc)
            simp only [h, h2, ite_false]
        rw [hrew, ← countMod_eq_sumRange]
        exact ih ⟨d - 1, by omega⟩ ⟨(r.val + m - popcount (2 ^ m - 1 - (d - 1 - g.val)) % m) % m, Nat.mod_lt _ hm⟩
    -- Rewrite both sides to a common 3-part sum: (gp < g) + (2 * V g r) + (g < gp)
    let leftTerm (gp : Nat) : Int :=
      if hgp : gp < 2 ^ m - 1 then
        V ⟨gp, hgp⟩ ⟨(r.val + m - popcount (g.val - gp) % m) % m, Nat.mod_lt _ hm⟩
      else 0
    let rightTerm (j : Nat) : Int :=
      if hgp : g.val + (j + 1) < 2 ^ m - 1 then
        V ⟨g.val + (j + 1), hgp⟩ ⟨(r.val + m - popcount (2 ^ m - 1 - (j + 1)) % m) % m, Nat.mod_lt _ hm⟩
      else 0
    have hLHS : sumRange (2 ^ m)
        (fun d => sumRange (2 ^ (m * k))
          (fun q => if popcount ((2 ^ m - 1) * (q * 2 ^ m + d) + g.val) % m = r.val % m then 1 else 0)) =
        sumRange g.val leftTerm + (V g r + V g r) + sumRange (2 ^ m - 2 - g.val) rightTerm := by
      have hsplit_len : 2 ^ m = (g.val + 1) + ((2 ^ m - 2 - g.val) + 1) := by
        have := g.isLt; omega
      rw [sumRange_congr hdigit]
      have hsplit_sum : sumRange (2 ^ m) digitTerm =
          sumRange (g.val + 1) digitTerm + sumRange ((2 ^ m - 2 - g.val) + 1) (fun j => digitTerm (g.val + 1 + j)) := by
        conv => lhs; rw [hsplit_len]
        exact sumRange_add (g.val + 1) ((2 ^ m - 2 - g.val) + 1) digitTerm
      rw [hsplit_sum]
      have hA : sumRange (g.val + 1) digitTerm =
          sumRange g.val leftTerm + V g r := by
        rw [sumRange]
        congr 1
        · apply sumRange_congr; intro d hd
          have h0 : d < 2 ^ m := by have := g.isLt; omega
          have h1 : d ≤ g.val := by omega
          have h2 : d < 2 ^ m - 1 := by have := g.isLt; omega
          simp only [digitTerm, leftTerm, h0, h1, h2, dite_true]
        · have h0 : g.val < 2 ^ m := by have := g.isLt; omega
          have hle : g.val ≤ g.val := Nat.le_refl _
          simp only [digitTerm, h0, hle, dite_true, Nat.sub_self, popcount_zero, Nat.zero_mod, Nat.sub_zero]
          congr 1
          exact Fin.ext (by dsimp only; rw [Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt])
      have hB : sumRange ((2 ^ m - 2 - g.val) + 1) (fun j => digitTerm (g.val + 1 + j)) =
          V g r + sumRange (2 ^ m - 2 - g.val) rightTerm := by
        rw [sumRange_succ_left]
        congr 1
        · have h0 : g.val + 1 + 0 < 2 ^ m := by have := g.isLt; omega
          have hnot : ¬ (g.val + 1 + 0 ≤ g.val) := by omega
          simp only [digitTerm, h0, hnot, dite_true, dite_false]
          have hpm : popcount (2 ^ m - 1) = m := by
            have h := popcount_complement m 0 (Nat.one_le_two_pow)
            simp [popcount_zero] at h; exact h
          have hsub1 : g.val + 1 + 0 - 1 = g.val := by omega
          have hsub2 : g.val + 1 + 0 - 1 - g.val = 0 := by omega
          have hfin1 : (⟨g.val + 1 + 0 - 1, by have := g.isLt; omega⟩ : Fin (2 ^ m - 1)) = g := Fin.ext hsub1
          have hfin2 : (⟨(r.val + m - popcount (2 ^ m - 1 - (g.val + 1 + 0 - 1 - g.val)) % m) % m, Nat.mod_lt _ hm⟩ : Fin m) = r := by
            apply Fin.ext; dsimp only
            rw [hsub2, Nat.sub_zero, hpm, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
          rw [hfin1, hfin2]
        · apply sumRange_congr; intro j hj
          have h0 : g.val + 1 + (j + 1) < 2 ^ m := by omega
          have hnot : ¬ (g.val + 1 + (j + 1) ≤ g.val) := by omega
          have hlt : g.val + (j + 1) < 2 ^ m - 1 := by omega
          simp only [digitTerm, h0, hnot, dite_false, rightTerm, hlt, dite_true]
          have hsub1 : g.val + 1 + (j + 1) - 1 = g.val + (j + 1) := by omega
          have hsub2 : g.val + 1 + (j + 1) - 1 - g.val = j + 1 := by omega
          congr 1
          · exact Fin.ext hsub1
          · apply Fin.ext; dsimp only; rw [hsub2]
      rw [hA, hB]; omega
    have hRHS : grMatVec hm (grMatPow hm (mersenneH m) (k + 1)) (mersenneV0 m) g r =
        sumRange g.val leftTerm + (V g r + V g r) + sumRange (2 ^ m - 2 - g.val) rightTerm := by
      simp only [grMatPow]
      rw [grMatVec_mul]
      change grMatVec hm (mersenneH m) V g r = _
      unfold grMatVec grSumFin sumFin
      have hEval : ∀ gp : Nat, (hgp : gp < 2 ^ m - 1) →
          grMul hm (mersenneH m g ⟨gp, hgp⟩) (V ⟨gp, hgp⟩) r =
          if gp = g.val then
            V ⟨gp, hgp⟩ r + V ⟨gp, hgp⟩ r
          else if gp < g.val then
            V ⟨gp, hgp⟩ ⟨(r.val + m - popcount (g.val - gp) % m) % m, Nat.mod_lt _ hm⟩
          else
            V ⟨gp, hgp⟩ ⟨(r.val + m - popcount (2 ^ m - 1 - (gp - g.val)) % m) % m, Nat.mod_lt _ hm⟩ := by
        intro gp hgp
        unfold mersenneH
        by_cases hEq : gp = g.val
        · simp only [hEq, ite_true]
          rw [grMul_add_left, grMul_unit_zero_left]
          rfl
        · have hfin : g ≠ ⟨gp, hgp⟩ := fun hc => hEq (congrArg Fin.val hc).symm
          simp only [hfin, hEq, ite_false]
          rw [grMul_unit_left]
          by_cases hlt : gp < g.val
          · simp only [hlt, ite_true]
            have hmod : (g.val + (2 ^ m - 1) - gp) % (2 ^ m - 1) = g.val - gp := by
              have : g.val + (2 ^ m - 1) - gp = (g.val - gp) + (2 ^ m - 1) := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [hmod]
          · simp only [hlt, ite_false]
            have hmod : (g.val + (2 ^ m - 1) - gp) % (2 ^ m - 1) = 2 ^ m - 1 - (gp - g.val) := by
              have : g.val + (2 ^ m - 1) - gp = 2 ^ m - 1 - (gp - g.val) := by omega
              rw [this, Nat.mod_eq_of_lt (by omega)]
            rw [hmod]
      have hsplit_len : 2 ^ m - 1 = g.val + ((2 ^ m - 2 - g.val) + 1) := by
        have := g.isLt; omega
      let fR : Nat → Int := fun gp =>
        if hgp : gp < 2 ^ m - 1 then grMul hm (mersenneH m g ⟨gp, hgp⟩) (V ⟨gp, hgp⟩) r else 0
      change sumRange (2 ^ m - 1) fR = _
      conv => lhs; rw [hsplit_len]
      rw [sumRange_add, sumRange_succ_left]
      have hP1 : sumRange g.val fR = sumRange g.val leftTerm := by
        apply sumRange_congr; intro gp hgp_lt
        have hgp : gp < 2 ^ m - 1 := by have := g.isLt; omega
        simp only [fR, leftTerm, hgp, dite_true]
        rw [hEval gp hgp]
        have hne : gp ≠ g.val := by omega
        simp [hne, hgp_lt]
      have hP2 : fR (g.val + 0) = V g r + V g r := by
        simp only [fR, Nat.add_zero, g.isLt, dite_true]
        rw [hEval g.val g.isLt]
        simp
      have hP3 : sumRange (2 ^ m - 2 - g.val) (fun j => fR (g.val + (j + 1))) =
                 sumRange (2 ^ m - 2 - g.val) rightTerm := by
        apply sumRange_congr; intro j hj
        have hgp : g.val + (j + 1) < 2 ^ m - 1 := by omega
        simp only [fR, rightTerm, hgp, dite_true]
        rw [hEval (g.val + (j + 1)) hgp]
        have hnotlt : ¬ (g.val + (j + 1) < g.val) := by omega
        have hsub : g.val + (j + 1) - g.val = j + 1 := by omega
        simp [hnotlt, hsub]
      rw [hP1, hP2, hP3]; omega
    rw [hLHS, hRHS]

/-- **THEOREM 1 (Universal All-m, All-k Mersenne Mod-m Popcount Palindromy):**
    For EVERY modulus `m ≥ 1`, EVERY block depth `k ≥ 0`, and EVERY residue `r < m`:
      `#{n < 2^(m*k) : s_2((2^m - 1) * n) ≡ r (mod m)}`
      `= #{n < 2^(m*k) : s_2((2^m - 1) * n) ≡ (m - r) % m (mod m)}`. -/
theorem mersenne_popcount_palindromy (m k r : Nat) (hm : 0 < m) (hr : r < m) :
    countMod (2 ^ (m * k)) m r (fun n => popcount ((2 ^ m - 1) * n)) =
    countMod (2 ^ (m * k)) m ((m - r) % m) (fun n => popcount ((2 ^ m - 1) * n)) := by
  have hD : 0 < 2 ^ m - 1 := two_pow_sub_one_pos hm
  have hv0 : mersenneV0 m ⟨0, hD⟩ = grUnit 0 := by
    unfold mersenneV0; simp [popcount_zero]
  have hsym := (hermitian_row0_telescope_symm hD hm (mersenneH m) (mersenneV0 m)
    (mersenneH_isRevHermitian m hm) hv0 (mersenneH_row0 m hm)).2 k
  have h1 := mersenneHist_eq_matPow m hm k ⟨0, hD⟩ ⟨r, hr⟩
  have h2 := mersenneHist_eq_matPow m hm k ⟨0, hD⟩ ⟨(m - r) % m, Nat.mod_lt _ hm⟩
  have h3 := congrFun hsym ⟨r, hr⟩
  unfold grRev at h3
  have hint : (countMod (2 ^ (m * k)) m r (fun n => popcount ((2 ^ m - 1) * n)) : Int) =
              (countMod (2 ^ (m * k)) m ((m - r) % m) (fun n => popcount ((2 ^ m - 1) * n)) : Int) := by
    simp only [Nat.add_zero] at h1 h2
    rw [h1, h2, ← h3]
  omega

-- ============================================================================
-- SECTION 1C: GENERAL ORBIT-LUMPING THEOREM & SHARP PHASE TRANSITION
-- ============================================================================

/-- **REUSABLE ORBIT-LUMPING LIFTING THEOREM (`orbit_lumping_sound`):**
    If `orb : Fin d → Fin O` lumps matrix `H` to `M` and vector `v` to `w`,
    then `(H^k v)_g = (M^k w)_{orb g}` for ALL `k : Nat` and ALL `g : Fin d`. -/
theorem orbit_lumping_sound {d O m : Nat} (hm : 0 < m)
    (orb : Fin d → Fin O)
    (H : GRMat d m) (M : GRMat O m)
    (v : GRVec d m) (w : GRVec O m)
    (hv : ∀ g : Fin d, v g = w (orb g))
    (hH : ∀ (g : Fin d) (j : Fin O),
      grSumFin d (fun gp => if orb gp = j then H g gp else grZero m) = M (orb g) j) :
    ∀ (k : Nat) (g : Fin d),
      grMatVec hm (grMatPow hm H k) v g = grMatVec hm (grMatPow hm M k) w (orb g) := by
  intro k
  induction k with
  | zero =>
    intro g
    simp only [grMatPow, grMatVec_id]
    exact hv g
  | succ k ih =>
    intro g
    simp only [grMatPow]
    rw [grMatVec_mul, grMatVec_mul]
    change grSumFin d (fun gp => grMul hm (H g gp) (grMatVec hm (grMatPow hm H k) v gp)) =
           grSumFin O (fun j => grMul hm (M (orb g) j) (grMatVec hm (grMatPow hm M k) w j))
    have hpart : ∀ gp : Fin d,
        grMul hm (H g gp) (grMatVec hm (grMatPow hm H k) v gp) =
        grSumFin O (fun j => if orb gp = j then grMul hm (H g gp) (grMatVec hm (grMatPow hm M k) w j) else grZero m) := by
      intro gp
      rw [ih gp]
      have h1 : grSumFin O (fun j => if orb gp = j then grMul hm (H g gp) (grMatVec hm (grMatPow hm M k) w j) else grZero m) =
                grSumFin O (fun j => if j = orb gp then grMul hm (H g gp) (grMatVec hm (grMatPow hm M k) w j) else grZero m) := by
        funext r; unfold grSumFin
        apply sumFin_congr; intro j
        by_cases h : j = orb gp
        · subst h; simp
        · have h' : orb gp ≠ j := fun hc => h hc.symm
          simp [h, h']
      rw [h1, grSumFin_single (orb gp)]
    have h1 : grSumFin d (fun gp => grMul hm (H g gp) (grMatVec hm (grMatPow hm H k) v gp)) =
              grSumFin d (fun gp => grSumFin O (fun j => if orb gp = j then grMul hm (H g gp) (grMatVec hm (grMatPow hm M k) w j) else grZero m)) := by
      funext r; unfold grSumFin
      apply sumFin_congr; intro gp; exact congrFun (hpart gp) r
    rw [h1, grSumFin_swap]
    funext r; unfold grSumFin
    apply sumFin_congr; intro j
    have h2 : grSumFin d (fun gp => if orb gp = j then grMul hm (H g gp) (grMatVec hm (grMatPow hm M k) w j) else grZero m) =
              grMul hm (grSumFin d (fun gp => if orb gp = j then H g gp else grZero m))
                       (grMatVec hm (grMatPow hm M k) w j) := by
      rw [grMul_sumFin_left]
      funext r'; unfold grSumFin
      apply sumFin_congr; intro gp
      by_cases h : orb gp = j
      · simp [h]
      · simp [h, grMul_zero_left]
    change grSumFin d (fun gp => if orb gp = j then grMul hm (H g gp) (grMatVec hm (grMatPow hm M k) w j) else grZero m) r =
           grMul hm (M (orb g) j) (grMatVec hm (grMatPow hm M k) w j) r
    rw [h2, hH g j]

-- --- Application 1b: Exact Mod-3 Mersenne Recurrence & Strict Positivity (m = 3, c = 7) ---

theorem orb3_v0_match : ∀ g : Fin 7, mersenneV0 3 g = v0Orb3 (orb3 g) := by
  intro g; funext r
  revert g r; decide

theorem orb3_H_match : ∀ (g : Fin 7) (j : Fin 3),
    grSumFin 7 (fun gp => if orb3 gp = j then mersenneH 3 g gp else grZero 3) =
    matOrb3 (orb3 g) j := by
  intro g j; funext r
  revert g j r; decide

theorem grMatVec_orb3_expand (W : GRVec 3 3) :
    let F := grMatVec (by decide : 0 < 3) matOrb3 W
    F ⟨0, by decide⟩ ⟨0, by decide⟩ = 2 * W ⟨0, by decide⟩ ⟨0, by decide⟩ + 3 * W ⟨1, by decide⟩ ⟨1, by decide⟩ + 3 * W ⟨2, by decide⟩ ⟨2, by decide⟩ ∧
    F ⟨0, by decide⟩ ⟨1, by decide⟩ = 2 * W ⟨0, by decide⟩ ⟨1, by decide⟩ + 3 * W ⟨1, by decide⟩ ⟨2, by decide⟩ + 3 * W ⟨2, by decide⟩ ⟨0, by decide⟩ ∧
    F ⟨0, by decide⟩ ⟨2, by decide⟩ = 2 * W ⟨0, by decide⟩ ⟨2, by decide⟩ + 3 * W ⟨1, by decide⟩ ⟨0, by decide⟩ + 3 * W ⟨2, by decide⟩ ⟨1, by decide⟩ ∧
    F ⟨1, by decide⟩ ⟨0, by decide⟩ = W ⟨0, by decide⟩ ⟨2, by decide⟩ +
      (2 * W ⟨1, by decide⟩ ⟨0, by decide⟩ + W ⟨1, by decide⟩ ⟨2, by decide⟩ + W ⟨1, by decide⟩ ⟨1, by decide⟩) +
      (W ⟨2, by decide⟩ ⟨2, by decide⟩ + 2 * W ⟨2, by decide⟩ ⟨1, by decide⟩) ∧
    F ⟨1, by decide⟩ ⟨1, by decide⟩ = W ⟨0, by decide⟩ ⟨0, by decide⟩ +
      (2 * W ⟨1, by decide⟩ ⟨1, by decide⟩ + W ⟨1, by decide⟩ ⟨0, by decide⟩ + W ⟨1, by decide⟩ ⟨2, by decide⟩) +
      (W ⟨2, by decide⟩ ⟨0, by decide⟩ + 2 * W ⟨2, by decide⟩ ⟨2, by decide⟩) ∧
    F ⟨1, by decide⟩ ⟨2, by decide⟩ = W ⟨0, by decide⟩ ⟨1, by decide⟩ +
      (2 * W ⟨1, by decide⟩ ⟨2, by decide⟩ + W ⟨1, by decide⟩ ⟨1, by decide⟩ + W ⟨1, by decide⟩ ⟨0, by decide⟩) +
      (W ⟨2, by decide⟩ ⟨1, by decide⟩ + 2 * W ⟨2, by decide⟩ ⟨0, by decide⟩) ∧
    F ⟨2, by decide⟩ ⟨0, by decide⟩ = W ⟨0, by decide⟩ ⟨1, by decide⟩ +
      (2 * W ⟨1, by decide⟩ ⟨2, by decide⟩ + W ⟨1, by decide⟩ ⟨1, by decide⟩) +
      (2 * W ⟨2, by decide⟩ ⟨0, by decide⟩ + W ⟨2, by decide⟩ ⟨2, by decide⟩ + W ⟨2, by decide⟩ ⟨1, by decide⟩) ∧
    F ⟨2, by decide⟩ ⟨1, by decide⟩ = W ⟨0, by decide⟩ ⟨2, by decide⟩ +
      (2 * W ⟨1, by decide⟩ ⟨0, by decide⟩ + W ⟨1, by decide⟩ ⟨2, by decide⟩) +
      (2 * W ⟨2, by decide⟩ ⟨1, by decide⟩ + W ⟨2, by decide⟩ ⟨0, by decide⟩ + W ⟨2, by decide⟩ ⟨2, by decide⟩) ∧
    F ⟨2, by decide⟩ ⟨2, by decide⟩ = W ⟨0, by decide⟩ ⟨0, by decide⟩ +
      (2 * W ⟨1, by decide⟩ ⟨1, by decide⟩ + W ⟨1, by decide⟩ ⟨0, by decide⟩) +
      (2 * W ⟨2, by decide⟩ ⟨2, by decide⟩ + W ⟨2, by decide⟩ ⟨1, by decide⟩ + W ⟨2, by decide⟩ ⟨0, by decide⟩) := by
  simp [grMatVec, grSumFin, grMul, sumFin, sumRange, matOrb3]

theorem orb3_iter_invariant (k : Nat) :
    let W := grMatVec (by decide : 0 < 3) (grMatPow (by decide : 0 < 3) matOrb3 k) v0Orb3
    let (A, u, v) := D3State k
    W ⟨0, by decide⟩ ⟨1, by decide⟩ = W ⟨0, by decide⟩ ⟨2, by decide⟩ ∧
    W ⟨2, by decide⟩ ⟨0, by decide⟩ = W ⟨1, by decide⟩ ⟨0, by decide⟩ ∧
    W ⟨2, by decide⟩ ⟨1, by decide⟩ = W ⟨1, by decide⟩ ⟨2, by decide⟩ ∧
    W ⟨2, by decide⟩ ⟨2, by decide⟩ = W ⟨1, by decide⟩ ⟨1, by decide⟩ ∧
    W ⟨0, by decide⟩ ⟨0, by decide⟩ - W ⟨0, by decide⟩ ⟨1, by decide⟩ = A ∧
    W ⟨1, by decide⟩ ⟨1, by decide⟩ - W ⟨1, by decide⟩ ⟨0, by decide⟩ = u ∧
    W ⟨1, by decide⟩ ⟨1, by decide⟩ - W ⟨1, by decide⟩ ⟨2, by decide⟩ = v := by
  induction k with
  | zero =>
    simp only [grMatPow, grMatVec_id, D3State]
    decide
  | succ k ih =>
    rcases hst : D3State k with ⟨A, u, v⟩
    rw [hst] at ih
    rcases ih with ⟨h0, h20, h21, h22, hA, hu, hv⟩
    dsimp only [D3State]
    rw [hst]
    let W := grMatVec (by decide : 0 < 3) (grMatPow (by decide : 0 < 3) matOrb3 k) v0Orb3
    have hstep : ∀ i r, grMatVec (by decide : 0 < 3) (grMatPow (by decide : 0 < 3) matOrb3 (k + 1)) v0Orb3 i r =
                        grMatVec (by decide : 0 < 3) matOrb3 W i r := by
      intro i r; simp only [grMatPow]; rw [grMatVec_mul]
    simp only [hstep]
    have hexp := grMatVec_orb3_expand W
    dsimp only at hexp
    rcases hexp with ⟨h00, h01, h02, h10, h11, h12, h20', h21', h22'⟩
    rw [h00, h01, h02, h10, h11, h12, h20', h21', h22']
    dsimp only [W] at *
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem mersenneMod3Excess_eq_D3State (k : Nat) :
    mersenneMod3Excess k = (D3State k).1 := by
  unfold mersenneMod3Excess
  have h0 := mersenneHist_eq_matPow 3 (by decide) k ⟨0, by decide⟩ ⟨0, by decide⟩
  have h1 := mersenneHist_eq_matPow 3 (by decide) k ⟨0, by decide⟩ ⟨1, by decide⟩
  simp only [Nat.add_zero] at h0 h1
  have hlump := orbit_lumping_sound (by decide : 0 < 3) orb3
    (mersenneH 3) matOrb3 (mersenneV0 3) v0Orb3
    orb3_v0_match orb3_H_match k ⟨0, by decide⟩
  have h0' : (countMod (2 ^ (3 * k)) 3 0 (fun n => popcount (7 * n)) : Int) =
             grMatVec (by decide : 0 < 3) (grMatPow (by decide : 0 < 3) matOrb3 k) v0Orb3 ⟨0, by decide⟩ ⟨0, by decide⟩ := by
    rw [h0, hlump]; rfl
  have h1' : (countMod (2 ^ (3 * k)) 3 1 (fun n => popcount (7 * n)) : Int) =
             grMatVec (by decide : 0 < 3) (grMatPow (by decide : 0 < 3) matOrb3 k) v0Orb3 ⟨0, by decide⟩ ⟨1, by decide⟩ := by
    rw [h1, hlump]; rfl
  rw [h0', h1']
  have hinv := orb3_iter_invariant k
  rcases hst : D3State k with ⟨A, u, v⟩
  rw [hst] at hinv
  exact hinv.2.2.2.2.1

/-- **THEOREM 1b (Exact 3-Term Recurrence & Exponential Positivity for Mod-3 Mersenne):**
    For ALL `k : Nat`:
      1. `D_3(k + 3) = 4 * D_3(k + 2) + 4 * D_3(k + 1) - D_3(k)`,
      2. `D_3(k) ≥ 4^k > 0`, hence class `0 (mod 3)` strictly dominates BOTH `1` and `2 (mod 3)`
         on every dyadic block `[0, 2^(3k))`. -/
theorem mersenne_mod3_recurrence (k : Nat) :
    mersenneMod3Excess (k + 3) =
    4 * mersenneMod3Excess (k + 2) + 4 * mersenneMod3Excess (k + 1) - mersenneMod3Excess k := by
  simp only [mersenneMod3Excess_eq_D3State, D3State]
  rcases D3State k with ⟨A, u, v⟩
  dsimp only
  omega

theorem mersenne_mod3_exponential_lower_bound (k : Nat) :
    ((4 ^ k : Nat) : Int) ≤ mersenneMod3Excess k := by
  rw [mersenneMod3Excess_eq_D3State]
  suffices h : ((4 ^ k : Nat) : Int) ≤ (D3State k).1 ∧ (D3State k).1 ≤ 3 * (D3State k).2.1 ∧
               (D3State k).2.1 ≤ (D3State k).2.2 by
    exact h.1
  induction k with
  | zero => simp [D3State]
  | succ k ih =>
    rcases hst : D3State k with ⟨A, u, v⟩
    simp only [hst] at ih
    rcases ih with ⟨h4, hAu, huv⟩
    simp only [D3State, hst]
    have hpow : ((4 ^ (k + 1) : Nat) : Int) = 4 * ((4 ^ k : Nat) : Int) := by
      rw [Nat.pow_succ, Int.natCast_mul]; omega
    have h4pos : (1 : Int) ≤ ((4 ^ k : Nat) : Int) := by
      have : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
      omega
    refine ⟨?_, ?_, ?_⟩ <;> omega

theorem mersenne_mod3_strict_dominance (k : Nat) :
    countMod (2 ^ (3 * k)) 3 1 (fun n => popcount (7 * n)) <
      countMod (2 ^ (3 * k)) 3 0 (fun n => popcount (7 * n)) ∧
    countMod (2 ^ (3 * k)) 3 2 (fun n => popcount (7 * n)) <
      countMod (2 ^ (3 * k)) 3 0 (fun n => popcount (7 * n)) := by
  have hlb := mersenne_mod3_exponential_lower_bound k
  have hpos : (1 : Int) ≤ ((4 ^ k : Nat) : Int) := by
    have : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
    omega
  have h1 : countMod (2 ^ (3 * k)) 3 1 (fun n => popcount (7 * n)) <
            countMod (2 ^ (3 * k)) 3 0 (fun n => popcount (7 * n)) := by
    unfold mersenneMod3Excess at hlb; omega
  have hsym := mersenne_popcount_palindromy 3 k 1 (by decide) (by decide)
  have h2 : countMod (2 ^ (3 * k)) 3 2 (fun n => popcount (7 * n)) =
            countMod (2 ^ (3 * k)) 3 1 (fun n => popcount (7 * n)) := hsym.symm
  exact ⟨h1, by omega⟩

-- --- Application 1c: Kernel-Checked Sharp Phase Transition at m = 6 (N = 2^72) ---

theorem v6Get_ofGR (f : GR 6) (r : Fin 6) : v6Get (v6OfGR f) r = f r := by
  rcases r with ⟨v, hv⟩
  match v, hv with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl

theorem v6Get_add (a b : Vec6) (r : Fin 6) : v6Get (v6Add a b) r = v6Get a r + v6Get b r := by
  rcases r with ⟨v, hv⟩
  match v, hv with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl

theorem v6Get_zero (r : Fin 6) : v6Get v6Zero r = 0 := by
  rcases r with ⟨v, hv⟩
  match v, hv with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl

theorem v6Get_mul (a b : Vec6) (r : Fin 6) :
    v6Get (v6Mul a b) r = grMul (by decide : 0 < 6) (v6Get a) (v6Get b) r := by
  rcases r with ⟨v, hv⟩
  match v, hv with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp [v6Mul, v6Get, grMul, sumFin, sumRange]

theorem orb6_v0_match : ∀ g : Fin 63, mersenneV0 6 g = v0Orb6 (orb6 g) := by
  intro g; funext r; revert g r; decide

theorem sumFin_rot6 (F : Fin 63 → Int) :
    sumFin 63 (fun x => F (rot6 x)) = sumFin 63 F := by
  unfold sumFin
  let G1 : Nat → Int := fun i => if h : i < 63 then F (rot6 ⟨i, h⟩) else 0
  let G2 : Nat → Int := fun i => if h : i < 63 then F ⟨i, h⟩ else 0
  let Ev : Nat → Int := fun y => if h : 2 * y < 63 then F ⟨2 * y, h⟩ else 0
  let Od : Nat → Int := fun y => if h : 2 * y + 1 < 63 then F ⟨2 * y + 1, h⟩ else 0
  change sumRange 63 G1 = sumRange 63 G2
  have hL : sumRange 63 G1 = sumRange 32 Ev + sumRange 31 Od := by
    have h63 : (63 : Nat) = 32 + 31 := rfl
    rw [h63, sumRange_add]
    congr 1
  have hR : sumRange 63 G2 = sumRange 32 Ev + sumRange 31 Od := by
    have h63 : (63 : Nat) = 2 * 31 + 1 := rfl
    rw [h63, sumRange_two_mul_add_one]
  rw [hL, hR]

theorem rot6_inj : ∀ a b : Fin 63, rot6 a = rot6 b → a = b := by decide
theorem orb6_rot6 : ∀ g : Fin 63, orb6 (rot6 g) = orb6 g := by decide
theorem popcount_rot6_diff : ∀ g gp : Fin 63,
    popcount (((rot6 g).val + 63 - (rot6 gp).val) % 63) =
    popcount ((g.val + 63 - gp.val) % 63) := by decide

theorem mersenneH6_rot6 (g gp : Fin 63) :
    mersenneH 6 (rot6 g) (rot6 gp) = mersenneH 6 g gp := by
  unfold mersenneH
  by_cases h : g = gp
  · subst h; simp
  · have hrot : rot6 g ≠ rot6 gp := fun hc => h (rot6_inj g gp hc)
    simp only [h, hrot, ite_false]
    have hp := popcount_rot6_diff g gp
    rw [hp]

theorem grSumFin_orb6_rot6 (g : Fin 63) (j : Fin 13) :
    grSumFin 63 (fun gp => if orb6 gp = j then mersenneH 6 (rot6 g) gp else grZero 6) =
    grSumFin 63 (fun gp => if orb6 gp = j then mersenneH 6 g gp else grZero 6) := by
  funext r
  unfold grSumFin
  rw [← sumFin_rot6]
  apply sumFin_congr; intro gp
  dsimp only
  rw [orb6_rot6, mersenneH6_rot6]

theorem grSumFin_orb6_rot6Iter (t : Nat) (g : Fin 63) (j : Fin 13) :
    grSumFin 63 (fun gp => if orb6 gp = j then mersenneH 6 (rot6Iter t g) gp else grZero 6) =
    grSumFin 63 (fun gp => if orb6 gp = j then mersenneH 6 g gp else grZero 6) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [rot6Iter]; rw [grSumFin_orb6_rot6, ih]

theorem orb6_reaches : ∀ g : Fin 63, ∃ t : Fin 6, rot6Iter t.val (orb6RepFin (orb6 g)) = g := by
  decide

theorem v6Get_mersenneH6Vec (g gp : Fin 63) (r : Fin 6) :
    v6Get (mersenneH6Vec g gp) r = mersenneH 6 g gp r := by
  unfold mersenneH6Vec mersenneH
  by_cases h : g = gp
  · simp only [h, ite_true]
    rcases r with ⟨v, hv⟩
    match v, hv with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl
  · simp only [h, ite_false]
    unfold v6Unit grUnit
    have hlt : popcount ((g.val + 63 - gp.val) % 63) % 6 < 6 := Nat.mod_lt _ (by decide)
    generalize popcount ((g.val + 63 - gp.val) % 63) % 6 = s at hlt ⊢
    rcases r with ⟨v, hv⟩
    match s, hlt, v, hv with
    | 0, _, 0, _ | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _ | 0, _, 4, _ | 0, _, 5, _
    | 1, _, 0, _ | 1, _, 1, _ | 1, _, 2, _ | 1, _, 3, _ | 1, _, 4, _ | 1, _, 5, _
    | 2, _, 0, _ | 2, _, 1, _ | 2, _, 2, _ | 2, _, 3, _ | 2, _, 4, _ | 2, _, 5, _
    | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 3, _ | 3, _, 4, _ | 3, _, 5, _
    | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 4, _, 4, _ | 4, _, 5, _
    | 5, _, 0, _ | 5, _, 1, _ | 5, _, 2, _ | 5, _, 3, _ | 5, _, 4, _ | 5, _, 5, _ => rfl

theorem orb6RepSum_eq_orb6Entry : ∀ i j : Fin 13, orb6RepSum i j = orb6Entry i j := by
  decide

theorem foldl_v6Add_cond_get {α : Type} (l : List α) (p : α → Bool) (f : α → Vec6) (init : Vec6) (r : Fin 6) :
    v6Get (l.foldl (fun acc x => if p x then v6Add acc (f x) else acc) init) r =
    v6Get init r + (l.map (fun x => if p x then v6Get (f x) r else 0)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    cases hpa : p a
    · simp only [Bool.false_eq_true, ite_false, ih]; omega
    · simp only [ite_true, ih, v6Get_add]; omega

theorem sum_finRange_eq_sumFin {d : Nat} (f : Fin d → Int) :
    ((List.finRange d).map f).sum = sumFin d f := by
  unfold sumFin
  have aux : ∀ n, n ≤ d →
      ((List.range n).map (fun i => if h : i < d then f ⟨i, h⟩ else 0)).sum =
      sumRange n (fun i => if h : i < d then f ⟨i, h⟩ else 0) := by
    intro n hn
    induction n with
    | zero => simp [sumRange]
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
          sumRange, ih (by omega)]
  rw [← aux d (Nat.le_refl d)]
  have hfr : (List.finRange d).map f = (List.range d).map (fun i => if h : i < d then f ⟨i, h⟩ else 0) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
      have hi : i < d := by simpa using h2
      simp [hi]
  rw [hfr]

theorem orb6_H_match : ∀ (g : Fin 63) (j : Fin 13),
    grSumFin 63 (fun gp => if orb6 gp = j then mersenneH 6 g gp else grZero 6) =
    matOrb6 (orb6 g) j := by
  intro g j
  rcases orb6_reaches g with ⟨t, ht⟩
  conv => lhs; rw [← ht]
  rw [grSumFin_orb6_rot6Iter]
  have hrep := orb6RepSum_eq_orb6Entry (orb6 g) j
  funext r
  unfold matOrb6
  rw [← hrep]
  unfold orb6RepSum
  have hcond : (fun acc gp => if orb6 gp = j then v6Add acc (mersenneH6Vec (orb6RepFin (orb6 g)) gp) else acc) =
               (fun acc gp => if (orb6 gp == j) then v6Add acc (mersenneH6Vec (orb6RepFin (orb6 g)) gp) else acc) := by
    funext acc gp; simp [beq_iff_eq]
  rw [hcond, foldl_v6Add_cond_get, v6Get_zero, Int.zero_add, sum_finRange_eq_sumFin]
  unfold grSumFin
  apply sumFin_congr; intro gp
  by_cases h : orb6 gp = j
  · simp [h, v6Get_mersenneH6Vec]
  · simp [h, grZero]

theorem foldl_v6Add_get {α : Type} (l : List α) (f : α → Vec6) (init : Vec6) (r : Fin 6) :
    v6Get (l.foldl (fun acc j => v6Add acc (f j)) init) r =
    v6Get init r + (l.map (fun j => v6Get (f j) r)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, v6Get_add]
    omega

theorem getD_map_finRange {α : Type} (d : Nat) (f : Fin d → α) (defv : α) (i : Fin d) :
    ((List.finRange d).map f).getD i.val defv = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [i.isLt])]
  simp

theorem iterOrb6List_correct (k : Nat) (i : Fin 13) (r : Fin 6) :
    v6Get ((iterOrb6List k).getD i.val v6Zero) r =
    grMatVec (by decide : 0 < 6) (grMatPow (by decide : 0 < 6) matOrb6 k) v0Orb6 i r := by
  induction k generalizing i r with
  | zero =>
    unfold iterOrb6List
    rw [getD_map_finRange, v6Get_ofGR]
    simp [grMatPow, grMatVec_id]
  | succ k ih =>
    unfold iterOrb6List
    dsimp only
    rw [getD_map_finRange, foldl_v6Add_get, v6Get_zero, Int.zero_add, sum_finRange_eq_sumFin]
    simp only [grMatPow]
    rw [grMatVec_mul]
    unfold grMatVec grSumFin
    apply sumFin_congr; intro j
    rw [v6Get_mul]
    have heq2 : v6Get ((iterOrb6List k).getD j.val v6Zero) =
                grMatVec (by decide : 0 < 6) (grMatPow (by decide : 0 < 6) matOrb6 k) v0Orb6 j := by
      funext r'; exact ih j r'
    rw [heq2]; rfl

set_option maxRecDepth 4096 in
/-- **THEOREM 1c (Kernel-Checked Sharp Phase Transition at m = 6, N = 2^72):**
    Although `c_0(2^(6k)) > c_r(2^(6k))` for all `1 ≤ k ≤ 11` (up to `2^66 ≈ 7.38 × 10^19`),
    at `k = 12` (`N = 2^72 = 4,722,366,482,869,645,213,696`), Mod-6 Mersenne 0-dominance
    SHARPLY BREAKS with exact deficit `-4,543,260,596,431,345`. -/
theorem mersenne_mod6_dominance_breaks_at_2_pow_72 :
    (countMod (2 ^ (6 * 12)) 6 0 (fun n => popcount (63 * n)) : Int) -
    (countMod (2 ^ (6 * 12)) 6 2 (fun n => popcount (63 * n)) : Int) =
    -4543260596431345 ∧
    countMod (2 ^ (6 * 12)) 6 0 (fun n => popcount (63 * n)) <
    countMod (2 ^ (6 * 12)) 6 2 (fun n => popcount (63 * n)) := by
  have h0 := mersenneHist_eq_matPow 6 (by decide) 12 ⟨0, by decide⟩ ⟨0, by decide⟩
  have h2 := mersenneHist_eq_matPow 6 (by decide) 12 ⟨0, by decide⟩ ⟨2, by decide⟩
  simp only [Nat.add_zero] at h0 h2
  have hlump := orbit_lumping_sound (by decide : 0 < 6) orb6
    (mersenneH 6) matOrb6 (mersenneV0 6) v0Orb6
    orb6_v0_match orb6_H_match 12 ⟨0, by decide⟩
  have heval : v6Get ((iterOrb6List 12).getD 0 v6Zero) ⟨0, by decide⟩ -
               v6Get ((iterOrb6List 12).getD 0 v6Zero) ⟨2, by decide⟩ = -4543260596431345 := by
    decide
  rw [iterOrb6List_correct 12 ⟨0, by decide⟩ ⟨0, by decide⟩,
      iterOrb6List_correct 12 ⟨0, by decide⟩ ⟨2, by decide⟩] at heval
  have hc0 : (countMod (2 ^ (6 * 12)) 6 0 (fun n => popcount (63 * n)) : Int) =
             grMatVec (by decide : 0 < 6) (grMatPow (by decide : 0 < 6) matOrb6 12) v0Orb6 ⟨0, by decide⟩ ⟨0, by decide⟩ := by
    rw [h0, hlump]; rfl
  have hc2 : (countMod (2 ^ (6 * 12)) 6 2 (fun n => popcount (63 * n)) : Int) =
             grMatVec (by decide : 0 < 6) (grMatPow (by decide : 0 < 6) matOrb6 12) v0Orb6 ⟨0, by decide⟩ ⟨2, by decide⟩ := by
    rw [h2, hlump]; rfl
  rw [hc0, hc2]
  exact ⟨heval, by omega⟩

-- Engine I Sharpness & Non-Triviality Witnesses (kernel-checked!)

theorem mersenne_palindromy_sharp_exponent :
    countMod (2 ^ 4) 3 1 (fun n => popcount (7 * n)) = 2 ∧
    countMod (2 ^ 4) 3 2 (fun n => popcount (7 * n)) = 1 ∧
    countMod (2 ^ 4) 3 1 (fun n => popcount (7 * n)) ≠
    countMod (2 ^ 4) 3 2 (fun n => popcount (7 * n)) := by
  decide

theorem mersenne_palindromy_sharp_multiplier :
    countMod (2 ^ 3) 3 1 (fun n => popcount (5 * n)) = 2 ∧
    countMod (2 ^ 3) 3 2 (fun n => popcount (5 * n)) = 3 ∧
    countMod (2 ^ 3) 3 1 (fun n => popcount (5 * n)) ≠
    countMod (2 ^ 3) 3 2 (fun n => popcount (5 * n)) := by
  decide

theorem mersenne_palindromy_naive_involutions_fail :
    popcount (7 * 11) % 3 = 1 ∧ popcount (7 * (64 - 11)) % 3 = 0 ∧
    popcount (7 * 13) % 3 = 2 ∧ popcount (7 * (63 - 13)) % 3 = 0 := by
  decide

-- ============================================================================
-- SECTION 2: ENGINE II — PURE-DATA 2-WINDOW BIT-SPLITTING CONE ENGINE
-- ============================================================================

theorem ParityTransducer.evalFuel_eq {d : Nat} (tr : ParityTransducer d)
    (f1 f2 n : Nat) (g : Fin d) (h1 : n ≤ f1) (h2 : n ≤ f2) :
    tr.evalFuel f1 g n = tr.evalFuel f2 g n := by
  induction f1 generalizing f2 n g with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    cases f2 <;> simp [ParityTransducer.evalFuel]
  | succ f1 ih =>
    cases f2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; simp [ParityTransducer.evalFuel]
    | succ f2 =>
      simp only [ParityTransducer.evalFuel]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ite_false]
        congr 1
        exact ih f2 (n / 2) (tr.nxt g (n % 2 == 1)) (by omega) (by omega)

theorem ParityTransducer.eval_zero {d : Nat} (tr : ParityTransducer d) (g : Fin d) :
    tr.eval g 0 = tr.base g := rfl

theorem ParityTransducer.eval_step {d : Nat} (tr : ParityTransducer d) (g : Fin d) (n : Nat) (hn : n ≠ 0) :
    tr.eval g n = signBool (tr.outBit g (n % 2 == 1)) * tr.eval (tr.nxt g (n % 2 == 1)) (n / 2) := by
  unfold ParityTransducer.eval
  cases n with
  | zero => exact absurd rfl hn
  | succ k =>
    simp only [ParityTransducer.evalFuel, Nat.succ_ne_zero, ite_false]
    congr 1
    exact tr.evalFuel_eq k ((k + 1) / 2) ((k + 1) / 2) _ (by omega) (Nat.le_refl _)

theorem ParityTransducer.eval_two_mul {d : Nat} (tr : ParityTransducer d)
    (hc : tr.isConsistent = true) (g : Fin d) (n : Nat) :
    tr.eval g (2 * n) = signBool (tr.outBit g false) * tr.eval (tr.nxt g false) n := by
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.mul_zero, ParityTransducer.eval_zero]
    unfold ParityTransducer.isConsistent at hc
    rw [List.all_eq_true] at hc
    have hg := hc g (List.mem_finRange g)
    simpa [beq_iff_eq] using hg
  · rw [tr.eval_step g (2 * n) (by omega)]
    have hmod : ((2 * n) % 2 == 1) = false := by
      have : (2 * n) % 2 = 0 := by omega
      simp [this]
    have hdiv : (2 * n) / 2 = n := by omega
    rw [hmod, hdiv]

theorem ParityTransducer.eval_two_mul_add_one {d : Nat} (tr : ParityTransducer d)
    (g : Fin d) (n : Nat) :
    tr.eval g (2 * n + 1) = signBool (tr.outBit g true) * tr.eval (tr.nxt g true) n := by
  rw [tr.eval_step g (2 * n + 1) (by omega)]
  have hmod : ((2 * n + 1) % 2 == 1) = true := by
    have : (2 * n + 1) % 2 = 1 := by omega
    simp [this]
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [hmod, hdiv]

theorem sumFin_LMat {d : Nat} (tr : ParityTransducer d) (b : Bool) (i : Fin d) (v : Fin d → Int) :
    sumFin d (fun j => LMat tr b i j * v j) = signBool (tr.outBit i b) * v (tr.nxt i b) := by
  have h : sumFin d (fun j => LMat tr b i j * v j) =
           sumFin d (fun j => if j = tr.nxt i b then signBool (tr.outBit i b) * v j else 0) := by
    apply sumFin_congr; intro j
    unfold LMat
    by_cases heq : j = tr.nxt i b
    · subst heq; simp
    · have hne : tr.nxt i b ≠ j := fun hc => heq hc.symm
      simp [heq, hne]
  rw [h, sumFin_single (tr.nxt i b)]

theorem sumFin_two_mul_split {d : Nat} (f : Fin (2 * d) → Int) :
    sumFin (2 * d) f =
    sumFin d (fun j => f ⟨j.val, by omega⟩) +
    sumFin d (fun j => f ⟨d + j.val, by omega⟩) := by
  unfold sumFin
  let g : Nat → Int := fun i => if h : i < 2 * d then f ⟨i, h⟩ else 0
  change sumRange (2 * d) g = _
  have h2 : 2 * d = d + d := by omega
  conv => lhs; rw [h2]
  rw [sumRange_add]
  congr 1
  · apply sumRange_congr; intro i hi
    have hi2 : i < 2 * d := by omega
    simp [g, hi, hi2]
  · apply sumRange_congr; intro i hi
    have hi2 : d + i < 2 * d := by omega
    simp [g, hi, hi2]

theorem prefixSum_two_mul {d : Nat} (tr : ParityTransducer d) (hc : tr.isConsistent = true)
    (g : Fin d) (N : Nat) :
    prefixSum tr g (2 * N) =
    signBool (tr.outBit g false) * prefixSum tr (tr.nxt g false) N +
    signBool (tr.outBit g true) * prefixSum tr (tr.nxt g true) N := by
  unfold prefixSum
  rw [sumRange_two_mul]
  congr 1
  · rw [← sumRange_mul_left]
    apply sumRange_congr; intro k _; exact tr.eval_two_mul hc g k
  · rw [← sumRange_mul_left]
    apply sumRange_congr; intro k _; exact tr.eval_two_mul_add_one g k

theorem prefixSum_two_mul_add_one {d : Nat} (tr : ParityTransducer d) (hc : tr.isConsistent = true)
    (g : Fin d) (N : Nat) :
    prefixSum tr g (2 * N + 1) =
    signBool (tr.outBit g false) * prefixSum tr (tr.nxt g false) (N + 1) +
    signBool (tr.outBit g true) * prefixSum tr (tr.nxt g true) N := by
  unfold prefixSum
  rw [sumRange_two_mul_add_one]
  congr 1
  · rw [← sumRange_mul_left]
    apply sumRange_congr; intro k _; exact tr.eval_two_mul hc g k
  · rw [← sumRange_mul_left]
    apply sumRange_congr; intro k _; exact tr.eval_two_mul_add_one g k

/-- **GENERAL 2-WINDOW BIT-SPLITTING THEOREM (Even & Odd Steps):**
    For ANY consistent finite-state LSB parity transducer and ALL `N : Nat`,
    `W(2*N) = T_0 * W(N)` and `W(2*N + 1) = T_1 * W(N)`. -/
theorem windowVec_two_mul {d : Nat} (tr : ParityTransducer d) (hc : tr.isConsistent = true) (N : Nat) :
    windowVec tr (2 * N) = matVecInt (T0Mat tr) (windowVec tr N) := by
  funext i
  unfold matVecInt
  rw [sumFin_two_mul_split]
  by_cases hi : i.val < d
  · unfold windowVec
    simp only [hi, dite_true]
    rw [prefixSum_two_mul tr hc ⟨i.val, hi⟩ N]
    have h1 : sumFin d (fun j => T0Mat tr i ⟨j.val, by omega⟩ * (if h : j.val < d then prefixSum tr ⟨j.val, h⟩ N else prefixSum tr ⟨j.val - d, by omega⟩ (N + 1))) =
              sumFin d (fun j => LMat tr false ⟨i.val, hi⟩ j * prefixSum tr j N) +
              sumFin d (fun j => LMat tr true ⟨i.val, hi⟩ j * prefixSum tr j N) := by
      rw [← sumFin_add]
      apply sumFin_congr; intro j
      unfold T0Mat
      simp only [hi, j.isLt, dite_true, Int.add_mul]
    have h2 : sumFin d (fun j => T0Mat tr i ⟨d + j.val, by omega⟩ * (if h : d + j.val < d then prefixSum tr ⟨d + j.val, h⟩ N else prefixSum tr ⟨d + j.val - d, by omega⟩ (N + 1))) = 0 := by
      rw [← sumFin_zero d]
      apply sumFin_congr; intro j
      unfold T0Mat
      have hnot : ¬ (d + j.val < d) := by omega
      simp [hi, hnot]
    rw [h1, h2, sumFin_LMat, sumFin_LMat, Int.add_zero]
  · unfold windowVec
    simp only [hi, dite_false]
    rw [prefixSum_two_mul_add_one tr hc ⟨i.val - d, by omega⟩ N]
    have h1 : sumFin d (fun j => T0Mat tr i ⟨j.val, by omega⟩ * (if h : j.val < d then prefixSum tr ⟨j.val, h⟩ N else prefixSum tr ⟨j.val - d, by omega⟩ (N + 1))) =
              sumFin d (fun j => LMat tr true ⟨i.val - d, by omega⟩ j * prefixSum tr j N) := by
      apply sumFin_congr; intro j
      unfold T0Mat
      simp [hi, j.isLt]
    have h2 : sumFin d (fun j => T0Mat tr i ⟨d + j.val, by omega⟩ * (if h : d + j.val < d then prefixSum tr ⟨d + j.val, h⟩ N else prefixSum tr ⟨d + j.val - d, by omega⟩ (N + 1))) =
              sumFin d (fun j => LMat tr false ⟨i.val - d, by omega⟩ j * prefixSum tr j (N + 1)) := by
      apply sumFin_congr; intro j
      unfold T0Mat
      have hnot : ¬ (d + j.val < d) := by omega
      simp only [hi, hnot, dite_false]
      have hfin : (⟨d + j.val - d, by omega⟩ : Fin d) = j := Fin.ext (by dsimp only; omega)
      rw [hfin]
    rw [h1, h2, sumFin_LMat, sumFin_LMat, Int.add_comm]

theorem windowVec_two_mul_add_one {d : Nat} (tr : ParityTransducer d) (hc : tr.isConsistent = true) (N : Nat) :
    windowVec tr (2 * N + 1) = matVecInt (T1Mat tr) (windowVec tr N) := by
  funext i
  unfold matVecInt
  rw [sumFin_two_mul_split]
  by_cases hi : i.val < d
  · unfold windowVec
    simp only [hi, dite_true]
    rw [prefixSum_two_mul_add_one tr hc ⟨i.val, hi⟩ N]
    have h1 : sumFin d (fun j => T1Mat tr i ⟨j.val, by omega⟩ * (if h : j.val < d then prefixSum tr ⟨j.val, h⟩ N else prefixSum tr ⟨j.val - d, by omega⟩ (N + 1))) =
              sumFin d (fun j => LMat tr true ⟨i.val, hi⟩ j * prefixSum tr j N) := by
      apply sumFin_congr; intro j
      unfold T1Mat
      simp [hi, j.isLt]
    have h2 : sumFin d (fun j => T1Mat tr i ⟨d + j.val, by omega⟩ * (if h : d + j.val < d then prefixSum tr ⟨d + j.val, h⟩ N else prefixSum tr ⟨d + j.val - d, by omega⟩ (N + 1))) =
              sumFin d (fun j => LMat tr false ⟨i.val, hi⟩ j * prefixSum tr j (N + 1)) := by
      apply sumFin_congr; intro j
      unfold T1Mat
      have hnot : ¬ (d + j.val < d) := by omega
      simp only [hi, hnot, dite_true, dite_false]
      have hfin : (⟨d + j.val - d, by omega⟩ : Fin d) = j := Fin.ext (by dsimp only; omega)
      rw [hfin]
    rw [h1, h2, sumFin_LMat, sumFin_LMat, Int.add_comm]
  · unfold windowVec
    simp only [hi, dite_false]
    have h2N2 : 2 * N + 1 + 1 = 2 * (N + 1) := by omega
    rw [h2N2, prefixSum_two_mul tr hc ⟨i.val - d, by omega⟩ (N + 1)]
    have h1 : sumFin d (fun j => T1Mat tr i ⟨j.val, by omega⟩ * (if h : j.val < d then prefixSum tr ⟨j.val, h⟩ N else prefixSum tr ⟨j.val - d, by omega⟩ (N + 1))) = 0 := by
      rw [← sumFin_zero d]
      apply sumFin_congr; intro j
      unfold T1Mat
      simp [hi, j.isLt]
    have h2 : sumFin d (fun j => T1Mat tr i ⟨d + j.val, by omega⟩ * (if h : d + j.val < d then prefixSum tr ⟨d + j.val, h⟩ N else prefixSum tr ⟨d + j.val - d, by omega⟩ (N + 1))) =
              sumFin d (fun j => LMat tr false ⟨i.val - d, by omega⟩ j * prefixSum tr j (N + 1)) +
              sumFin d (fun j => LMat tr true ⟨i.val - d, by omega⟩ j * prefixSum tr j (N + 1)) := by
      rw [← sumFin_add]
      apply sumFin_congr; intro j
      unfold T1Mat
      have hnot : ¬ (d + j.val < d) := by omega
      simp only [hi, hnot, dite_false, Int.add_mul]
      have hfin : (⟨d + j.val - d, by omega⟩ : Fin d) = j := Fin.ext (by dsimp only; omega)
      rw [hfin]
    rw [h1, h2, Int.zero_add, sumFin_LMat, sumFin_LMat]

theorem windowVec1_eq {d : Nat} (tr : ParityTransducer d) (hc : tr.isConsistent = true) :
    windowVec tr 1 = windowVec1 tr := by
  have h1 : (1 : Nat) = 2 * 0 + 1 := rfl
  rw [h1, windowVec_two_mul_add_one tr hc 0]
  unfold windowVec1
  congr 1
  funext j
  unfold windowVec
  by_cases hj : j.val < d
  · simp [hj, prefixSum, sumRange]
  · simp [hj, prefixSum, sumRange, ParityTransducer.eval_zero]

/-- **REUSABLE MECHANISM II (General Infinite Soundness Theorem for `ConeCert`):**
    If `checkConeCert tr cert = true` on a consistent LSB parity transducer `tr`, then
    for EVERY `N ≥ 1` and EVERY cone functional `i : Fin q`:
      `(C * W(N))_i ≥ 1`. -/
theorem coneCert_sound {d q : Nat} (tr : ParityTransducer d) (cert : ConeCert q (2 * d))
    (hcons : tr.isConsistent = true)
    (hcert : checkConeCert tr cert = true) :
    ∀ (N : Nat), 1 ≤ N → ∀ i : Fin q,
      1 ≤ sumFin (2 * d) (fun j => cert.CAt i j * windowVec tr N j) := by
  unfold checkConeCert at hcert
  simp only [Bool.and_eq_true] at hcert
  rcases hcert with ⟨⟨hBase, h0⟩, h1⟩
  rw [List.all_eq_true] at hBase h0 h1
  have hStep : ∀ (T : Fin (2 * d) → Fin (2 * d) → Int)
      (U : Fin q → Fin q → Nat) (den : Fin q → Nat)
      (hU : ∀ i : Fin q, 0 < den i ∧ 1 ≤ sumFin q (fun r => (U i r : Int)) ∧
            ∀ col : Fin (2 * d),
              (den i : Int) * sumFin (2 * d) (fun k => cert.CAt i k * T k col) =
              sumFin q (fun r => (U i r : Int) * cert.CAt r col))
      (w : Fin (2 * d) → Int)
      (hw : ∀ r : Fin q, 1 ≤ sumFin (2 * d) (fun col => cert.CAt r col * w col)),
      ∀ i : Fin q, 1 ≤ sumFin (2 * d) (fun k => cert.CAt i k * matVecInt T w k) := by
    intro T U den hU w hw i
    rcases hU i with ⟨hden, hrow, hmat⟩
    have hLHS : (den i : Int) * sumFin (2 * d) (fun k => cert.CAt i k * matVecInt T w k) =
                sumFin (2 * d) (fun col => ((den i : Int) * sumFin (2 * d) (fun k => cert.CAt i k * T k col)) * w col) := by
      unfold matVecInt
      rw [← sumFin_mul_left]
      have hA : sumFin (2 * d) (fun k => (den i : Int) * (cert.CAt i k * sumFin (2 * d) (fun col => T k col * w col))) =
                sumFin (2 * d) (fun k => sumFin (2 * d) (fun col => ((den i : Int) * (cert.CAt i k * T k col)) * w col)) := by
        apply sumFin_congr; intro k
        rw [← sumFin_mul_left, ← sumFin_mul_left]
        apply sumFin_congr; intro col
        rw [Int.mul_assoc, Int.mul_assoc]
      rw [hA, sumFin_swap]
      apply sumFin_congr; intro col
      rw [sumFin_mul_right, sumFin_mul_left]
    have hRHS : sumFin (2 * d) (fun col => ((den i : Int) * sumFin (2 * d) (fun k => cert.CAt i k * T k col)) * w col) =
                sumFin q (fun r => (U i r : Int) * sumFin (2 * d) (fun col => cert.CAt r col * w col)) := by
      have hB : sumFin (2 * d) (fun col => ((den i : Int) * sumFin (2 * d) (fun k => cert.CAt i k * T k col)) * w col) =
                sumFin (2 * d) (fun col => sumFin q (fun r => ((U i r : Int) * cert.CAt r col) * w col)) := by
        apply sumFin_congr; intro col
        rw [hmat col, ← sumFin_mul_right]
      rw [hB, sumFin_swap]
      apply sumFin_congr; intro r
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro col
      rw [Int.mul_assoc]
    have hGe : sumFin q (fun r => (U i r : Int)) ≤
               sumFin q (fun r => (U i r : Int) * sumFin (2 * d) (fun col => cert.CAt r col * w col)) := by
      apply sumFin_le_sumFin; intro r
      have hr := hw r
      have hu0 : (0 : Int) ≤ (U i r : Int) := Int.natCast_nonneg _
      have hmul : (U i r : Int) * 1 ≤ (U i r : Int) * sumFin (2 * d) (fun col => cert.CAt r col * w col) :=
        Int.mul_le_mul_of_nonneg_left hr hu0
      simpa using hmul
    have hprod_pos : 1 ≤ (den i : Int) * sumFin (2 * d) (fun k => cert.CAt i k * matVecInt T w k) := by
      rw [hLHS, hRHS]; omega
    -- Constructive: if a > 0 (Nat) and a * x >= 1 (Int), then x >= 1
    let X : Int := sumFin (2 * d) (fun k => cert.CAt i k * matVecInt T w k)
    change 1 ≤ X
    change 1 ≤ (den i : Int) * X at hprod_pos
    cases hX : X with
    | ofNat n =>
      cases n with
      | zero => rw [hX] at hprod_pos; simp at hprod_pos
      | succ m => exact Int.ofNat_le.mpr (Nat.succ_le_succ (Nat.zero_le m))
    | negSucc m =>
      rw [hX] at hprod_pos
      have hneg : (den i : Int) * Int.negSucc m ≤ 0 := by
        have h1 : Int.negSucc m ≤ 0 := by omega
        have h2 : (0 : Int) ≤ (den i : Int) := Int.natCast_nonneg _
        have h3 := Int.mul_le_mul_of_nonneg_left h1 h2
        simpa using h3
      omega
  have hU0 : ∀ i : Fin q, 0 < cert.den0At i ∧ 1 ≤ sumFin q (fun r => (cert.U0At i r : Int)) ∧
      ∀ col : Fin (2 * d),
        (cert.den0At i : Int) * sumFin (2 * d) (fun k => cert.CAt i k * T0Mat tr k col) =
        sumFin q (fun r => (cert.U0At i r : Int) * cert.CAt r col) := by
    intro i
    have hi := h0 i (List.mem_finRange i)
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hi
    exact ⟨hi.1.1, hi.1.2, fun col => hi.2 col (List.mem_finRange col)⟩
  have hU1 : ∀ i : Fin q, 0 < cert.den1At i ∧ 1 ≤ sumFin q (fun r => (cert.U1At i r : Int)) ∧
      ∀ col : Fin (2 * d),
        (cert.den1At i : Int) * sumFin (2 * d) (fun k => cert.CAt i k * T1Mat tr k col) =
        sumFin q (fun r => (cert.U1At i r : Int) * cert.CAt r col) := by
    intro i
    have hi := h1 i (List.mem_finRange i)
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hi
    exact ⟨hi.1.1, hi.1.2, fun col => hi.2 col (List.mem_finRange col)⟩
  -- Strong binary induction on N ≥ 1
  intro N
  have hStrong : ∀ M, ∀ k, k ≤ M → 1 ≤ k → ∀ i : Fin q,
      1 ≤ sumFin (2 * d) (fun j => cert.CAt i j * windowVec tr k j) := by
    intro M
    induction M with
    | zero => intro k hk1 hk2; omega
    | succ M ih =>
      intro k hkM hk1 i
      by_cases h1k : k = 1
      · subst h1k
        rw [windowVec1_eq tr hcons]
        have hi := hBase i (List.mem_finRange i)
        simpa [decide_eq_true_eq] using hi
      · have hhalf_le : k / 2 ≤ M := by omega
        have hhalf_ge : 1 ≤ k / 2 := by omega
        have hIH := ih (k / 2) hhalf_le hhalf_ge
        by_cases hpar : k % 2 = 0
        · have hEq : k = 2 * (k / 2) := by omega
          rw [hEq, windowVec_two_mul tr hcons]
          exact hStep (T0Mat tr) cert.U0At cert.den0At hU0 (windowVec tr (k / 2)) hIH i
        · have hEq : k = 2 * (k / 2) + 1 := by omega
          rw [hEq, windowVec_two_mul_add_one tr hcons]
          exact hStep (T1Mat tr) cert.U1At cert.den1At hU1 (windowVec tr (k / 2)) hIH i
  exact hStrong N N (Nat.le_refl N)

-- ============================================================================
-- SECTION 2B: CONCRETE BITWISE-OR & MULTIPLICATIVE TRANSDUCER COMPILATION
-- ============================================================================

theorem paritySign_add_bit (b k : Nat) (hb : b < 2) :
    paritySign (b + k) = signBool (b == 1) * paritySign k := by
  unfold paritySign signBool
  have : b = 0 ∨ b = 1 := by omega
  rcases this with rfl | rfl
  · simp
  · by_cases hk : k % 2 = 0
    · have h1 : (1 + k) % 2 ≠ 0 := by omega
      simp [hk, h1]
    · have h1 : (1 + k) % 2 = 0 := by omega
      simp [hk, h1]

theorem bit_lor_lt_two (a b : Nat) (ha : a < 2) (hb : b < 2) : a ||| b < 2 := by
  have ha2 : a = 0 ∨ a = 1 := by omega
  have hb2 : b = 0 ∨ b = 1 := by omega
  rcases ha2 with rfl | rfl <;> rcases hb2 with rfl | rfl <;> decide

theorem mul_two_decomp (c n g : Nat) :
    c * n + g = 2 * (c * (n / 2) + (c * (n % 2) + g) / 2) + (c * (n % 2) + g) % 2 := by
  have h1 : n = 2 * (n / 2) + n % 2 := by omega
  have h2 : c * n = 2 * (c * (n / 2)) + c * (n % 2) := by
    conv => lhs; rw [h1]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc]
  rw [h2]; omega

theorem eval_orMulTransducer (c : Nat) (hc : 0 < c) :
    ∀ (n : Nat) (g : Fin c),
      (orMulTransducer c hc).eval g n = paritySign (popcount (n ||| (c * n + g.val))) := by
  intro n
  have hStrong : ∀ M, ∀ k, k ≤ M → ∀ g : Fin c,
      (orMulTransducer c hc).eval g k = paritySign (popcount (k ||| (c * k + g.val))) := by
    intro M
    induction M with
    | zero =>
      intro k hk g
      have hk0 : k = 0 := by omega
      subst hk0
      simp [ParityTransducer.eval_zero, orMulTransducer]
    | succ M ih =>
      intro k hk g
      by_cases hk0 : k = 0
      · subst hk0
        simp [ParityTransducer.eval_zero, orMulTransducer]
      · rw [(orMulTransducer c hc).eval_step g k hk0]
        rw [ih (k / 2) (by omega)]
        have hbit : (if (k % 2 == 1) then 1 else 0) = k % 2 := by
          by_cases h : k % 2 = 1 <;> simp [h]; omega
        have hlor_lt : (k % 2) ||| ((c * (k % 2) + g.val) % 2) < 2 :=
          bit_lor_lt_two _ _ (by omega) (by omega)
        have hlor_eq : k ||| (c * k + g.val) =
            2 * ((k / 2) ||| (c * (k / 2) + (c * (k % 2) + g.val) / 2)) +
            ((k % 2) ||| ((c * (k % 2) + g.val) % 2)) := by
          have hk_eq : k = 2 * (k / 2) + k % 2 := by omega
          have hcn_eq := mul_two_decomp c k g.val
          conv => lhs; rw [hk_eq, ← hk_eq, hcn_eq]
          conv => lhs; arg 1; rw [hk_eq]
          exact lor_two_mul_add_bit _ _ _ _ (by omega) (by omega)
        rw [hlor_eq, popcount_two_mul_add_bit _ _ hlor_lt, paritySign_add_bit _ _ hlor_lt]
        simp only [orMulTransducer, hbit]
  exact hStrong n n (Nat.le_refl n)

theorem eval_mulTransducer (c : Nat) (hc : 0 < c) :
    ∀ (n : Nat) (g : Fin c),
      (mulTransducer c hc).eval g n = paritySign (popcount (c * n + g.val)) := by
  intro n
  have hStrong : ∀ M, ∀ k, k ≤ M → ∀ g : Fin c,
      (mulTransducer c hc).eval g k = paritySign (popcount (c * k + g.val)) := by
    intro M
    induction M with
    | zero =>
      intro k hk g
      have hk0 : k = 0 := by omega
      subst hk0
      simp [ParityTransducer.eval_zero, mulTransducer]
    | succ M ih =>
      intro k hk g
      by_cases hk0 : k = 0
      · subst hk0
        simp [ParityTransducer.eval_zero, mulTransducer]
      · rw [(mulTransducer c hc).eval_step g k hk0]
        rw [ih (k / 2) (by omega)]
        have hbit : (if (k % 2 == 1) then 1 else 0) = k % 2 := by
          by_cases h : k % 2 = 1 <;> simp [h]; omega
        rw [mul_two_decomp c k g.val, popcount_two_mul_add_bit _ _ (by omega), paritySign_add_bit _ _ (by omega)]
        simp only [mulTransducer, hbit]
  exact hStrong n n (Nat.le_refl n)

/-- Helper: extract strict evil dominance from row 0 of a cone certificate with `C[0] = e_0`. -/
theorem strict_evil_dominance_of_cert {d q : Nat} (hd : 0 < d) (hq : 0 < q)
    (tr : ParityTransducer d) (cert : ConeCert q (2 * d))
    (f : Nat → Nat)
    (hcons : tr.isConsistent = true)
    (hcert : checkConeCert tr cert = true)
    (hrow0 : ∀ j : Fin (2 * d), cert.CAt ⟨0, hq⟩ j = if j = ⟨0, by omega⟩ then 1 else 0)
    (heval : ∀ n, tr.eval ⟨0, hd⟩ n = paritySign (f n)) :
    ∀ N, 1 ≤ N → countMod N 2 1 f < countMod N 2 0 f := by
  intro N hN
  have h := coneCert_sound tr cert hcons hcert N hN ⟨0, hq⟩
  have hdot : sumFin (2 * d) (fun j => cert.CAt ⟨0, hq⟩ j * windowVec tr N j) =
              windowVec tr N ⟨0, by omega⟩ := by
    have h1 : sumFin (2 * d) (fun j => cert.CAt ⟨0, hq⟩ j * windowVec tr N j) =
              sumFin (2 * d) (fun j => if j = ⟨0, by omega⟩ then windowVec tr N j else 0) := by
      apply sumFin_congr; intro j
      rw [hrow0 j]; split <;> simp
    rw [h1, sumFin_single ⟨0, by omega⟩]
  rw [hdot] at h
  have hw0 : windowVec tr N ⟨0, by omega⟩ = sumRange N (fun n => paritySign (f n)) := by
    unfold windowVec prefixSum
    simp only [hd, dite_true]
    apply sumRange_congr; intro n _; exact heval n
  rw [hw0, sumRange_paritySign_eq_count_diff] at h
  omega

-- ============================================================================
-- SECTION 2C: FLAGSHIP INFINITE THEOREMS (THEOREMS 2, 2b, 3, 4)
-- ============================================================================

-- --- Certificate 2: Nonlinear Bitwise-OR `s_2(n ||| 5*n) mod 2` (q = 18, 2d = 10, max denom = 6) ---

theorem certOrMul5_valid : checkConeCert (orMulTransducer 5 (by decide)) certOrMul5 = true := by
  decide

/-- **THEOREM 2 (Nonlinear Bitwise-OR Evil Dominance for `n ||| 5*n`, ALL `N ≥ 1`):**
    For EVERY `N ≥ 1`, strictly more `n < N` have `s_2(n ||| 5*n)` even than odd. -/
theorem or_mul5_strict_evil_dominance :
    ∀ N : Nat, 1 ≤ N →
      countMod N 2 1 (fun n => popcount (n ||| (5 * n))) <
      countMod N 2 0 (fun n => popcount (n ||| (5 * n))) :=
  strict_evil_dominance_of_cert (by decide : 0 < 5) (by decide : 0 < 18)
    (orMulTransducer 5 (by decide)) certOrMul5 (fun n => popcount (n ||| (5 * n)))
    (by decide) certOrMul5_valid
    (by intro j; revert j; decide)
    (fun n => by simpa using eval_orMulTransducer 5 (by decide) n ⟨0, by decide⟩)

-- --- Theorem 2b: Exact Tribonacci Dyadic Law for `s_2(n ||| 5*n) mod 2` ---

theorem or5DyadicVec_step (k : Nat) :
    let v := or5DyadicVec k
    let nv := or5DyadicVec (k + 1)
    nv ⟨0, by decide⟩ = v ⟨0, by decide⟩ - v ⟨2, by decide⟩ ∧
    nv ⟨1, by decide⟩ = -v ⟨0, by decide⟩ - v ⟨3, by decide⟩ ∧
    nv ⟨2, by decide⟩ = v ⟨1, by decide⟩ - v ⟨3, by decide⟩ ∧
    nv ⟨3, by decide⟩ = -v ⟨1, by decide⟩ - v ⟨4, by decide⟩ ∧
    nv ⟨4, by decide⟩ = v ⟨2, by decide⟩ - v ⟨4, by decide⟩ := by
  have hcons : (orMulTransducer 5 (by decide)).isConsistent = true := by decide
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hstep : ∀ g : Fin 5,
      or5DyadicVec (k + 1) g =
      signBool ((orMulTransducer 5 (by decide)).outBit g false) *
        or5DyadicVec k ((orMulTransducer 5 (by decide)).nxt g false) +
      signBool ((orMulTransducer 5 (by decide)).outBit g true) *
        or5DyadicVec k ((orMulTransducer 5 (by decide)).nxt g true) := by
    intro g
    unfold or5DyadicVec
    rw [hpow, prefixSum_two_mul _ hcons g (2 ^ k)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := hstep ⟨0, by decide⟩; change or5DyadicVec (k + 1) ⟨0, by decide⟩ = 1 * or5DyadicVec k ⟨0, by decide⟩ + (-1) * or5DyadicVec k ⟨2, by decide⟩ at h; omega
  · have h := hstep ⟨1, by decide⟩; change or5DyadicVec (k + 1) ⟨1, by decide⟩ = (-1) * or5DyadicVec k ⟨0, by decide⟩ + (-1) * or5DyadicVec k ⟨3, by decide⟩ at h; omega
  · have h := hstep ⟨2, by decide⟩; change or5DyadicVec (k + 1) ⟨2, by decide⟩ = 1 * or5DyadicVec k ⟨1, by decide⟩ + (-1) * or5DyadicVec k ⟨3, by decide⟩ at h; omega
  · have h := hstep ⟨3, by decide⟩; change or5DyadicVec (k + 1) ⟨3, by decide⟩ = (-1) * or5DyadicVec k ⟨1, by decide⟩ + (-1) * or5DyadicVec k ⟨4, by decide⟩ at h; omega
  · have h := hstep ⟨4, by decide⟩; change or5DyadicVec (k + 1) ⟨4, by decide⟩ = 1 * or5DyadicVec k ⟨2, by decide⟩ + (-1) * or5DyadicVec k ⟨4, by decide⟩ at h; omega

/-- Exact eigen-defect of `or5DyadicVec`: `v(k+4) - v(k+3) - v(k+2) - v(k+1) = (-1)^(k+1) * (0, 2, 0, 2, 0)`. -/
theorem or5DyadicVec_tribonacci_defect (k : Nat) :
    let d (g : Fin 5) :=
      or5DyadicVec (k + 4) g - or5DyadicVec (k + 3) g - or5DyadicVec (k + 2) g - or5DyadicVec (k + 1) g
    let s : Int := if k % 2 = 0 then -2 else 2
    d ⟨0, by decide⟩ = 0 ∧ d ⟨1, by decide⟩ = s ∧ d ⟨2, by decide⟩ = 0 ∧
    d ⟨3, by decide⟩ = s ∧ d ⟨4, by decide⟩ = 0 := by
  induction k with
  | zero =>
    dsimp only
    have hbase : ∀ g : Fin 5,
        or5DyadicVec 4 g - or5DyadicVec 3 g - or5DyadicVec 2 g - or5DyadicVec 1 g =
        if g.val = 1 ∨ g.val = 3 then -2 else 0 := by
      intro g; revert g; decide
    exact ⟨hbase ⟨0, by decide⟩, hbase ⟨1, by decide⟩, hbase ⟨2, by decide⟩,
           hbase ⟨3, by decide⟩, hbase ⟨4, by decide⟩⟩
  | succ k ih =>
    rcases ih with ⟨d0, d1, d2, d3, d4⟩
    have s1 := or5DyadicVec_step (k + 1)
    have s2 := or5DyadicVec_step (k + 2)
    have s3 := or5DyadicVec_step (k + 3)
    have s4 := or5DyadicVec_step (k + 4)
    have e2 : k + 1 + 1 = k + 2 := by omega
    have e3 : k + 1 + 2 = k + 3 := by omega
    have e4 : k + 1 + 3 = k + 4 := by omega
    have e5 : k + 1 + 4 = k + 5 := by omega
    have f2 : k + 2 + 1 = k + 3 := by omega
    have f3 : k + 3 + 1 = k + 4 := by omega
    have f4 : k + 4 + 1 = k + 5 := by omega
    dsimp only at *
    rw [e2, e3, e4, e5]
    rw [e2] at s1; rw [f2] at s2; rw [f3] at s3; rw [f4] at s4
    by_cases hp : k % 2 = 0
    · have hp1 : (k + 1) % 2 ≠ 0 := by omega
      simp only [hp, ite_true] at d1 d3
      simp only [hp1, ite_false]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
    · have hp1 : (k + 1) % 2 = 0 := by omega
      simp only [hp, ite_false] at d1 d3
      simp only [hp1, ite_true]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **THEOREM 2b (Exact Tribonacci Dyadic Law for `s_2(n ||| 5*n) mod 2`):**
    For EVERY `k ≥ 1`:
      `∑_{n < 2^k} (-1)^{s_2(n ||| 5*n)} = 2 * tribonacci (k + 1)`. -/
theorem or_mul5_tribonacci_law (k : Nat) (hk : 1 ≤ k) :
    sumRange (2 ^ k) (fun n => paritySign (popcount (n ||| (5 * n)))) =
    2 * (tribonacci (k + 1) : Int) := by
  have heq : sumRange (2 ^ k) (fun n => paritySign (popcount (n ||| (5 * n)))) =
             or5DyadicVec k ⟨0, by decide⟩ := by
    unfold or5DyadicVec prefixSum
    apply sumRange_congr; intro n _
    simpa using (eval_orMulTransducer 5 (by decide) n ⟨0, by decide⟩).symm
  rw [heq]
  have hStrong : ∀ M, ∀ j, j ≤ M → 1 ≤ j →
      or5DyadicVec j ⟨0, by decide⟩ = 2 * (tribonacci (j + 1) : Int) := by
    intro M
    induction M with
    | zero => intro j hj1 hj2; omega
    | succ M ih =>
      intro j hjM hj1
      match j with
      | 0 => omega
      | 1 => decide
      | 2 => decide
      | 3 => decide
      | m + 4 =>
        have hdef := (or5DyadicVec_tribonacci_defect m).1
        dsimp only at hdef
        have h1 := ih (m + 1) (by omega) (by omega)
        have h2 := ih (m + 2) (by omega) (by omega)
        have h3 := ih (m + 3) (by omega) (by omega)
        have t2 : m + 1 + 1 = m + 2 := by omega
        have t3 : m + 2 + 1 = m + 3 := by omega
        have t4 : m + 3 + 1 = m + 4 := by omega
        have t5 : m + 4 + 1 = m + 5 := by omega
        rw [t2] at h1; rw [t3] at h2; rw [t4] at h3; rw [t5]
        have ht : tribonacci (m + 5) = tribonacci (m + 4) + tribonacci (m + 3) + tribonacci (m + 2) := rfl
        omega
  exact hStrong k k (Nat.le_refl k) hk

-- --- Certificate 3: Nonlinear Bitwise-OR `s_2(n ||| 3*n) mod 2` (q = 27, 2d = 6) ---

theorem certOrMul3_valid : checkConeCert (orMulTransducer 3 (by decide)) certOrMul3 = true := by
  decide

/-- **THEOREM 3 (Nonlinear Bitwise-OR Evil Dominance for `n ||| 3*n`, ALL `N ≥ 1`):**
    For EVERY `N ≥ 1`, strictly more `n < N` have `s_2(n ||| 3*n)` even than odd. -/
theorem or_mul3_strict_evil_dominance :
    ∀ N : Nat, 1 ≤ N →
      countMod N 2 1 (fun n => popcount (n ||| (3 * n))) <
      countMod N 2 0 (fun n => popcount (n ||| (3 * n))) :=
  strict_evil_dominance_of_cert (by decide : 0 < 3) (by decide : 0 < 27)
    (orMulTransducer 3 (by decide)) certOrMul3 (fun n => popcount (n ||| (3 * n)))
    (by decide) certOrMul3_valid
    (by intro j; revert j; decide)
    (fun n => by simpa using eval_orMulTransducer 3 (by decide) n ⟨0, by decide⟩)

-- --- Certificate 4: Classical Newman Benchmark `s_2(3*n) mod 2` (q = 9, 2d = 6, max denom = 3) ---

theorem certNewman3_valid : checkConeCert (mulTransducer 3 (by decide)) certNewman3 = true := by
  decide

/-- **THEOREM 4 (Classical Newman 1969 Benchmark Recovered in 9 Rows):**
    Demonstrates engine reuse across both linear (`3*n`) and nonlinear (`n ||| 3*n`, `n ||| 5*n`)
    binary carry transducers. -/
theorem mul3_newman_benchmark :
    ∀ N : Nat, 1 ≤ N →
      countMod N 2 1 (fun n => popcount (3 * n)) <
      countMod N 2 0 (fun n => popcount (3 * n)) :=
  strict_evil_dominance_of_cert (by decide : 0 < 3) (by decide : 0 < 9)
    (mulTransducer 3 (by decide)) certNewman3 (fun n => popcount (3 * n))
    (by decide) certNewman3_valid
    (by intro j; revert j; decide)
    (fun n => by simpa using eval_mulTransducer 3 (by decide) n ⟨0, by decide⟩)

-- ============================================================================
-- SECTION 3: NON-VACUITY, HOSTILE MUTATION TESTS & SHARPNESS COUNTEREXAMPLES
-- ============================================================================

/-- Non-vacuity witness for Engine I: explicit inhabited triple `(H, v)` for `m = 3`. -/
theorem engineI_nonvacuous_witness :
    ∃ (m : Nat) (hm : 0 < m),
      IsRevHermitian hm (mersenneH m) ∧
      countMod (2 ^ (m * 2)) m 1 (fun n => popcount ((2 ^ m - 1) * n)) = 9 ∧
      countMod (2 ^ (m * 2)) m 2 (fun n => popcount ((2 ^ m - 1) * n)) = 9 :=
  ⟨3, by decide, mersenneH_isRevHermitian 3 (by decide), by decide, by decide⟩

/-- Non-vacuity witness for Engine II: explicit inhabited `(tr, cert)` passing `checkConeCert`. -/
theorem engineII_nonvacuous_witness :
    ∃ (tr : ParityTransducer 5) (cert : ConeCert 18 10),
      tr.isConsistent = true ∧ checkConeCert tr cert = true :=
  ⟨orMulTransducer 5 (by decide), certOrMul5, by decide, certOrMul5_valid⟩

theorem hostile_mutation_U0_rejected :
    checkConeCert (orMulTransducer 5 (by decide)) badCertOrMul5_U0 = false := by
  decide

theorem hostile_mutation_den0_rejected :
    checkConeCert (orMulTransducer 5 (by decide)) badCertOrMul5_den0 = false := by
  decide

theorem hostile_mutation_wrong_transducer_rejected :
    checkConeCert (xorMulTransducer 5 (by decide)) certOrMul5 = false := by
  decide

/-- **3-WAY SHARPNESS COUNTEREXAMPLES FOR ENGINE II:**
    Replacing `|||` by `^^^`, replacing `|||` by `&&&`, or replacing `c ∈ {3, 5}` by `c = 7`
    all break strict evil dominance immediately at `N = 3` (`evil = 1 < 2 = odious`). -/
theorem engineII_three_way_sharpness :
    countMod 3 2 0 (fun n => popcount (n ^^^ (3 * n))) < countMod 3 2 1 (fun n => popcount (n ^^^ (3 * n))) ∧
    countMod 3 2 0 (fun n => popcount (n &&& (3 * n))) < countMod 3 2 1 (fun n => popcount (n &&& (3 * n))) ∧
    countMod 3 2 0 (fun n => popcount (n ^^^ (5 * n))) < countMod 3 2 1 (fun n => popcount (n ^^^ (5 * n))) ∧
    countMod 3 2 0 (fun n => popcount (n &&& (5 * n))) < countMod 3 2 1 (fun n => popcount (n &&& (5 * n))) ∧
    countMod 3 2 0 (fun n => popcount (n ||| (7 * n))) < countMod 3 2 1 (fun n => popcount (n ||| (7 * n))) := by
  decide

-- ============================================================================
-- SECTION 4: AXIOM VERIFICATION (SUBSET OF {propext, Classical.choice, Quot.sound})
-- ============================================================================


end Adic16
