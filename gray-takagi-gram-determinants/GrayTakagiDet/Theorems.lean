import GrayTakagiDet.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace GrayTakagiDet

open Matrix Polynomial BigOperators

/-! ## Section 1: Popcount and Gray-Code Bitwise Identities -/

private theorem popcount_zero : popcount 0 = 0 := by
  unfold popcount; simp

private theorem popcount_eq_mod_add_div (n : ℕ) :
    popcount n = n % 2 + popcount (n / 2) := by
  by_cases hn : n = 0
  · subst hn; simp [popcount_zero]
  · conv => lhs; unfold popcount
    simp [hn]

private theorem popcount_eq_zero_iff (n : ℕ) : popcount n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact hn
    · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
      rw [popcount_eq_mod_add_div] at h
      have hdiv : n / 2 = 0 := (popcount_eq_zero_iff (n / 2)).mp (by omega)
      omega
  · rintro rfl; exact popcount_zero
termination_by n

private theorem popcount_two_mul (n : ℕ) : popcount (2 * n) = popcount n := by
  rw [popcount_eq_mod_add_div (2 * n)]
  simp [show (2 * n) % 2 = 0 by omega, show (2 * n) / 2 = n by omega]

private theorem popcount_two_mul_add_one (n : ℕ) : popcount (2 * n + 1) = 1 + popcount n := by
  rw [popcount_eq_mod_add_div (2 * n + 1)]
  simp [show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega]

private theorem popcount_two_pow_add (m x : ℕ) (hx : x < 2 ^ m) :
    popcount (2 ^ m + x) = 1 + popcount x := by
  induction m generalizing x with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0
    rw [pow_zero, add_zero, popcount_zero, popcount_eq_mod_add_div 1]
    simp [popcount_zero]
  | succ m ih =>
    have hdiv : (2 ^ (m + 1) + x) / 2 = 2 ^ m + x / 2 := by
      rw [pow_succ]; omega
    have hmod : (2 ^ (m + 1) + x) % 2 = x % 2 := by
      rw [pow_succ]; omega
    rw [popcount_eq_mod_add_div (2 ^ (m + 1) + x), popcount_eq_mod_add_div x, hdiv, hmod]
    have hx' : x / 2 < 2 ^ m := by rw [pow_succ] at hx; omega
    rw [ih (x / 2) hx']
    omega

private theorem popcount_or_add_and (a b : ℕ) :
    popcount (a ||| b) + popcount (a &&& b) = popcount a + popcount b := by
  by_cases ha : a = 0
  · subst ha; simp [popcount_zero]
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    have ih := popcount_or_add_and (a / 2) (b / 2)
    rw [popcount_eq_mod_add_div (a ||| b), popcount_eq_mod_add_div (a &&& b),
      popcount_eq_mod_add_div a, popcount_eq_mod_add_div b]
    have hor_div : (a ||| b) / 2 = (a / 2) ||| (b / 2) := by
      apply Nat.eq_of_testBit_eq; intro k
      rw [← Nat.testBit_succ, Nat.testBit_or, Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ]
    have hand_div : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
      apply Nat.eq_of_testBit_eq; intro k
      rw [← Nat.testBit_succ, Nat.testBit_and, Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ]
    have hbit : (a ||| b) % 2 + (a &&& b) % 2 = a % 2 + b % 2 := by
      have h1 : (a ||| b).testBit 0 = (a.testBit 0 || b.testBit 0) := Nat.testBit_or a b 0
      have h2 : (a &&& b).testBit 0 = (a.testBit 0 && b.testBit 0) := Nat.testBit_and a b 0
      simp only [Nat.testBit_zero] at h1 h2
      have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2 <;>
        (rw [ha2, hb2] at h1 h2;
         by_cases ho : (a ||| b) % 2 = 1 <;> by_cases hn : (a &&& b) % 2 = 1 <;>
          (simp [ho, hn] at h1 h2; try omega))
    rw [hor_div, hand_div]; omega
termination_by a

private theorem popcount_xor_add_two_and (a b : ℕ) :
    popcount (a ^^^ b) + 2 * popcount (a &&& b) = popcount a + popcount b := by
  by_cases ha : a = 0
  · subst ha; simp [popcount_zero]
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    have ih := popcount_xor_add_two_and (a / 2) (b / 2)
    rw [popcount_eq_mod_add_div (a ^^^ b), popcount_eq_mod_add_div (a &&& b),
      popcount_eq_mod_add_div a, popcount_eq_mod_add_div b]
    have hxor_div : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
      apply Nat.eq_of_testBit_eq; intro k
      rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ]
    have hand_div : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
      apply Nat.eq_of_testBit_eq; intro k
      rw [← Nat.testBit_succ, Nat.testBit_and, Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ]
    have hbit : (a ^^^ b) % 2 + 2 * ((a &&& b) % 2) = a % 2 + b % 2 := by
      have h1 : (a ^^^ b).testBit 0 = (a.testBit 0 ^^ b.testBit 0) := Nat.testBit_xor a b 0
      have h2 : (a &&& b).testBit 0 = (a.testBit 0 && b.testBit 0) := Nat.testBit_and a b 0
      simp only [Nat.testBit_zero] at h1 h2
      have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2 <;>
        (rw [ha2, hb2] at h1 h2;
         by_cases hx : (a ^^^ b) % 2 = 1 <;> by_cases hn : (a &&& b) % 2 = 1 <;>
          (simp [hx, hn] at h1 h2; try omega))
    rw [hxor_div, hand_div]; omega
termination_by a

private theorem testBit_two_pow_add (m x k : ℕ) (hx : x < 2 ^ m) :
    (2 ^ m + x).testBit k = if k = m then true else if k < m then x.testBit k else false := by
  by_cases hkm : k < m
  · have hne : k ≠ m := by omega
    have hm : (2 ^ m + x) % 2 ^ m = x % 2 ^ m := by simp
    have htb := congrArg (fun n => n.testBit k) hm
    simp only [Nat.testBit_mod_two_pow, decide_eq_true hkm, Bool.true_and] at htb
    simp [hkm, hne, htb]
  · by_cases heq : k = m
    · subst heq
      have hdiv : (2 ^ k + x) / 2 ^ k = 1 := by
        rw [Nat.add_comm, Nat.add_div_right _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hx]
      simp only [↓reduceIte]
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]; simp
    · have hlt : 2 ^ m + x < 2 ^ k := by
        have hp : 2 ^ (m + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        rw [pow_succ] at hp; omega
      simp [hkm, heq, Nat.testBit_lt_two_pow hlt]

private theorem testBit_two_pow_sub_one_sub (m r k : ℕ) (hr : r < 2 ^ m) :
    (2 ^ m - 1 - r).testBit k = if k < m then !r.testBit k else false := by
  induction m generalizing r k with
  | zero =>
    have hr0 : r = 0 := by omega
    subst hr0; simp
  | succ m ih =>
    have hle : r ≤ 2 ^ (m + 1) - 1 := by omega
    have hsub_div : (2 ^ (m + 1) - 1 - r) / 2 = 2 ^ m - 1 - r / 2 := by
      have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
      omega
    have hsub_mod : (2 ^ (m + 1) - 1 - r) % 2 = 1 - r % 2 := by
      have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
      omega
    cases k with
    | zero =>
      simp only [Nat.zero_lt_succ, ↓reduceIte, Nat.testBit_zero, hsub_mod]
      by_cases h : r % 2 = 1
      · simp [h]
      · simp [show r % 2 = 0 by omega]
    | succ k =>
      rw [Nat.testBit_succ, Nat.testBit_succ, hsub_div, ih (r / 2) k (by rw [pow_succ] at hr; omega)]
      by_cases hkm : k < m <;> simp [hkm, show (k + 1 < m + 1) ↔ k < m by omega]

private theorem gray_testBit (n k : ℕ) :
    (gray n).testBit k = (n.testBit k ^^ n.testBit (k + 1)) := by
  unfold gray
  rw [Nat.testBit_xor, Nat.testBit_succ]

private theorem gray_lt_two_pow (m i : ℕ) (hi : i < 2 ^ m) : gray i < 2 ^ m := by
  unfold gray
  exact Nat.xor_lt_two_pow hi (by omega)

private theorem gray_injective : Function.Injective gray := by
  intro i j hij
  apply Nat.eq_of_testBit_eq
  -- Downward induction from an upper bound `N` above `max i j`.
  have hdown : ∀ N, i < 2 ^ N → j < 2 ^ N → ∀ d, i.testBit (N - d) = j.testBit (N - d) := by
    intro N hi hj d
    induction d with
    | zero =>
      simp only [Nat.sub_zero]
      rw [Nat.testBit_lt_two_pow hi, Nat.testBit_lt_two_pow hj]
    | succ d ih =>
      by_cases hd : N ≤ d
      · have h1 : N - (d + 1) = 0 := by omega
        have h2 : N - d = 0 := by omega
        rw [h1]; rw [h2] at ih; exact ih
      · have hsucc : N - (d + 1) + 1 = N - d := by omega
        have htb := congrArg (fun n => n.testBit (N - (d + 1))) hij
        rw [gray_testBit, gray_testBit, hsucc, ih] at htb
        cases ha : i.testBit (N - (d + 1)) <;> cases hb : j.testBit (N - (d + 1)) <;>
          cases hc : j.testBit (N - d) <;> simp [ha, hb, hc] at htb ⊢
  intro k
  let N := max (max i j) k + 1
  have hlt_pow : ∀ x, x < 2 ^ x := fun x => Nat.lt_two_pow_self
  have hiN : i < 2 ^ N := lt_of_lt_of_le (hlt_pow i) (Nat.pow_le_pow_right (by omega) (by omega))
  have hjN : j < 2 ^ N := lt_of_lt_of_le (hlt_pow j) (Nat.pow_le_pow_right (by omega) (by omega))
  have h := hdown N hiN hjN (N - k)
  rwa [show N - (N - k) = k by omega] at h

private noncomputable def grayPerm (m : ℕ) : Equiv.Perm (Fin (2 ^ m)) :=
  Equiv.ofBijective
    (fun i : Fin (2 ^ m) => ⟨gray i.val, gray_lt_two_pow m i.val i.isLt⟩)
    ((Finite.injective_iff_bijective).mp fun i j h => by
      ext
      exact gray_injective (congrArg Fin.val h))

private theorem grayPerm_val (m : ℕ) (i : Fin (2 ^ m)) : (grayPerm m i).val = gray i.val := rfl

private theorem gray_add_two_pow (m r : ℕ) (hr : r < 2 ^ m) :
    gray (2 ^ m + r) = 2 ^ m + gray (2 ^ m - 1 - r) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [gray_testBit, testBit_two_pow_add m (gray (2 ^ m - 1 - r)) k
    (gray_lt_two_pow m _ (by omega))]
  rw [testBit_two_pow_add m r k hr, testBit_two_pow_add m r (k + 1) hr]
  by_cases hkm : k < m
  · have hne : k ≠ m := by omega
    simp only [hne, hkm, ↓reduceIte]
    rw [gray_testBit, testBit_two_pow_sub_one_sub m r k hr,
      testBit_two_pow_sub_one_sub m r (k + 1) hr]
    by_cases hk1 : k + 1 < m
    · simp only [hkm, hk1, show k + 1 ≠ m by omega, ↓reduceIte]
      cases r.testBit k <;> cases r.testBit (k + 1) <;> rfl
    · have hkeq : k + 1 = m := by omega
      simp only [hkm, hkeq, show ¬ m < m by omega, ↓reduceIte]
      cases r.testBit k <;> rfl
  · by_cases heq : k = m
    · subst heq
      simp [show ¬ (k + 1 < k) by omega]
    · simp [hkm, heq, show ¬ (k + 1 < m) by omega, show k + 1 ≠ m by omega]

private theorem gray_reflect (m r : ℕ) (hr : r < 2 ^ m) :
    gray (2 ^ (m + 1) - 1 - r) = 2 ^ m + gray r := by
  have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
  have hr' : 2 ^ m - 1 - r < 2 ^ m := by omega
  have h1 : 2 ^ (m + 1) - 1 - r = 2 ^ m + (2 ^ m - 1 - r) := by omega
  have h2' : 2 ^ m - 1 - (2 ^ m - 1 - r) = r := by omega
  rw [h1, gray_add_two_pow m (2 ^ m - 1 - r) hr', h2']

private theorem and_two_pow_add_left (m x y : ℕ) (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    x &&& (2 ^ m + y) = x &&& y := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_and, testBit_two_pow_add m y k hy]
  by_cases hkm : k < m
  · simp [hkm, show k ≠ m by omega]
  · have hxf : x.testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hxf]

private theorem and_two_pow_add_both (m x y : ℕ) (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    (2 ^ m + x) &&& (2 ^ m + y) = 2 ^ m + (x &&& y) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, testBit_two_pow_add m x k hx, testBit_two_pow_add m y k hy,
    testBit_two_pow_add m (x &&& y) k (lt_of_le_of_lt Nat.and_le_left hx)]
  by_cases hkm : k < m
  · simp [hkm, show k ≠ m by omega, Nat.testBit_and]
  · by_cases heq : k = m
    · simp [heq]
    · simp [hkm, heq]

/-! ## Section 2: Takagi Function & Gray Popcount Sum Identities -/

private theorem takagi_zero : takagi 0 = 0 := by
  unfold takagi; simp

private theorem takagi_one : takagi 1 = 0 := by
  unfold takagi; simp

theorem takagi_recurrence (m k : ℕ) (hk : k ≤ 2 ^ m) :
    takagi (2 ^ m + k) = takagi k + min k (2 ^ m - k) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp only [add_zero, takagi_zero, Nat.min_eq_left (Nat.zero_le _)]
    clear hk
    induction m with
    | zero => exact takagi_one
    | succ m ih =>
      have hge : ¬ (2 ^ (m + 1) ≤ 1) := by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ m + 1); omega
      conv => lhs; unfold takagi
      simp only [hge, ↓reduceDIte]
      have hlog : Nat.log 2 (2 ^ (m + 1) - 1) = m := by
        apply Nat.log_eq_of_pow_le_of_lt_pow
        · have : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
          have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
          omega
        · omega
      rw [hlog]
      have hsub : 2 ^ (m + 1) - 2 ^ m = 2 ^ m := by rw [pow_succ]; omega
      rw [hsub, Nat.sub_self, ih]
      simp
  · have hge : ¬ (2 ^ m + k ≤ 1) := by
      have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
      omega
    conv => lhs; unfold takagi
    simp only [hge, ↓reduceDIte]
    have hlog : Nat.log 2 (2 ^ m + k - 1) = m := by
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · omega
      · rw [pow_succ]; omega
    rw [hlog, Nat.add_sub_cancel_left]

private theorem takagi_pow2 (m : ℕ) : takagi (2 ^ m) = 0 := by
  have h := takagi_recurrence m 0 (Nat.zero_le _)
  simpa [takagi_zero] using h

theorem takagi_eq_zero_iff (n : ℕ) :
    takagi n = 0 ↔ n = 0 ∨ ∃ m : ℕ, n = 2 ^ m := by
  constructor
  · intro h
    by_cases hn1 : n ≤ 1
    · interval_cases n
      · exact Or.inl rfl
      · exact Or.inr ⟨0, rfl⟩
    · let m := Nat.log 2 (n - 1)
      have hm1 : 2 ^ m ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
      have hm2 : n - 1 < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) (n - 1)
      let k := n - 2 ^ m
      have hk_pos : 1 ≤ k := by omega
      have hk_le : k ≤ 2 ^ m := by rw [pow_succ] at hm2; omega
      have hn_eq : n = 2 ^ m + k := by omega
      rw [hn_eq, takagi_recurrence m k hk_le] at h
      have hmin0 : min k (2 ^ m - k) = 0 := by omega
      have hkeq : k = 2 ^ m := by omega
      exact Or.inr ⟨m + 1, by rw [hn_eq, hkeq, pow_succ]; omega⟩
  · rintro (rfl | ⟨m, rfl⟩)
    · exact takagi_zero
    · exact takagi_pow2 m

private theorem popcount_sum_pow2 (m : ℕ) :
    ∑ i ∈ Finset.range (2 ^ m), popcount i = m * 2 ^ (m - 1) := by
  induction m with
  | zero => simp [popcount_zero]
  | succ m ih =>
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
    rw [h2, Finset.sum_range_add]
    have hshift : ∑ x ∈ Finset.range (2 ^ m), popcount (2 ^ m + x) =
        2 ^ m + ∑ x ∈ Finset.range (2 ^ m), popcount x := by
      have hcongr : ∑ x ∈ Finset.range (2 ^ m), popcount (2 ^ m + x) =
          ∑ x ∈ Finset.range (2 ^ m), (1 + popcount x) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact popcount_two_pow_add m x (Finset.mem_range.mp hx)
      rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    rw [hshift, ih]
    cases m with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
      rw [hp]; ring

private theorem grayPopSum_pow2 (m : ℕ) :
    grayPopSum (2 ^ m) = m * 2 ^ (m - 1) := by
  unfold grayPopSum
  have hbij : ∑ i ∈ Finset.range (2 ^ m), popcount (gray i) =
      ∑ i : Fin (2 ^ m), popcount (grayPerm m i).val := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => popcount (gray i)) (2 ^ m)]
    rfl
  have hperm : ∑ i : Fin (2 ^ m), popcount (grayPerm m i).val =
      ∑ i : Fin (2 ^ m), popcount i.val :=
    Fintype.sum_equiv (grayPerm m) _ _ (fun _ => rfl)
  rw [hbij, hperm, Fin.sum_univ_eq_sum_range popcount (2 ^ m)]
  exact popcount_sum_pow2 m

private theorem grayPopSum_add_eq (m k : ℕ) (hk : k ≤ 2 ^ m) :
    grayPopSum (2 ^ m + k) =
      grayPopSum (2 ^ m) + k + min k (2 ^ m - k) + grayPopSum k := by
  induction m generalizing k with
  | zero =>
    have hk1 : k = 0 ∨ k = 1 := by omega
    rcases hk1 with rfl | rfl
    · simp [grayPopSum]
    · simp [grayPopSum, Finset.sum_range_succ, gray, popcount_zero, popcount_eq_mod_add_div 1]
  | succ m ih =>
    unfold grayPopSum
    rw [Finset.sum_range_add]
    by_cases hk_half : k ≤ 2 ^ m
    · have htail : ∑ r ∈ Finset.range k, popcount (gray (2 ^ (m + 1) + r)) =
          2 * k + ∑ r ∈ Finset.range k, popcount (gray r) := by
        have hcongr : ∑ r ∈ Finset.range k, popcount (gray (2 ^ (m + 1) + r)) =
            ∑ r ∈ Finset.range k, (2 + popcount (gray r)) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hr_lt : r < 2 ^ m := lt_of_lt_of_le (Finset.mem_range.mp hr) hk_half
          have hr_lt2 : r < 2 ^ (m + 1) := lt_of_lt_of_le hr_lt (Nat.pow_le_pow_right (by omega) (by omega))
          rw [gray_add_two_pow (m + 1) r hr_lt2,
            popcount_two_pow_add (m + 1) _ (gray_lt_two_pow (m + 1) _ (by omega)),
            gray_reflect m r hr_lt,
            popcount_two_pow_add m _ (gray_lt_two_pow m r hr_lt)]
          omega
        rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
        omega
      rw [htail]
      have hmin : min k (2 ^ (m + 1) - k) = k := by rw [pow_succ] at *; omega
      rw [hmin]; omega
    · let j := k - 2 ^ m
      have hj_le : j ≤ 2 ^ m := by rw [pow_succ] at hk; omega
      have hk_eq : k = 2 ^ m + j := by omega
      rw [hk_eq, Finset.sum_range_add]
      have hfirst : ∑ r ∈ Finset.range (2 ^ m), popcount (gray (2 ^ (m + 1) + r)) =
          2 * 2 ^ m + ∑ r ∈ Finset.range (2 ^ m), popcount (gray r) := by
        have hcongr : ∑ r ∈ Finset.range (2 ^ m), popcount (gray (2 ^ (m + 1) + r)) =
            ∑ r ∈ Finset.range (2 ^ m), (2 + popcount (gray r)) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hr_lt : r < 2 ^ m := Finset.mem_range.mp hr
          have hr_lt2 : r < 2 ^ (m + 1) := lt_of_lt_of_le hr_lt (Nat.pow_le_pow_right (by omega) (by omega))
          rw [gray_add_two_pow (m + 1) r hr_lt2,
            popcount_two_pow_add (m + 1) _ (gray_lt_two_pow (m + 1) _ (by omega)),
            gray_reflect m r hr_lt,
            popcount_two_pow_add m _ (gray_lt_two_pow m r hr_lt)]
          omega
        rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
        omega
      have hsecond : ∑ s ∈ Finset.range j, popcount (gray (2 ^ (m + 1) + (2 ^ m + s))) =
          ∑ s ∈ Finset.range j, popcount (gray (2 ^ m + s)) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hs_lt : s < 2 ^ m := lt_of_lt_of_le (Finset.mem_range.mp hs) hj_le
        have hsum_lt : 2 ^ m + s < 2 ^ (m + 1) := by rw [pow_succ]; omega
        rw [gray_add_two_pow (m + 1) (2 ^ m + s) hsum_lt,
          popcount_two_pow_add (m + 1) _ (gray_lt_two_pow (m + 1) _ (by omega))]
        rw [gray_add_two_pow m s hs_lt,
          popcount_two_pow_add m _ (gray_lt_two_pow m _ (by omega))]
        have hsub : 2 ^ (m + 1) - 1 - (2 ^ m + s) = 2 ^ m - 1 - s := by rw [pow_succ]; omega
        rw [hsub]
      rw [hfirst, hsecond, Finset.sum_range_add]
      have hmin : min (2 ^ m + j) (2 ^ (m + 1) - (2 ^ m + j)) = 2 ^ m - j := by
        rw [pow_succ]; omega
      rw [hmin]
      have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
      omega

theorem takagi_le_grayPopSum (n : ℕ) : takagi n ≤ grayPopSum n := by
  by_cases hn1 : n ≤ 1
  · interval_cases n <;> simp [takagi_zero, takagi_one]
  · let m := Nat.log 2 (n - 1)
    have hm1 : 2 ^ m ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
    have hm2 : n - 1 < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) (n - 1)
    let k := n - 2 ^ m
    have hk_le : k ≤ 2 ^ m := by rw [pow_succ] at hm2; omega
    have hk_lt : k < n := by have := Nat.two_pow_pos m; omega
    have hn_eq : n = 2 ^ m + k := by omega
    have ih := takagi_le_grayPopSum k
    rw [hn_eq, takagi_recurrence m k hk_le, grayPopSum_add_eq m k hk_le]
    omega
termination_by n

private theorem grayPopSum_sub_takagi_add (m k : ℕ) (hk : k ≤ 2 ^ m) :
    grayPopSum (2 ^ m + k) - takagi (2 ^ m + k) =
      grayPopSum (2 ^ m) + k + (grayPopSum k - takagi k) := by
  have hle := takagi_le_grayPopSum k
  rw [grayPopSum_add_eq m k hk, takagi_recurrence m k hk]
  omega

/-! ## Section 3: Boolean Zeta `LDL^T` Factorization at `n = 2^m` -/

private def unpermAndMat {R : Type*} [CommRing R] (q : R) (m : ℕ) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) R :=
  Matrix.of fun i j => q ^ popcount (i.val &&& j.val)

private def zetaMat {R : Type*} [CommRing R] (m : ℕ) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) R :=
  Matrix.of fun i j => if (i.val &&& j.val) = j.val then 1 else 0

private theorem sum_submask_pow {R : Type*} [CommRing R] (q : R) (m a : ℕ) (ha : a < 2 ^ m) :
    ∑ u ∈ Finset.range (2 ^ m), (if (a &&& u) = u then (q - 1) ^ popcount u else 0) =
      q ^ popcount a := by
  induction m generalizing a with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    simp [popcount_zero]
  | succ m ih =>
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
    rw [h2, Finset.sum_range_add]
    by_cases ha_lt : a < 2 ^ m
    · have hhi : ∑ u ∈ Finset.range (2 ^ m),
          (if (a &&& (2 ^ m + u)) = 2 ^ m + u then (q - 1) ^ popcount (2 ^ m + u) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        have hlt : a &&& (2 ^ m + u) < 2 ^ m := lt_of_le_of_lt Nat.and_le_left ha_lt
        simp [show a &&& (2 ^ m + u) ≠ 2 ^ m + u by omega]
      rw [hhi, add_zero]
      exact ih a ha_lt
    · let a' := a - 2 ^ m
      have ha' : a' < 2 ^ m := by omega
      have ha_eq : a = 2 ^ m + a' := by omega
      rw [ha_eq]
      have hlo : ∑ u ∈ Finset.range (2 ^ m),
          (if ((2 ^ m + a') &&& u) = u then (q - 1) ^ popcount u else 0) = q ^ popcount a' := by
        rw [← ih a' ha']
        apply Finset.sum_congr rfl
        intro u hu
        have hu_lt : u < 2 ^ m := Finset.mem_range.mp hu
        rw [Nat.and_comm, and_two_pow_add_left m u a' hu_lt ha', Nat.and_comm]
      have hhi : ∑ u ∈ Finset.range (2 ^ m),
          (if ((2 ^ m + a') &&& (2 ^ m + u)) = 2 ^ m + u then (q - 1) ^ popcount (2 ^ m + u) else 0) =
          (q - 1) * q ^ popcount a' := by
        rw [← ih a' ha', Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        have hu_lt : u < 2 ^ m := Finset.mem_range.mp hu
        rw [and_two_pow_add_both m a' u ha' hu_lt, popcount_two_pow_add m u hu_lt]
        have hiff : (2 ^ m + (a' &&& u) = 2 ^ m + u) ↔ (a' &&& u = u) := by omega
        by_cases h : a' &&& u = u
        · simp only [h, ↓reduceIte]
          rw [Nat.add_comm 1, pow_succ, mul_comm]
        · simp [h]
      rw [hlo, hhi, popcount_two_pow_add m a' ha', Nat.add_comm 1, pow_succ]
      ring

private theorem unpermAndMat_factor {R : Type*} [CommRing R] (q : R) (m : ℕ) :
    unpermAndMat q m =
      zetaMat m * Matrix.diagonal (fun u : Fin (2 ^ m) => (q - 1) ^ popcount u.val) * (zetaMat m)ᵀ := by
  ext i j
  simp only [unpermAndMat, zetaMat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
    Matrix.of_apply, mul_ite, mul_zero, ite_mul, zero_mul, one_mul, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hsum : ∑ u : Fin (2 ^ m),
      (if (j.val &&& u.val) = u.val then if (i.val &&& u.val) = u.val then (q - 1) ^ popcount u.val else 0 else 0) =
      ∑ u ∈ Finset.range (2 ^ m),
        (if ((i.val &&& j.val) &&& u) = u then (q - 1) ^ popcount u else 0) := by
    rw [Fin.sum_univ_eq_sum_range (fun u =>
      if (j.val &&& u) = u then if (i.val &&& u) = u then (q - 1) ^ popcount u else 0 else 0) (2 ^ m)]
    apply Finset.sum_congr rfl
    intro u _
    have hiff : ((i.val &&& j.val) &&& u = u) ↔ (i.val &&& u = u ∧ j.val &&& u = u) := by
      constructor
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro k
          have htb := congrArg (fun z => z.testBit k) h
          simp only [Nat.testBit_and] at htb ⊢
          cases h1 : i.val.testBit k <;> cases h2 : j.val.testBit k <;> cases h3 : u.testBit k <;>
            simp [h1, h2, h3] at htb ⊢
        · apply Nat.eq_of_testBit_eq; intro k
          have htb := congrArg (fun z => z.testBit k) h
          simp only [Nat.testBit_and] at htb ⊢
          cases h1 : i.val.testBit k <;> cases h2 : j.val.testBit k <;> cases h3 : u.testBit k <;>
            simp [h1, h2, h3] at htb ⊢
      · rintro ⟨hi, hj⟩
        apply Nat.eq_of_testBit_eq; intro k
        have h1 := congrArg (fun z => z.testBit k) hi
        have h2 := congrArg (fun z => z.testBit k) hj
        simp only [Nat.testBit_and] at h1 h2 ⊢
        cases ha : i.val.testBit k <;> cases hb : j.val.testBit k <;> cases hc : u.testBit k <;>
          simp [ha, hb, hc] at h1 h2 ⊢
    by_cases hi : i.val &&& u = u <;> by_cases hj : j.val &&& u = u <;> simp [hiff, hi, hj]
  rw [hsum]
  exact (sum_submask_pow q m (i.val &&& j.val) (lt_of_le_of_lt Nat.and_le_left i.isLt)).symm

private theorem det_zetaMat {R : Type*} [CommRing R] (m : ℕ) : (zetaMat (R := R) m).det = 1 := by
  have htri : (zetaMat (R := R) m).BlockTriangular (fun i : Fin (2 ^ m) => OrderDual.toDual i) := by
    intro i j hij
    have hlt : i.val < j.val := hij
    simp only [zetaMat, Matrix.of_apply]
    have hle : i.val &&& j.val ≤ i.val := Nat.and_le_left
    simp [show i.val &&& j.val ≠ j.val by omega]
  rw [Matrix.det_of_isLowerTriangular (zetaMat (R := R) m) htri]
  apply Finset.prod_eq_one
  intro i _
  simp [zetaMat, Nat.and_self]

theorem det_grayAndMat_pow2_eq {R : Type*} [CommRing R] (q : R) (m : ℕ) :
    (grayAndMat q (2 ^ m)).det = (q - 1) ^ (m * 2 ^ (m - 1)) := by
  have hsub : grayAndMat q (2 ^ m) = (unpermAndMat q m).submatrix (grayPerm m) (grayPerm m) := by
    ext i j
    simp [grayAndMat, unpermAndMat, grayPerm_val]
  rw [hsub, Matrix.det_submatrix_equiv_self, unpermAndMat_factor, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, det_zetaMat, Matrix.det_diagonal, one_mul, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range popcount (2 ^ m), popcount_sum_pow2]

/-! ## Section 4: Block-Triangular Schur Reductions (All `n : ℕ`) -/

private def tailMat {R : Type*} [CommRing R] (q : R) (m k : ℕ) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun r s => q ^ popcount (gray (2 ^ m - 1 - r.val) &&& gray (2 ^ m - 1 - s.val))

private theorem det_grayAndMat_add {R : Type*} [CommRing R] (q : R) (m k : ℕ) (hk : k ≤ 2 ^ m) :
    (grayAndMat q (2 ^ m + k)).det =
      (grayAndMat q (2 ^ m)).det * (q - 1) ^ k * (tailMat q m k).det := by
  let A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) R := grayAndMat q (2 ^ m)
  let E : Matrix (Fin (2 ^ m)) (Fin k) R :=
    Matrix.of fun i r => if i.val = 2 ^ m - 1 - r.val then 1 else 0
  have hAE : ∀ i r, (A * E) i r = q ^ popcount (gray i.val &&& gray (2 ^ m - 1 - r.val)) := by
    intro i r
    have hlt : 2 ^ m - 1 - r.val < 2 ^ m := by omega
    rw [Matrix.mul_apply]
    simp only [E, Matrix.of_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single ⟨2 ^ m - 1 - r.val, hlt⟩]
    · simp [A, grayAndMat]
    · intro x _ hne
      have hval : x.val ≠ 2 ^ m - 1 - r.val := fun h => hne (Fin.ext h)
      simp [hval]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hEtA : ∀ r j, (Eᵀ * A) r j = q ^ popcount (gray (2 ^ m - 1 - r.val) &&& gray j.val) := by
    intro r j
    have hlt : 2 ^ m - 1 - r.val < 2 ^ m := by omega
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, E, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single ⟨2 ^ m - 1 - r.val, hlt⟩]
    · simp [A, grayAndMat]
    · intro x _ hne
      have hval : x.val ≠ 2 ^ m - 1 - r.val := fun h => hne (Fin.ext h)
      simp [hval]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hEtAE : Eᵀ * A * E = tailMat q m k := by
    ext r s
    have hlt : 2 ^ m - 1 - s.val < 2 ^ m := by omega
    rw [Matrix.mul_apply]
    simp only [E, Matrix.of_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single ⟨2 ^ m - 1 - s.val, hlt⟩]
    · simp only [↓reduceIte]; exact hEtA r ⟨2 ^ m - 1 - s.val, hlt⟩
    · intro x _ hne
      have hval : x.val ≠ 2 ^ m - 1 - s.val := fun h => hne (Fin.ext h)
      simp [hval]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hblock : (grayAndMat q (2 ^ m + k)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A (A * E) (Eᵀ * A) (q • (Eᵀ * A * E)) := by
    ext x y
    cases x with
    | inl i =>
      cases y with
      | inl j => simp [grayAndMat, A]
      | inr r =>
        have hr_lt : r.val < 2 ^ m := lt_of_lt_of_le r.isLt hk
        simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.val_castAdd, Fin.val_natAdd, grayAndMat, Matrix.of_apply, Matrix.fromBlocks_apply₁₂, hAE]
        rw [gray_add_two_pow m r.val hr_lt,
          and_two_pow_add_left m _ _ (gray_lt_two_pow m i.val i.isLt) (gray_lt_two_pow m _ (by omega))]
    | inr r =>
      cases y with
      | inl j =>
        have hr_lt : r.val < 2 ^ m := lt_of_lt_of_le r.isLt hk
        simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.val_castAdd, Fin.val_natAdd, grayAndMat, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, hEtA]
        rw [gray_add_two_pow m r.val hr_lt, Nat.and_comm,
          and_two_pow_add_left m _ _ (gray_lt_two_pow m j.val j.isLt) (gray_lt_two_pow m _ (by omega)),
          Nat.and_comm]
      | inr s =>
        have hr_lt : r.val < 2 ^ m := lt_of_lt_of_le r.isLt hk
        have hs_lt : s.val < 2 ^ m := lt_of_lt_of_le s.isLt hk
        simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, Fin.val_natAdd,
          grayAndMat, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul,
          hEtAE, tailMat]
        rw [gray_add_two_pow m r.val hr_lt, gray_add_two_pow m s.val hs_lt,
          and_two_pow_add_both m _ _ (gray_lt_two_pow m _ (by omega)) (gray_lt_two_pow m _ (by omega)),
          popcount_two_pow_add m _ (lt_of_le_of_lt Nat.and_le_left (gray_lt_two_pow m _ (by omega))),
          Nat.add_comm 1, pow_succ, mul_comm]
  have helim : Matrix.fromBlocks (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) R) 0 (-Eᵀ) 1 *
      Matrix.fromBlocks A (A * E) (Eᵀ * A) (q • (Eᵀ * A * E)) =
      Matrix.fromBlocks A (A * E) 0 ((q - 1) • (Eᵀ * A * E)) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · simp
    · simp only [Matrix.mul_assoc, Matrix.neg_mul, one_mul, sub_smul, one_smul]
      abel
  have hdet_eq := congrArg Matrix.det helim
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, one_mul, one_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Fintype.card_fin] at hdet_eq
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hblock, hdet_eq, hEtAE]
  ring

private theorem det_tailMat_poly (m k : ℕ) (hk : k ≤ 2 ^ (m + 1)) :
    (tailMat (Polynomial.X : Polynomial ℤ) (m + 1) k).det =
      (Polynomial.X : Polynomial ℤ) ^ (min k (2 ^ (m + 1) - k)) *
        (grayAndMat (Polynomial.X : Polynomial ℤ) k).det := by
  let X : Polynomial ℤ := Polynomial.X
  by_cases hk_half : k ≤ 2 ^ m
  · have hmin : min k (2 ^ (m + 1) - k) = k := by rw [pow_succ]; omega
    rw [hmin]
    have hsmul : tailMat X (m + 1) k = X • grayAndMat X k := by
      ext r s
      have hr : r.val < 2 ^ m := lt_of_lt_of_le r.isLt hk_half
      have hs : s.val < 2 ^ m := lt_of_lt_of_le s.isLt hk_half
      simp only [tailMat, grayAndMat, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [gray_reflect m r.val hr, gray_reflect m s.val hs,
        and_two_pow_add_both m _ _ (gray_lt_two_pow m r.val hr) (gray_lt_two_pow m s.val hs),
        popcount_two_pow_add m _ (lt_of_le_of_lt Nat.and_le_left (gray_lt_two_pow m r.val hr)),
        Nat.add_comm 1, pow_succ, mul_comm]
    rw [hsmul, Matrix.det_smul, Fintype.card_fin]
  · obtain ⟨j, hj_le, rfl⟩ : ∃ j ≤ 2 ^ m, k = 2 ^ m + j :=
      ⟨k - 2 ^ m, by rw [pow_succ] at hk; omega, by omega⟩
    have hmin : min (2 ^ m + j) (2 ^ (m + 1) - (2 ^ m + j)) = 2 ^ m - j := by rw [pow_succ]; omega
    rw [hmin]
    let C : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (Polynomial ℤ) := grayAndMat X (2 ^ m)
    let F : Matrix (Fin (2 ^ m)) (Fin j) (Polynomial ℤ) :=
      Matrix.of fun r s => if r.val = 2 ^ m - 1 - s.val then 1 else 0
    have hCF : ∀ r s, (C * F) r s = X ^ popcount (gray r.val &&& gray (2 ^ m - 1 - s.val)) := by
      intro r s
      have hlt : 2 ^ m - 1 - s.val < 2 ^ m := by omega
      rw [Matrix.mul_apply]
      simp only [F, Matrix.of_apply, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single ⟨2 ^ m - 1 - s.val, hlt⟩]
      · simp [C, grayAndMat]
      · intro x _ hne; simp [show x.val ≠ 2 ^ m - 1 - s.val by intro h; exact hne (Fin.ext h)]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hFtC : ∀ s r, (Fᵀ * C) s r = X ^ popcount (gray (2 ^ m - 1 - s.val) &&& gray r.val) := by
      intro s r
      have hlt : 2 ^ m - 1 - s.val < 2 ^ m := by omega
      rw [Matrix.mul_apply]
      simp only [Matrix.transpose_apply, F, Matrix.of_apply, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_eq_single ⟨2 ^ m - 1 - s.val, hlt⟩]
      · simp [C, grayAndMat]
      · intro x _ hne; simp [show x.val ≠ 2 ^ m - 1 - s.val by intro h; exact hne (Fin.ext h)]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hFtCF : Fᵀ * C * F = tailMat X m j := by
      refine Matrix.ext fun s t => ?_
      have hlt : 2 ^ m - 1 - t.val < 2 ^ m := by omega
      rw [Matrix.mul_apply]
      simp only [F, Matrix.of_apply, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single ⟨2 ^ m - 1 - t.val, hlt⟩]
      · simp only [↓reduceIte]; exact hFtC s ⟨2 ^ m - 1 - t.val, hlt⟩
      · intro x _ hne; simp [show x.val ≠ 2 ^ m - 1 - t.val by intro h; exact hne (Fin.ext h)]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hblock : (tailMat X (m + 1) (2 ^ m + j)).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (X • C) (C * F) (Fᵀ * C) (Fᵀ * C * F) := by
      ext x y
      cases x with
      | inl r =>
        cases y with
        | inl s =>
          simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, Fin.val_castAdd,
            tailMat, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, smul_eq_mul,
            C, grayAndMat]
          rw [gray_reflect m r.val r.isLt, gray_reflect m s.val s.isLt,
            and_two_pow_add_both m _ _ (gray_lt_two_pow m r.val r.isLt) (gray_lt_two_pow m s.val s.isLt),
            popcount_two_pow_add m _ (lt_of_le_of_lt Nat.and_le_left (gray_lt_two_pow m r.val r.isLt)),
            Nat.add_comm 1, pow_succ, mul_comm]
        | inr s =>
          have hsub : 2 ^ (m + 1) - 1 - (2 ^ m + s.val) = 2 ^ m - 1 - s.val := by rw [pow_succ]; omega
          simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
            Fin.val_castAdd, Fin.val_natAdd, tailMat, Matrix.of_apply, Matrix.fromBlocks_apply₁₂, hCF, hsub]
          rw [gray_reflect m r.val r.isLt, Nat.and_comm,
            and_two_pow_add_left m _ _ (gray_lt_two_pow m _ (by omega)) (gray_lt_two_pow m r.val r.isLt),
            Nat.and_comm]
      | inr s =>
        cases y with
        | inl r =>
          have hsub : 2 ^ (m + 1) - 1 - (2 ^ m + s.val) = 2 ^ m - 1 - s.val := by rw [pow_succ]; omega
          simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
            Fin.val_castAdd, Fin.val_natAdd, tailMat, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, hFtC, hsub]
          rw [gray_reflect m r.val r.isLt,
            and_two_pow_add_left m _ _ (gray_lt_two_pow m _ (by omega)) (gray_lt_two_pow m r.val r.isLt)]
        | inr t =>
          have hsub1 : 2 ^ (m + 1) - 1 - (2 ^ m + s.val) = 2 ^ m - 1 - s.val := by rw [pow_succ]; omega
          have hsub2 : 2 ^ (m + 1) - 1 - (2 ^ m + t.val) = 2 ^ m - 1 - t.val := by rw [pow_succ]; omega
          simp [Matrix.submatrix_apply, finSumFinEquiv_apply_right, Fin.val_natAdd,
            tailMat, hFtCF, hsub1, hsub2]
    have helim : Matrix.fromBlocks (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) (Polynomial ℤ)) 0
          (-Fᵀ) (X • (1 : Matrix (Fin j) (Fin j) (Polynomial ℤ))) *
        Matrix.fromBlocks (X • C) (C * F) (Fᵀ * C) (Fᵀ * C * F) =
        Matrix.fromBlocks (X • C) (C * F) 0 ((X - 1) • (Fᵀ * C * F)) := by
      rw [Matrix.fromBlocks_multiply]
      congr 1
      · simp
      · simp
      · simp
      · simp only [Matrix.mul_assoc, Matrix.neg_mul, smul_mul_assoc, one_mul, sub_smul, one_smul]
        abel
    have hdet_eq := congrArg Matrix.det helim
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul,
      Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_smul, Fintype.card_fin,
      Fintype.card_fin] at hdet_eq
    rw [← hblock, Matrix.det_submatrix_equiv_self, hFtCF] at hdet_eq
    have hrhs : X ^ (2 ^ m) * C.det * ((X - 1) ^ j * (tailMat X m j).det) =
        X ^ j * (X ^ (2 ^ m - j) * (grayAndMat X (2 ^ m + j)).det) := by
      rw [det_grayAndMat_add X m j hj_le]
      have hpow : X ^ (2 ^ m) = X ^ j * X ^ (2 ^ m - j) := by
        rw [← pow_add, show j + (2 ^ m - j) = 2 ^ m by omega]
      rw [hpow]; ring
    rw [hrhs] at hdet_eq
    have hX_ne : X ^ j ≠ 0 := pow_ne_zero j Polynomial.X_ne_zero
    exact mul_left_cancel₀ hX_ne hdet_eq

private theorem det_grayAndMat_poly (n : ℕ) :
    (grayAndMat (Polynomial.X : Polynomial ℤ) n).det =
      (Polynomial.X : Polynomial ℤ) ^ takagi n *
        ((Polynomial.X : Polynomial ℤ) - 1) ^ (grayPopSum n - takagi n) := by
  by_cases hn1 : n ≤ 1
  · interval_cases n
    · simp [grayAndMat, takagi_zero, grayPopSum]
    · simp [grayAndMat, takagi_one, grayPopSum, gray, popcount_zero]
  · let m := Nat.log 2 (n - 1)
    have hm1 : 2 ^ m ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
    have hm2 : n - 1 < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) (n - 1)
    let k := n - 2 ^ m
    have hk_le : k ≤ 2 ^ m := by rw [pow_succ] at hm2; omega
    have hk_lt : k < n := by have := Nat.two_pow_pos m; omega
    have hn_eq : n = 2 ^ m + k := by omega
    rw [hn_eq, det_grayAndMat_add _ m k hk_le, det_grayAndMat_pow2_eq]
    rw [← grayPopSum_pow2 m, grayPopSum_sub_takagi_add m k hk_le, takagi_recurrence m k hk_le]
    cases hm_eq : m with
    | zero =>
      rw [hm_eq] at hk_le hm1 hn_eq
      simp only [pow_zero] at hk_le hm1 hn_eq
      have hk1 : k = 1 := by omega
      rw [hk1]
      have htail : (tailMat (Polynomial.X : Polynomial ℤ) 0 1).det = 1 := by
        simp [tailMat, gray, popcount_zero]
      have hsum1 : grayPopSum 1 = 0 := by simp [grayPopSum, gray, popcount_zero]
      have hsum1' : grayPopSum (2 ^ 0) = 0 := by simpa using hsum1
      rw [htail, takagi_one, hsum1', hsum1]
      simp
    | succ m' =>
      rw [hm_eq] at hk_le
      rw [det_tailMat_poly m' k hk_le, det_grayAndMat_poly k]
      ring
termination_by n

theorem det_grayAndMat {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    (grayAndMat q n).det = q ^ takagi n * (q - 1) ^ (grayPopSum n - takagi n) := by
  let φ : Polynomial ℤ →+* R := (Polynomial.aeval q).toRingHom
  have hmap : φ.mapMatrix (grayAndMat Polynomial.X n) = grayAndMat q n := by
    ext i j
    simp [φ, grayAndMat]
  have hdet := RingHom.map_det φ (grayAndMat Polynomial.X n)
  rw [hmap, det_grayAndMat_poly n] at hdet
  simpa [φ] using hdet.symm

theorem det_grayAndMat_two (n : ℕ) :
    (grayAndMat (2 : ℤ) n).det = (2 : ℤ) ^ takagi n := by
  rw [det_grayAndMat (2 : ℤ) n]
  norm_num

theorem det_grayDisjointMat {R : Type*} [CommRing R] (n : ℕ) :
    (grayDisjointMat (R := R) n).det =
      if takagi n = 0 then (-1 : R) ^ grayPopSum n else 0 := by
  have heq : grayDisjointMat (R := R) n = grayAndMat (0 : R) n := by
    ext i j
    simp only [grayDisjointMat, grayAndMat, Matrix.of_apply]
    by_cases h : (gray i.val &&& gray j.val) = 0
    · simp [h, popcount_zero]
    · have hp : popcount (gray i.val &&& gray j.val) ≠ 0 := by
        intro hz; exact h ((popcount_eq_zero_iff _).mp hz)
      simp [h, zero_pow hp]
  rw [heq, det_grayAndMat (0 : R) n]
  by_cases ht : takagi n = 0
  · simp [ht]
  · simp [ht, zero_pow ht]

/-! ## Section 5: Symbolic `OR` and `XOR` Gray-Code Gram Determinant Theorems -/

private theorem poly_eq_of_aeval_rat_succ (P Q : Polynomial ℤ)
    (h : ∀ k : ℕ, Polynomial.aeval ((k + 1 : ℕ) : ℚ) P = Polynomial.aeval ((k + 1 : ℕ) : ℚ) Q) :
    P = Q := by
  let D : Polynomial ℚ := (P - Q).map (Int.castRingHom ℚ)
  have hD : D = 0 := by
    by_contra hne
    have hfin : (D.roots.toFinset : Set ℚ).Finite := Finset.finite_toSet _
    have hinf : Set.Infinite {x : ℚ | ∃ k : ℕ, x = ((k + 1 : ℕ) : ℚ)} := by
      refine Set.infinite_of_injective_forall_mem
        (f := fun k : ℕ => ((k + 1 : ℕ) : ℚ))
        (fun a b hab => by
          dsimp only at hab
          have hnat : a + 1 = b + 1 := by exact_mod_cast hab
          omega)
        (fun k => ⟨k, rfl⟩)
    have hsub : {x : ℚ | ∃ k : ℕ, x = ((k + 1 : ℕ) : ℚ)} ⊆ (D.roots.toFinset : Set ℚ) := by
      rintro x ⟨k, rfl⟩
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne,
        Polynomial.IsRoot.def, D, Polynomial.eval_map]
      have hk := h k
      simp only [Polynomial.aeval_def, Polynomial.eval₂_sub] at hk ⊢
      have heq_hom : algebraMap ℤ ℚ = Int.castRingHom ℚ := rfl
      rw [← heq_hom]
      exact sub_eq_zero.mpr hk
    exact hinf (hfin.subset hsub)
  have hmap_inj : Function.Injective (Polynomial.map (Int.castRingHom ℚ)) :=
    Polynomial.map_injective _ Int.cast_injective
  have hsub0 : P - Q = 0 := hmap_inj (by simpa [D] using hD)
  exact sub_eq_zero.mp hsub0

theorem det_grayOrMat {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    (grayOrMat q n).det = q ^ grayPopSum n * (1 - q) ^ (grayPopSum n - takagi n) := by
  have hpoly : (grayOrMat (Polynomial.X : Polynomial ℤ) n).det =
      (Polynomial.X : Polynomial ℤ) ^ grayPopSum n *
        (1 - (Polynomial.X : Polynomial ℤ)) ^ (grayPopSum n - takagi n) := by
    apply poly_eq_of_aeval_rat_succ
    intro k
    let q0 : ℚ := ((k + 1 : ℕ) : ℚ)
    have hq0 : q0 ≠ 0 := by positivity
    let φ : Polynomial ℤ →+* ℚ := (Polynomial.aeval q0).toRingHom
    have hmap : φ.mapMatrix (grayOrMat Polynomial.X n) = grayOrMat q0 n := by
      ext i j; simp [φ, grayOrMat]
    have hdet := RingHom.map_det φ (grayOrMat Polynomial.X n)
    rw [hmap] at hdet
    change φ (grayOrMat Polynomial.X n).det =
      φ (Polynomial.X ^ grayPopSum n * (1 - Polynomial.X) ^ (grayPopSum n - takagi n))
    rw [hdet]
    have hfac : grayOrMat q0 n =
        Matrix.diagonal (fun i : Fin n => q0 ^ popcount (gray i.val)) *
          grayAndMat q0⁻¹ n *
          Matrix.diagonal (fun j : Fin n => q0 ^ popcount (gray j.val)) := by
      ext i j
      simp only [grayOrMat, grayAndMat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply,
        mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      have hpop := popcount_or_add_and (gray i.val) (gray j.val)
      rw [inv_pow]
      have hne : q0 ^ popcount (gray i.val &&& gray j.val) ≠ 0 := pow_ne_zero _ hq0
      field_simp [hne]
      rw [← pow_add, ← pow_add, hpop]
    rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_grayAndMat q0⁻¹ n]
    have hprod : ∏ i : Fin n, q0 ^ popcount (gray i.val) = q0 ^ grayPopSum n := by
      rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => popcount (gray i)) n]
      rfl
    rw [hprod]
    simp only [φ, map_mul, map_pow, map_sub, map_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_X]
    have hle := takagi_le_grayPopSum n
    have h1 : q0⁻¹ - 1 = (1 - q0) * q0⁻¹ := by field_simp [hq0]
    rw [h1, mul_pow, inv_pow, inv_pow]
    have hne1 : q0 ^ takagi n ≠ 0 := pow_ne_zero _ hq0
    have hne2 : q0 ^ (grayPopSum n - takagi n) ≠ 0 := pow_ne_zero _ hq0
    field_simp [hne1, hne2]
    have hmerge :
        q0 ^ takagi n * (1 - q0) ^ (grayPopSum n - takagi n) * q0 ^ (grayPopSum n - takagi n) =
        q0 ^ (takagi n + (grayPopSum n - takagi n)) * (1 - q0) ^ (grayPopSum n - takagi n) := by
      rw [pow_add]; ring
    rw [hmerge, show takagi n + (grayPopSum n - takagi n) = grayPopSum n by omega]
  let φ : Polynomial ℤ →+* R := (Polynomial.aeval q).toRingHom
  have hmap : φ.mapMatrix (grayOrMat Polynomial.X n) = grayOrMat q n := by
    ext i j; simp [φ, grayOrMat]
  have hdet := RingHom.map_det φ (grayOrMat Polynomial.X n)
  rw [hmap, hpoly] at hdet
  simpa [φ] using hdet.symm

theorem det_grayXorMat {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    (grayXorMat q n).det = (1 - q ^ 2) ^ (grayPopSum n - takagi n) := by
  have hpoly : (grayXorMat (Polynomial.X : Polynomial ℤ) n).det =
      (1 - (Polynomial.X : Polynomial ℤ) ^ 2) ^ (grayPopSum n - takagi n) := by
    apply poly_eq_of_aeval_rat_succ
    intro k
    let q0 : ℚ := ((k + 1 : ℕ) : ℚ)
    have hq0 : q0 ≠ 0 := by positivity
    have hq2 : q0 ^ 2 ≠ 0 := pow_ne_zero 2 hq0
    let φ : Polynomial ℤ →+* ℚ := (Polynomial.aeval q0).toRingHom
    have hmap : φ.mapMatrix (grayXorMat Polynomial.X n) = grayXorMat q0 n := by
      ext i j; simp [φ, grayXorMat]
    have hdet := RingHom.map_det φ (grayXorMat Polynomial.X n)
    rw [hmap] at hdet
    change φ (grayXorMat Polynomial.X n).det =
      φ ((1 - Polynomial.X ^ 2) ^ (grayPopSum n - takagi n))
    rw [hdet]
    have hfac : grayXorMat q0 n =
        Matrix.diagonal (fun i : Fin n => q0 ^ popcount (gray i.val)) *
          grayAndMat (q0 ^ 2)⁻¹ n *
          Matrix.diagonal (fun j : Fin n => q0 ^ popcount (gray j.val)) := by
      ext i j
      simp only [grayXorMat, grayAndMat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply,
        mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      have hpop := popcount_xor_add_two_and (gray i.val) (gray j.val)
      rw [inv_pow]
      have hne : (q0 ^ 2) ^ popcount (gray i.val &&& gray j.val) ≠ 0 := pow_ne_zero _ hq2
      field_simp [hne]
      rw [← pow_mul, ← pow_add, ← pow_add, hpop]
    rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_grayAndMat (q0 ^ 2)⁻¹ n]
    have hprod : ∏ i : Fin n, q0 ^ popcount (gray i.val) = q0 ^ grayPopSum n := by
      rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => popcount (gray i)) n]
      rfl
    rw [hprod]
    simp only [φ, map_pow, map_sub, map_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_X]
    have hle := takagi_le_grayPopSum n
    have h1 : (q0 ^ 2)⁻¹ - 1 = (1 - q0 ^ 2) * (q0 ^ 2)⁻¹ := by field_simp [hq2]
    rw [h1, mul_pow, inv_pow, inv_pow]
    have hne1 : (q0 ^ 2) ^ takagi n ≠ 0 := pow_ne_zero _ hq2
    have hne2 : (q0 ^ 2) ^ (grayPopSum n - takagi n) ≠ 0 := pow_ne_zero _ hq2
    field_simp [hne1, hne2]
    simp only [← pow_mul]
    have hmerge :
        q0 ^ (2 * takagi n) * (1 - q0 ^ 2) ^ (grayPopSum n - takagi n) *
          q0 ^ (2 * (grayPopSum n - takagi n)) =
        q0 ^ (2 * takagi n + 2 * (grayPopSum n - takagi n)) *
          (1 - q0 ^ 2) ^ (grayPopSum n - takagi n) := by
      rw [pow_add]; ring
    rw [hmerge, show 2 * takagi n + 2 * (grayPopSum n - takagi n) = grayPopSum n * 2 by omega]
  let φ : Polynomial ℤ →+* R := (Polynomial.aeval q).toRingHom
  have hmap : φ.mapMatrix (grayXorMat Polynomial.X n) = grayXorMat q n := by
    ext i j; simp [φ, grayXorMat]
  have hdet := RingHom.map_det φ (grayXorMat Polynomial.X n)
  rw [hmap, hpoly] at hdet
  simpa [φ] using hdet.symm

end GrayTakagiDet
