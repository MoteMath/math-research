import Defs

namespace ClmulCarryDynamics

/-! ## Section 0: Pure-Init Bit-Level Helpers -/

private theorem getLsbD_eq_testBit {w : Nat} (x : BitVec w) (i : Nat) :
    x.getLsbD i = x.toNat.testBit i :=
  (BitVec.testBit_toNat x).symm

private theorem bv_add_right_cancel {w : Nat} {a b c : BitVec w} (h : a + c = b + c) :
    a = b := by
  grind

private theorem one_and_ne_zero_iff (n : Nat) :
    ((1 &&& n) != 0) = decide (n % 2 = 1) := by
  rw [Nat.and_comm, Nat.and_one_is_mod]
  by_cases h : n % 2 = 1 <;> simp [h] <;> omega

private theorem testBit_add_two_pow_lt (w x k : Nat) (hk : k < w) :
    (x + 2 ^ w).testBit k = x.testBit k := by
  have hm : (x + 2 ^ w) % 2 ^ w = x % 2 ^ w := by simp
  have htb := congrArg (fun n => n.testBit k) hm
  simp only [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and] at htb
  exact htb

private theorem testBit_two_pow_add_lt (w x k : Nat) (hk : k < w) :
    (2 ^ w + x).testBit k = x.testBit k := by
  rw [Nat.add_comm]
  exact testBit_add_two_pow_lt w x k hk

/-! ## Section 1: Carry-less Multiplication Basics and Bit-Level Properties -/

private theorem clmul_zero (x : Nat) : clmul 0 x = 0 := by
  unfold clmul
  simp

private theorem clmul_zero_right (a : Nat) : clmul a 0 = 0 := by
  by_cases ha : a = 0
  · subst ha; exact clmul_zero 0
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    conv => lhs; unfold clmul
    simp [ha, clmul_zero_right (a / 2)]
termination_by a

private theorem clmul_eq_of_ne_zero {a : Nat} (ha : a ≠ 0) (x : Nat) :
    clmul a x = (if a % 2 = 1 then x else 0) ^^^ (clmul (a / 2) x <<< 1) := by
  conv => lhs; unfold clmul
  simp [ha]

private theorem clmul_one_left (x : Nat) : clmul 1 x = x := by
  rw [clmul_eq_of_ne_zero (by omega)]
  simp [clmul_zero]

private theorem clmul_two_left (x : Nat) : clmul 2 x = 2 * x := by
  rw [clmul_eq_of_ne_zero (by omega)]
  simp [clmul_one_left, Nat.shiftLeft_eq, Nat.mul_comm]

private theorem clmul_three (x : Nat) : clmul 3 x = x ^^^ (2 * x) := by
  rw [clmul_eq_of_ne_zero (by omega)]
  simp [clmul_one_left, Nat.shiftLeft_eq, Nat.mul_comm]

theorem clmul_xor (a x y : Nat) :
    clmul a (x ^^^ y) = clmul a x ^^^ clmul a y := by
  by_cases ha : a = 0
  · subst ha; simp [clmul_zero]
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    rw [clmul_eq_of_ne_zero ha, clmul_eq_of_ne_zero ha, clmul_eq_of_ne_zero ha]
    rw [clmul_xor (a / 2) x y]
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hodd : a % 2 = 1 <;> simp [hodd, Nat.testBit_xor, Nat.testBit_shiftLeft] <;>
      cases x.testBit k <;> cases y.testBit k <;>
      cases (clmul (a / 2) x).testBit (k - 1) <;> cases (clmul (a / 2) y).testBit (k - 1) <;>
      cases decide (1 ≤ k) <;> rfl
termination_by a

private theorem clmul_one_right (a : Nat) : clmul a 1 = a := by
  by_cases ha : a = 0
  · subst ha; simp [clmul_zero]
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    rw [clmul_eq_of_ne_zero ha, clmul_one_right (a / 2)]
    apply Nat.eq_of_testBit_eq
    intro k
    cases k with
    | zero =>
      simp only [Nat.testBit_zero]
      by_cases hodd : a % 2 = 1 <;> simp [hodd] <;> omega
    | succ k =>
      have h1 : (1 : Nat).testBit (k + 1) = false := by rw [Nat.testBit_succ]; simp
      have hdiv : (a / 2).testBit k = a.testBit (k + 1) := by rw [Nat.testBit_succ]
      by_cases hodd : a % 2 = 1 <;>
        simp [hodd, h1, hdiv, Nat.testBit_xor, Nat.testBit_shiftLeft]
termination_by a

private theorem clmul_shiftLeft (a x k : Nat) :
    clmul a (x <<< k) = clmul a x <<< k := by
  by_cases ha : a = 0
  · subst ha; simp [clmul_zero]
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    rw [clmul_eq_of_ne_zero ha, clmul_eq_of_ne_zero ha, clmul_shiftLeft (a / 2) x k]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hodd : a % 2 = 1
    · simp only [hodd, ↓reduceIte, Nat.testBit_xor, Nat.testBit_shiftLeft]
      by_cases hk : k ≤ i
      · by_cases hk1 : k + 1 ≤ i
        · have h1 : 1 ≤ i := by omega
          have h2 : 1 ≤ i - k := by omega
          have h3 : i - 1 - k = i - k - 1 := by omega
          have h4 : k ≤ i - 1 := by omega
          simp [hk, h1, h2, h3, h4]
        · have hi : i = k := by omega
          subst hi
          by_cases h1 : 1 ≤ i
          · simp [h1, show ¬ i ≤ i - 1 by omega]
          · simp [h1]
      · by_cases h1 : 1 ≤ i
        · simp [hk, h1, show ¬ k ≤ i - 1 by omega]
        · simp [hk, h1]
    · simp only [hodd, ↓reduceIte, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.zero_testBit,
        Bool.false_xor]
      by_cases hk : k ≤ i
      · by_cases hk1 : k + 1 ≤ i
        · have h1 : 1 ≤ i := by omega
          have h2 : 1 ≤ i - k := by omega
          have h3 : i - 1 - k = i - k - 1 := by omega
          have h4 : k ≤ i - 1 := by omega
          simp [hk, h1, h2, h3, h4]
        · have hi : i = k := by omega
          subst hi
          by_cases h1 : 1 ≤ i
          · simp [h1, show ¬ i ≤ i - 1 by omega]
          · simp [h1]
      · by_cases h1 : 1 ≤ i
        · simp [hk, h1, show ¬ k ≤ i - 1 by omega]
        · simp [hk, h1]
termination_by a

private theorem clmul_testBit_of_mod_eq (w a x y : Nat)
    (hxy : ∀ k, k < w → x.testBit k = y.testBit k) :
    ∀ k, k < w → (clmul a x).testBit k = (clmul a y).testBit k := by
  by_cases ha : a = 0
  · subst ha; intro k _; simp [clmul_zero]
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    intro k hk
    rw [clmul_eq_of_ne_zero ha, clmul_eq_of_ne_zero ha]
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have hxy_k : x.testBit k = y.testBit k := hxy k hk
    by_cases h1 : 1 ≤ k
    · have ih := clmul_testBit_of_mod_eq w (a / 2) x y hxy (k - 1) (by omega)
      by_cases hodd : a % 2 = 1 <;> simp [hodd, h1, hxy_k, ih]
    · by_cases hodd : a % 2 = 1 <;> simp [hodd, h1, hxy_k]
termination_by a

private theorem clmul_mod_right (w a x : Nat) :
    clmul a x % 2 ^ w = clmul a (x % 2 ^ w) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_mod_two_pow]
  by_cases hk : k < w
  · simp only [decide_eq_true hk, Bool.true_and]
    exact clmul_testBit_of_mod_eq w a x (x % 2 ^ w)
      (fun j hj => by simp [Nat.testBit_mod_two_pow, hj]) k hk
  · simp [hk]

private theorem clmul_mod_left (w a x : Nat) :
    clmul a x % 2 ^ w = clmul (a % 2 ^ w) x % 2 ^ w := by
  induction w generalizing a with
  | zero => simp [Nat.mod_one]
  | succ w ih =>
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit_mod_two_pow]
    by_cases hk : k < w + 1
    · simp only [decide_eq_true hk, Bool.true_and]
      have hmod2 : (a % 2 ^ (w + 1)) % 2 = a % 2 := by
        have : 2 ∣ 2 ^ (w + 1) := by rw [Nat.pow_succ]; exact ⟨2 ^ w, by omega⟩
        exact Nat.mod_mod_of_dvd a this
      have hdiv2 : (a % 2 ^ (w + 1)) / 2 = (a / 2) % 2 ^ w := by
        rw [Nat.pow_succ, Nat.mod_mul_left_div_self]
      by_cases ha0 : a = 0
      · subst ha0; simp [clmul_zero]
      · by_cases ham0 : a % 2 ^ (w + 1) = 0
        · rw [ham0, clmul_zero, Nat.zero_testBit]
          have hodd : a % 2 = 0 := by omega
          have hdiv0 : (a / 2) % 2 ^ w = 0 := by rw [← hdiv2, ham0]
          rw [clmul_eq_of_ne_zero ha0]
          simp only [hodd, show ¬ (0 = 1) by omega, ↓reduceIte, Nat.testBit_xor, Nat.zero_testBit,
            Bool.false_xor, Nat.testBit_shiftLeft]
          by_cases h1 : 1 ≤ k
          · simp only [decide_eq_true h1, Bool.true_and]
            have hkm : k - 1 < w := by omega
            have hstep := ih (a / 2)
            rw [hdiv0, clmul_zero] at hstep
            have htb := congrArg (fun n => n.testBit (k - 1)) hstep
            simp only [Nat.testBit_mod_two_pow, decide_eq_true hkm, Bool.true_and, Nat.zero_testBit] at htb
            exact htb
          · simp [h1]
        · rw [clmul_eq_of_ne_zero ha0, clmul_eq_of_ne_zero ham0, hmod2, hdiv2]
          simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
          by_cases h1 : 1 ≤ k
          · simp only [decide_eq_true h1, Bool.true_and]
            have hkm : k - 1 < w := by omega
            have hstep := ih (a / 2)
            have htb := congrArg (fun n => n.testBit (k - 1)) hstep
            simp only [Nat.testBit_mod_two_pow, decide_eq_true hkm, Bool.true_and] at htb
            rw [htb]
          · simp [h1]
    · simp [hk]

private theorem clmul_zero_testBit_of_odd (w a z : Nat) (ha : a % 2 = 1)
    (h0 : clmul a z % 2 ^ w = 0) : ∀ k, k < w → z.testBit k = false := by
  have ha0 : a ≠ 0 := by omega
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    have htb := congrArg (fun n => n.testBit k) h0
    simp only [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, Nat.zero_testBit] at htb
    rw [clmul_eq_of_ne_zero ha0] at htb
    simp only [ha, ↓reduceIte, Nat.testBit_xor, Nat.testBit_shiftLeft] at htb
    by_cases h1 : 1 ≤ k
    · simp only [decide_eq_true h1, Bool.true_and] at htb
      have hzero : (clmul (a / 2) z).testBit (k - 1) = false := by
        have heq := clmul_testBit_of_mod_eq k (a / 2) z 0
          (fun j hj => by rw [ih j hj (by omega), Nat.zero_testBit]) (k - 1) (by omega)
        rw [heq]; simp [clmul_zero_right]
      rw [hzero, Bool.xor_false] at htb
      exact htb
    · simp [h1] at htb
      exact htb

private theorem clmul_zero_of_odd_mod (w a z : Nat) (ha : a % 2 = 1)
    (hz : z < 2 ^ w) (h0 : clmul a z % 2 ^ w = 0) : z = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.zero_testBit]
  by_cases hk : k < w
  · exact clmul_zero_testBit_of_odd w a z ha h0 k hk
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hz (Nat.pow_le_pow_right (by omega) (by omega)))

theorem clmul_mod_injective_of_odd (w a : Nat) (ha : a % 2 = 1) :
    ∀ x y, x < 2 ^ w → y < 2 ^ w →
      clmul a x % 2 ^ w = clmul a y % 2 ^ w → x = y := by
  intro x y hx hy heq
  have hxor_lt : x ^^^ y < 2 ^ w := Nat.xor_lt_two_pow hx hy
  have hcl0 : clmul a (x ^^^ y) % 2 ^ w = 0 := by
    rw [clmul_xor]
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.zero_testBit]
    by_cases hk : k < w
    · simp only [decide_eq_true hk, Bool.true_and]
      have htb := congrArg (fun n => n.testBit k) heq
      simp only [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and] at htb
      rw [htb, Bool.xor_self]
    · simp [hk]
  have hxy0 : x ^^^ y = 0 := clmul_zero_of_odd_mod w a (x ^^^ y) ha hxor_lt hcl0
  apply Nat.eq_of_testBit_eq
  intro k
  have htb := congrArg (fun n => n.testBit k) hxy0
  rw [Nat.testBit_xor, Nat.zero_testBit] at htb
  cases hx' : x.testBit k <;> cases hy' : y.testBit k <;> rw [hx', hy'] at htb <;> simp at htb ⊢

private theorem clmul_add_two_pow (w a x : Nat) (hx : x < 2 ^ w) :
    clmul a (x + 2 ^ w) = clmul a x ^^^ (a <<< w) := by
  have hadd : x + 2 ^ w = x ^^^ (1 <<< w) := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
    by_cases hk : k < w
    · simp [show ¬ w ≤ k by omega, testBit_add_two_pow_lt w x k hk]
    · by_cases hkw : k = w
      · subst hkw
        have hxk : x.testBit k = false := Nat.testBit_lt_two_pow hx
        have hdiv : (x + 2 ^ k) / 2 ^ k = 1 := by
          rw [Nat.add_div_right _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hx]
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
        simp [hxk]
      · have hxk : x.testBit k = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
        have hsum_lt : x + 2 ^ w < 2 ^ k := by
          have hpow : 2 ^ (w + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
          rw [Nat.pow_succ] at hpow
          omega
        have hsk : (x + 2 ^ w).testBit k = false := Nat.testBit_lt_two_pow hsum_lt
        have h1k : (1 : Nat).testBit (k - w) = false := by
          cases hdiff : k - w with
          | zero => omega
          | succ d => rw [Nat.testBit_succ]; simp
        simp [hxk, hsk, h1k]
  rw [hadd, clmul_xor, clmul_shiftLeft, clmul_one_right]

/-! ## Section 2: Pure-Init Finite Bijection & XOR-Sum Toolkit -/

private theorem surj_of_inj_range (N : Nat) :
    ∀ (g : Nat → Nat),
      (∀ i, i < N → g i < N) →
      (∀ i j, i < N → j < N → g i = g j → i = j) →
      ∀ y, y < N → ∃ i, i < N ∧ g i = y := by
  induction N with
  | zero => intro _ _ _ y hy; omega
  | succ N ih =>
    intro g hbound hinj
    have hexN : ∃ k, k < N + 1 ∧ g k = N := by
      apply Classical.byContradiction
      intro hno
      have hbound' : ∀ i, i < N → g i < N := by
        intro i hi
        have hlt := hbound i (by omega)
        have hne : g i ≠ N := fun h => hno ⟨i, by omega, h⟩
        omega
      have hinj' : ∀ i j, i < N → j < N → g i = g j → i = j :=
        fun i j hi hj heq => hinj i j (by omega) (by omega) heq
      have hsurj' := ih g hbound' hinj'
      have hgN_lt : g N < N := by
        have hlt := hbound N (by omega)
        have hne : g N ≠ N := fun h => hno ⟨N, by omega, h⟩
        omega
      rcases hsurj' (g N) hgN_lt with ⟨i, hi, heq⟩
      have hiN : i = N := hinj i N (by omega) (by omega) heq
      omega
    rcases hexN with ⟨k, hk, hgk⟩
    let g' : Nat → Nat := fun i => if i = k then g N else g i
    have hbound' : ∀ i, i < N → g' i < N := by
      intro i hi
      dsimp only [g']
      by_cases hik : i = k
      · subst hik
        have hlt := hbound N (by omega)
        have hne : g N ≠ N := by
          intro heq
          have : N = i := hinj N i (by omega) (by omega) (by rw [heq, hgk])
          omega
        simp; omega
      · simp only [hik, ↓reduceIte]
        have hlt := hbound i (by omega)
        have hne : g i ≠ N := by
          intro heq
          have : i = k := hinj i k (by omega) hk (by rw [heq, hgk])
          exact hik this
        omega
    have hinj' : ∀ i j, i < N → j < N → g' i = g' j → i = j := by
      intro i j hi hj heq
      dsimp only [g'] at heq
      by_cases hik : i = k <;> by_cases hjk : j = k
      · omega
      · simp only [hik, hjk, ↓reduceIte] at heq
        have : N = j := hinj N j (by omega) (by omega) heq
        omega
      · simp only [hik, hjk, ↓reduceIte] at heq
        have : i = N := hinj i N (by omega) (by omega) heq
        omega
      · simp only [hik, hjk, ↓reduceIte] at heq
        exact hinj i j (by omega) (by omega) heq
    have hsurj' := ih g' hbound' hinj'
    intro y hy
    by_cases hyN : y = N
    · subst hyN; exact ⟨k, hk, hgk⟩
    · rcases hsurj' y (by omega) with ⟨i, hi, hgi⟩
      dsimp only [g'] at hgi
      by_cases hik : i = k
      · simp only [hik, ↓reduceIte] at hgi
        exact ⟨N, by omega, hgi⟩
      · simp only [hik, ↓reduceIte] at hgi
        exact ⟨i, by omega, hgi⟩

private def xorRange : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, f => xor (xorRange n f) (f n)

private theorem xorRange_congr (N : Nat) (f g : Nat → Bool)
    (h : ∀ i, i < N → f i = g i) : xorRange N f = xorRange N g := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [xorRange]
    rw [ih (fun i hi => h i (by omega)), h N (by omega)]

private theorem xorRange_xor (N : Nat) (f g : Nat → Bool) :
    xorRange N (fun i => xor (f i) (g i)) = xor (xorRange N f) (xorRange N g) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [xorRange, ih]
    cases xorRange N f <;> cases xorRange N g <;> cases f N <;> cases g N <;> rfl

private theorem xorRange_const_even (n : Nat) (c : Bool) :
    xorRange (2 * n) (fun _ => c) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h2]
    simp only [xorRange, ih]
    cases c <;> rfl

private theorem xorRange_pair (n : Nat) (f : Nat → Bool) :
    xorRange (2 * n) f = xorRange n (fun k => xor (f (2 * k)) (f (2 * k + 1))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h2]
    simp only [xorRange, ih]
    cases xorRange n (fun k => xor (f (2 * k)) (f (2 * k + 1))) <;>
      cases f (2 * n) <;> cases f (2 * n + 1) <;> rfl

private theorem xorRange_update (N k : Nat) (hk : k < N) (f : Nat → Bool) (v : Bool) :
    xorRange N (fun i => if i = k then v else f i) = xor (xor (xorRange N f) (f k)) v := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [xorRange]
    by_cases hNk : N = k
    · subst hNk
      have hcongr : xorRange N (fun i => if i = N then v else f i) = xorRange N f :=
        xorRange_congr N _ _ (fun i hi => by simp [show i ≠ N by omega])
      rw [hcongr]
      simp only [↓reduceIte]
      cases xorRange N f <;> cases f N <;> cases v <;> rfl
    · simp only [hNk, ↓reduceIte]
      rw [ih (by omega)]
      cases xorRange N f <;> cases f N <;> cases f k <;> cases v <;> rfl

private theorem xorRange_bij (N : Nat) :
    ∀ (p : Nat → Nat) (f : Nat → Bool),
      (∀ i, i < N → p i < N) →
      (∀ i j, i < N → j < N → p i = p j → i = j) →
      (∀ y, y < N → ∃ i, i < N ∧ p i = y) →
      xorRange N (fun i => f (p i)) = xorRange N f := by
  induction N with
  | zero => intro _ _ _ _ _; rfl
  | succ N ih =>
    intro p f hbound hinj hsurj
    rcases hsurj N (by omega) with ⟨k, hk, hpk⟩
    by_cases hkN : k = N
    · rw [hkN] at hpk
      simp only [xorRange, hpk]
      have hbound' : ∀ i, i < N → p i < N := by
        intro i hi
        have hlt := hbound i (by omega)
        have hne : p i ≠ N := by
          intro heq
          have : i = N := hinj i N (by omega) (by omega) (by rw [heq, hpk])
          omega
        omega
      have hinj' : ∀ i j, i < N → j < N → p i = p j → i = j :=
        fun i j hi hj heq => hinj i j (by omega) (by omega) heq
      have hsurj' := surj_of_inj_range N p hbound' hinj'
      rw [ih p f hbound' hinj' hsurj']
    · let p' : Nat → Nat := fun i => if i = k then p N else p i
      have hbound' : ∀ i, i < N → p' i < N := by
        intro i hi
        dsimp only [p']
        by_cases hik : i = k
        · subst hik
          simp only [↓reduceIte]
          have hlt := hbound N (by omega)
          have hne : p N ≠ N := by
            intro heq
            have : N = i := hinj N i (by omega) (by omega) (by rw [heq, hpk])
            omega
          omega
        · simp only [hik, ↓reduceIte]
          have hlt := hbound i (by omega)
          have hne : p i ≠ N := by
            intro heq
            have : i = k := hinj i k (by omega) hk (by rw [heq, hpk])
            exact hik this
          omega
      have hinj' : ∀ i j, i < N → j < N → p' i = p' j → i = j := by
        intro i j hi hj heq
        dsimp only [p'] at heq
        by_cases hik : i = k <;> by_cases hjk : j = k
        · omega
        · simp only [hik, hjk, ↓reduceIte] at heq
          have : N = j := hinj N j (by omega) (by omega) heq
          omega
        · simp only [hik, hjk, ↓reduceIte] at heq
          have : i = N := hinj i N (by omega) (by omega) heq
          omega
        · simp only [hik, hjk, ↓reduceIte] at heq
          exact hinj i j (by omega) (by omega) heq
      have hsurj' := surj_of_inj_range N p' hbound' hinj'
      have hih := ih p' f hbound' hinj' hsurj'
      have hupd : xorRange N (fun i => f (p' i)) =
          xor (xor (xorRange N (fun i => f (p i))) (f N)) (f (p N)) := by
        have hfun : ∀ i, i < N → f (p' i) = (if i = k then f (p N) else f (p i)) := by
          intro i _
          dsimp only [p']
          by_cases hik : i = k <;> simp [hik]
        rw [xorRange_congr N _ _ hfun]
        rw [xorRange_update N k (by omega) (fun i => f (p i)) (f (p N)), hpk]
      simp only [xorRange]
      rw [← hih, hupd]
      cases xorRange N (fun i => f (p i)) <;> cases f N <;> cases f (p N) <;> rfl

private theorem xorRange_carry_threshold (M r : Nat) (hr : r ≤ M) :
    xorRange M (fun y => decide (M ≤ y + r)) = decide (r % 2 = 1) := by
  have haux : ∀ k, k ≤ M →
      xorRange k (fun y => decide (M ≤ y + r)) =
        if k ≤ M - r then false else decide ((k - (M - r)) % 2 = 1) := by
    intro k hk
    induction k with
    | zero => simp [xorRange]
    | succ k ih =>
      simp only [xorRange, ih (by omega)]
      by_cases h1 : k + 1 ≤ M - r
      · simp [h1, show k ≤ M - r by omega, show ¬ M ≤ k + r by omega]
      · by_cases h0 : k ≤ M - r
        · simp [h1, h0, show M ≤ k + r by omega, show k + 1 - (M - r) = 1 by omega]
        · have htrue : M ≤ k + r := by omega
          have hdiff : k + 1 - (M - r) = (k - (M - r)) + 1 := by omega
          simp only [h1, h0, ↓reduceIte, decide_eq_true htrue, hdiff]
          by_cases hodd : (k - (M - r)) % 2 = 1
          · simp [hodd, show ((k - (M - r)) + 1) % 2 ≠ 1 by omega]
          · simp [hodd, show ((k - (M - r)) + 1) % 2 = 1 by omega]
  have hM := haux M (Nat.le_refl M)
  by_cases hr0 : r = 0
  · subst hr0; simp [Nat.sub_zero] at hM; exact hM
  · simp [show ¬ M ≤ M - r by omega, show M - (M - r) = r by omega] at hM
    exact hM

/-! ## Section 3: Carryless–Carried Hybrid Hull–Dobell Theorem -/

private theorem iterate_succ_right {α : Type} (f : α → α) (n : Nat) (x : α) :
    iterate f (n + 1) x = f (iterate f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

private theorem iterate_add {α : Type} (f : α → α) (m n : Nat) (x : α) :
    iterate f (m + n) x = iterate f n (iterate f m x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, iterate_succ_right, iterate_succ_right, ih]

private theorem hybridStep_mod_le (a b w u x : Nat) (hu : u ≤ w) :
    hybridStep a b w x % 2 ^ u = hybridStep a b u (x % 2 ^ u) := by
  unfold hybridStep
  have hdvd : 2 ^ u ∣ 2 ^ w := Nat.pow_dvd_pow 2 hu
  rw [Nat.mod_mod_of_dvd _ hdvd]
  rw [Nat.add_mod, clmul_mod_right u a x, ← Nat.add_mod]

private theorem iterate_hybridStep_mod_le (a b w u n x : Nat) (hu : u ≤ w) :
    iterate (hybridStep a b w) n x % 2 ^ u = iterate (hybridStep a b u) n (x % 2 ^ u) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [iterate]
    rw [ih, hybridStep_mod_le a b w u x hu]

private theorem hybridStep_lt (a b w x : Nat) : hybridStep a b w x < 2 ^ w :=
  Nat.mod_lt _ (Nat.two_pow_pos w)

private theorem add_two_pow_mod_succ (w y : Nat) (hy : y < 2 ^ (w + 1)) :
    (y + 2 ^ w) % 2 ^ (w + 1) = y ^^^ 2 ^ w := by
  have h2 : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hlt : y < 2 ^ w
  · rw [Nat.mod_eq_of_lt (by omega : y + 2 ^ w < 2 ^ (w + 1))]
    by_cases hkw : k < w
    · simp [show w ≠ k by omega, testBit_add_two_pow_lt w y k hkw]
    · by_cases heq : k = w
      · subst heq
        have hyk : y.testBit k = false := Nat.testBit_lt_two_pow hlt
        have hdiv : (y + 2 ^ k) / 2 ^ k = 1 := by
          rw [Nat.add_div_right _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlt]
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
        simp [hyk]
      · have hlt2 : y + 2 ^ w < 2 ^ k := by
          have hp : 2 ^ (w + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        simp [show w ≠ k by omega, Nat.testBit_lt_two_pow (by omega : y < 2 ^ k),
          Nat.testBit_lt_two_pow hlt2]
  · have hmod : (y + 2 ^ w) % 2 ^ (w + 1) = y - 2 ^ w := by
      have hsum : y + 2 ^ w = (y - 2 ^ w) + 2 ^ (w + 1) := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    have hz : y - 2 ^ w < 2 ^ w := by omega
    have hyz : y = (y - 2 ^ w) + 2 ^ w := by omega
    by_cases hkw : k < w
    · simp only [show w ≠ k by omega, decide_false, Bool.xor_false]
      conv => rhs; rw [hyz]
      exact (testBit_add_two_pow_lt w (y - 2 ^ w) k hkw).symm
    · by_cases heq : k = w
      · subst heq
        have hzk : (y - 2 ^ k).testBit k = false := Nat.testBit_lt_two_pow hz
        have hdiv : ((y - 2 ^ k) + 2 ^ k) / 2 ^ k = 1 := by
          rw [Nat.add_div_right _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hz]
        have hyk : y.testBit k = true := by
          rw [hyz, Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]; simp
        simp [hzk, hyk]
      · have hlt2 : y < 2 ^ k := by
          have hp : 2 ^ (w + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hzk : (y - 2 ^ w).testBit k = false := Nat.testBit_lt_two_pow (by omega)
        have hyk : y.testBit k = false := Nat.testBit_lt_two_pow hlt2
        simp [show w ≠ k by omega, hzk, hyk]

private theorem hybridStep_add_two_pow (w a b x : Nat) (ha : a % 2 = 1) (hx : x < 2 ^ w) :
    hybridStep a b (w + 1) (x + 2 ^ w) = hybridStep a b (w + 1) x ^^^ 2 ^ w := by
  unfold hybridStep
  have hcl : clmul a (x + 2 ^ w) % 2 ^ (w + 1) = (clmul a x % 2 ^ (w + 1)) ^^^ 2 ^ w := by
    rw [clmul_add_two_pow w a x hx]
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_two_pow]
    by_cases hkw : k < w
    · simp [show ¬ w ≤ k by omega, show k < w + 1 by omega, show w ≠ k by omega]
    · by_cases heq : k = w
      · subst heq
        have ha0 : a.testBit 0 = true := by rw [Nat.testBit_zero]; simp [ha]
        simp [ha0]
      · simp [show ¬ k < w + 1 by omega, show w ≠ k by omega]
  have hcl2 : clmul a (x + 2 ^ w) % 2 ^ (w + 1) =
      (clmul a x % 2 ^ (w + 1) + 2 ^ w) % 2 ^ (w + 1) := by
    rw [hcl, add_two_pow_mod_succ w _ (Nat.mod_lt _ (Nat.two_pow_pos (w + 1)))]
  have hsum : (clmul a (x + 2 ^ w) + b) % 2 ^ (w + 1) =
      ((clmul a x + b) % 2 ^ (w + 1) + 2 ^ w) % 2 ^ (w + 1) := by
    have hstep1 : (clmul a (x + 2 ^ w) + b) % 2 ^ (w + 1) =
        (clmul a x + 2 ^ w + b) % 2 ^ (w + 1) := by
      rw [Nat.add_mod (clmul a (x + 2 ^ w)), hcl2]
      simp only [Nat.mod_add_mod, Nat.add_mod_mod]
    have hstep2 : (clmul a x + 2 ^ w + b) % 2 ^ (w + 1) =
        (clmul a x + b + 2 ^ w) % 2 ^ (w + 1) := by
      congr 1; omega
    have hstep3 : (clmul a x + b + 2 ^ w) % 2 ^ (w + 1) =
        ((clmul a x + b) % 2 ^ (w + 1) + 2 ^ w) % 2 ^ (w + 1) := by
      simp only [Nat.mod_add_mod]
    rw [hstep1, hstep2, hstep3]
  rw [hsum, add_two_pow_mod_succ w _ (Nat.mod_lt _ (Nat.two_pow_pos (w + 1)))]

private theorem hybridStep_topBit (w a b y : Nat) (ha : a % 2 = 1) (hy : y < 2 ^ (w + 1)) :
    (hybridStep a b (w + 1) y).testBit w =
      xor (y.testBit w) ((hybridStep a b (w + 1) (y % 2 ^ w)).testBit w) := by
  have h2 : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
  by_cases hlt : y < 2 ^ w
  · simp [Nat.testBit_lt_two_pow hlt, Nat.mod_eq_of_lt hlt]
  · have hmod : y % 2 ^ w = y - 2 ^ w := by
      have hy' : y = (y - 2 ^ w) + 2 ^ w := by omega
      conv => lhs; rw [hy']
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hy' : y = (y % 2 ^ w) + 2 ^ w := by omega
    have htb : y.testBit w = true := by
      have hdiv : y / 2 ^ w = 1 := by
        rw [hy', Nat.add_div_right _ (Nat.two_pow_pos w),
          Nat.div_eq_of_lt (Nat.mod_lt y (Nat.two_pow_pos w))]
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]; simp
    conv => lhs; rw [hy']
    rw [hybridStep_add_two_pow w a b (y % 2 ^ w) ha (Nat.mod_lt y (Nat.two_pow_pos w))]
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    simp [htb]

private theorem iterate_hybridStep_topBit (w a b k : Nat) (ha : a % 2 = 1) :
    (iterate (hybridStep a b (w + 1)) k 0).testBit w =
      xorRange k (fun i =>
        (hybridStep a b (w + 1) (iterate (hybridStep a b w) i 0)).testBit w) := by
  induction k with
  | zero => simp [iterate, xorRange]
  | succ k ih =>
    rw [iterate_succ_right]
    have hlt : iterate (hybridStep a b (w + 1)) k 0 < 2 ^ (w + 1) := by
      cases k with
      | zero => exact Nat.two_pow_pos (w + 1)
      | succ k' => rw [iterate_succ_right]; exact hybridStep_lt a b (w + 1) _
    rw [hybridStep_topBit w a b _ ha hlt, ih]
    have hmod : iterate (hybridStep a b (w + 1)) k 0 % 2 ^ w =
        iterate (hybridStep a b w) k 0 := by
      rw [iterate_hybridStep_mod_le a b (w + 1) w k 0 (by omega)]; simp
    rw [hmod]
    rfl

private theorem add_testBit_top (w u v : Nat) :
    (u + v).testBit w =
      xor (xor (u.testBit w) (v.testBit w)) (decide (2 ^ w ≤ u % 2 ^ w + v % 2 ^ w)) := by
  have hu : u = u % 2 ^ w + 2 ^ w * (u / 2 ^ w) := (Nat.mod_add_div u (2 ^ w)).symm
  have hv : v = v % 2 ^ w + 2 ^ w * (v / 2 ^ w) := (Nat.mod_add_div v (2 ^ w)).symm
  have hsum : (u + v) / 2 ^ w =
      (u / 2 ^ w) + (v / 2 ^ w) + (u % 2 ^ w + v % 2 ^ w) / 2 ^ w := by
    have h1 : u + v = (u % 2 ^ w + v % 2 ^ w) + 2 ^ w * (u / 2 ^ w + v / 2 ^ w) := by
      calc u + v = (u % 2 ^ w + 2 ^ w * (u / 2 ^ w)) + (v % 2 ^ w + 2 ^ w * (v / 2 ^ w)) := by
            rw [← hu, ← hv]
        _ = (u % 2 ^ w + v % 2 ^ w) + 2 ^ w * (u / 2 ^ w + v / 2 ^ w) := by
            rw [Nat.mul_add]; omega
    rw [h1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w)]
    omega
  have hcarry : (u % 2 ^ w + v % 2 ^ w) / 2 ^ w =
      if 2 ^ w ≤ u % 2 ^ w + v % 2 ^ w then 1 else 0 := by
    have hru : u % 2 ^ w < 2 ^ w := Nat.mod_lt u (Nat.two_pow_pos w)
    have hrv : v % 2 ^ w < 2 ^ w := Nat.mod_lt v (Nat.two_pow_pos w)
    by_cases hc : 2 ^ w ≤ u % 2 ^ w + v % 2 ^ w
    · simp only [hc, ↓reduceIte]
      have hdiv_lt : (u % 2 ^ w + v % 2 ^ w) / 2 ^ w < 2 :=
        Nat.div_lt_of_lt_mul (by omega)
      have hdiv_ge : 1 ≤ (u % 2 ^ w + v % 2 ^ w) / 2 ^ w :=
        (Nat.le_div_iff_mul_le (Nat.two_pow_pos w)).mpr (by omega)
      omega
    · simp only [hc, ↓reduceIte]
      exact Nat.div_eq_of_lt (by omega)
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hsum, hcarry]
  rw [one_and_ne_zero_iff, one_and_ne_zero_iff, one_and_ne_zero_iff]
  by_cases hc : 2 ^ w ≤ u % 2 ^ w + v % 2 ^ w <;>
    by_cases hu2 : (u / 2 ^ w) % 2 = 1 <;>
    by_cases hv2 : (v / 2 ^ w) % 2 = 1 <;>
    simp [hc, hu2, hv2] <;> omega

private theorem xorRange_clmul_topBit (w a : Nat) (hw : 2 ≤ w) :
    xorRange (2 ^ w) (fun x => (clmul a x).testBit w) = false := by
  have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
    have : w = (w - 1) + 1 := by omega
    conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
  rw [hpow, xorRange_pair]
  have hpair : ∀ k, k < 2 ^ (w - 1) →
      xor ((clmul a (2 * k)).testBit w) ((clmul a (2 * k + 1)).testBit w) = a.testBit w := by
    intro k _
    have h2k1 : 2 * k + 1 = (2 * k) ^^^ 1 := by
      apply Nat.eq_of_testBit_eq
      intro i
      cases i with
      | zero => simp [Nat.testBit_zero]
      | succ i =>
        rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        simp [show (2 * k + 1) / 2 = k by omega, show (2 * k) / 2 = k by omega]
    rw [h2k1, clmul_xor, clmul_one_right, Nat.testBit_xor]
    cases (clmul a (2 * k)).testBit w <;> cases a.testBit w <;> rfl
  rw [xorRange_congr _ _ _ hpair]
  have hpow2 : 2 ^ (w - 1) = 2 * 2 ^ (w - 2) := by
    have : w - 1 = (w - 2) + 1 := by omega
    conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
  rw [hpow2]
  exact xorRange_const_even (2 ^ (w - 2)) (a.testBit w)

private theorem hybrid_step_lift (w a b : Nat) (hw : 2 ≤ w) (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hcyc : IsFullCycle (hybridStep a b w) (2 ^ w)) :
    IsFullCycle (hybridStep a b (w + 1)) (2 ^ (w + 1)) := by
  rcases hcyc with ⟨hclose, hinj, hsurj⟩
  have hhalf_top : (iterate (hybridStep a b (w + 1)) (2 ^ w) 0).testBit w = true := by
    rw [iterate_hybridStep_topBit w a b (2 ^ w) ha]
    have hbound : ∀ i, i < 2 ^ w → iterate (hybridStep a b w) i 0 < 2 ^ w := by
      intro i _
      cases i with
      | zero => exact Nat.two_pow_pos w
      | succ i' => rw [iterate_succ_right]; exact hybridStep_lt a b w _
    rw [xorRange_bij (2 ^ w) (fun i => iterate (hybridStep a b w) i 0)
      (fun x => (hybridStep a b (w + 1) x).testBit w) hbound hinj hsurj]
    have hbit : ∀ x, x < 2 ^ w →
        (hybridStep a b (w + 1) x).testBit w =
          xor (xor ((clmul a x).testBit w) (b.testBit w))
              (decide (2 ^ w ≤ clmul a x % 2 ^ w + b % 2 ^ w)) := by
      intro x _
      unfold hybridStep
      rw [Nat.testBit_mod_two_pow]
      simp only [decide_eq_true (show w < w + 1 by omega), Bool.true_and]
      exact add_testBit_top w (clmul a x) b
    rw [xorRange_congr (2 ^ w) _ _ hbit]
    rw [xorRange_xor, xorRange_xor, xorRange_clmul_topBit w a hw]
    have hpow_even : 2 ^ w = 2 * 2 ^ (w - 1) := by
      have : w = (w - 1) + 1 := by omega
      conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
    rw [hpow_even, xorRange_const_even (2 ^ (w - 1)) (b.testBit w), ← hpow_even]
    have hcl_bound : ∀ x, x < 2 ^ w → clmul a x % 2 ^ w < 2 ^ w :=
      fun x _ => Nat.mod_lt _ (Nat.two_pow_pos w)
    have hcl_inj := clmul_mod_injective_of_odd w a ha
    have hcl_surj := surj_of_inj_range (2 ^ w) (fun x => clmul a x % 2 ^ w) hcl_bound hcl_inj
    rw [xorRange_bij (2 ^ w) (fun x => clmul a x % 2 ^ w)
      (fun y => decide (2 ^ w ≤ y + b % 2 ^ w)) hcl_bound hcl_inj hcl_surj]
    rw [xorRange_carry_threshold (2 ^ w) (b % 2 ^ w)
      (Nat.le_of_lt (Nat.mod_lt b (Nat.two_pow_pos w)))]
    have hbmod : (b % 2 ^ w) % 2 = 1 := by
      have hdvd : 2 ∣ 2 ^ w := by rw [hpow_even]; exact ⟨2 ^ (w - 1), rfl⟩
      rw [Nat.mod_mod_of_dvd b hdvd, hb]
    simp [hbmod]
  have hhalf_eq : iterate (hybridStep a b (w + 1)) (2 ^ w) 0 = 2 ^ w := by
    have hmod : iterate (hybridStep a b (w + 1)) (2 ^ w) 0 % 2 ^ w = 0 := by
      rw [iterate_hybridStep_mod_le a b (w + 1) w (2 ^ w) 0 (by omega)]
      simpa using hclose
    have hlt : iterate (hybridStep a b (w + 1)) (2 ^ w) 0 < 2 ^ (w + 1) := by
      have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
      have hpred : 2 ^ w = (2 ^ w - 1) + 1 := by omega
      rw [hpred, iterate_succ_right]; exact hybridStep_lt a b (w + 1) _
    have hdiv_lt : iterate (hybridStep a b (w + 1)) (2 ^ w) 0 / 2 ^ w < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.pow_succ] at hlt
      exact hlt
    have hdiv_odd : (iterate (hybridStep a b (w + 1)) (2 ^ w) 0 / 2 ^ w) % 2 = 1 := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, one_and_ne_zero_iff] at hhalf_top
      exact of_decide_eq_true hhalf_top
    have hdiv1 : iterate (hybridStep a b (w + 1)) (2 ^ w) 0 / 2 ^ w = 1 := by
      generalize iterate (hybridStep a b (w + 1)) (2 ^ w) 0 / 2 ^ w = q at hdiv_lt hdiv_odd
      omega
    have hdecomp := (Nat.mod_add_div (iterate (hybridStep a b (w + 1)) (2 ^ w) 0) (2 ^ w)).symm
    rw [hmod, hdiv1, Nat.zero_add, Nat.mul_one] at hdecomp
    exact hdecomp
  have hflip_step : ∀ y, y < 2 ^ (w + 1) →
      hybridStep a b (w + 1) (y ^^^ 2 ^ w) = hybridStep a b (w + 1) y ^^^ 2 ^ w := by
    intro y hy
    have h2 : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
    by_cases hlt : y < 2 ^ w
    · have hadd : y ^^^ 2 ^ w = y + 2 ^ w := by
        rw [← add_two_pow_mod_succ w y hy]
        exact Nat.mod_eq_of_lt (by omega : y + 2 ^ w < 2 ^ (w + 1))
      rw [hadd, hybridStep_add_two_pow w a b y ha hlt]
    · let z := y - 2 ^ w
      have hz : z < 2 ^ w := by omega
      have hyz : y = z + 2 ^ w := by omega
      have hxor_z : y ^^^ 2 ^ w = z := by
        rw [← add_two_pow_mod_succ w y hy]
        have hsum : y + 2 ^ w = z + 2 ^ (w + 1) := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hxor_z, hyz, hybridStep_add_two_pow w a b z ha hz]
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hflip_iter : ∀ n y, y < 2 ^ (w + 1) →
      iterate (hybridStep a b (w + 1)) n (y ^^^ 2 ^ w) =
        iterate (hybridStep a b (w + 1)) n y ^^^ 2 ^ w := by
    intro n
    induction n with
    | zero => intro y _; rfl
    | succ n ih =>
      intro y hy
      simp only [iterate]
      rw [hflip_step y hy, ih _ (hybridStep_lt a b (w + 1) y)]
  have hshift : ∀ i, iterate (hybridStep a b (w + 1)) (i + 2 ^ w) 0 =
      iterate (hybridStep a b (w + 1)) i 0 ^^^ 2 ^ w := by
    intro i
    rw [Nat.add_comm i (2 ^ w), iterate_add, hhalf_eq]
    have h0 : iterate (hybridStep a b (w + 1)) i (2 ^ w) =
        iterate (hybridStep a b (w + 1)) i (0 ^^^ 2 ^ w) := by simp
    rw [h0]
    exact hflip_iter i 0 (Nat.two_pow_pos (w + 1))
  have hpow2 : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hpow2, hshift, hhalf_eq, Nat.xor_self]
  · intro i j hi hj heq
    have hmodi : iterate (hybridStep a b (w + 1)) i 0 % 2 ^ w = iterate (hybridStep a b w) i 0 := by
      rw [iterate_hybridStep_mod_le a b (w + 1) w i 0 (by omega)]; simp
    have hmodj : iterate (hybridStep a b (w + 1)) j 0 % 2 ^ w = iterate (hybridStep a b w) j 0 := by
      rw [iterate_hybridStep_mod_le a b (w + 1) w j 0 (by omega)]; simp
    have hxor_mod : ∀ z, (z ^^^ 2 ^ w) % 2 ^ w = z % 2 ^ w := by
      intro z
      apply Nat.eq_of_testBit_eq
      intro k
      simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
      by_cases hkw : k < w
      · simp [hkw, show w ≠ k by omega]
      · simp [hkw]
    by_cases hiw : i < 2 ^ w <;> by_cases hjw : j < 2 ^ w
    · have hm := congrArg (fun n => n % 2 ^ w) heq
      rw [hmodi, hmodj] at hm
      exact hinj i j hiw hjw hm
    · have hj' : j = (j - 2 ^ w) + 2 ^ w := by omega
      have hjl : j - 2 ^ w < 2 ^ w := by omega
      rw [hj', hshift] at heq
      have hm := congrArg (fun n => n % 2 ^ w) heq
      rw [hxor_mod, hmodi] at hm
      have hmodj' : iterate (hybridStep a b (w + 1)) (j - 2 ^ w) 0 % 2 ^ w =
          iterate (hybridStep a b w) (j - 2 ^ w) 0 := by
        rw [iterate_hybridStep_mod_le a b (w + 1) w (j - 2 ^ w) 0 (by omega)]; simp
      rw [hmodj'] at hm
      have hieq : i = j - 2 ^ w := hinj i (j - 2 ^ w) hiw hjl hm
      rw [hieq] at heq
      have htb := congrArg (fun n => n.testBit w) heq
      rw [Nat.testBit_xor, Nat.testBit_two_pow] at htb
      simp at htb
    · have hi' : i = (i - 2 ^ w) + 2 ^ w := by omega
      have hil : i - 2 ^ w < 2 ^ w := by omega
      rw [hi', hshift] at heq
      have hm := congrArg (fun n => n % 2 ^ w) heq
      rw [hxor_mod, hmodj] at hm
      have hmodi' : iterate (hybridStep a b (w + 1)) (i - 2 ^ w) 0 % 2 ^ w =
          iterate (hybridStep a b w) (i - 2 ^ w) 0 := by
        rw [iterate_hybridStep_mod_le a b (w + 1) w (i - 2 ^ w) 0 (by omega)]; simp
      rw [hmodi'] at hm
      have hjeq : i - 2 ^ w = j := hinj (i - 2 ^ w) j hil hjw hm
      rw [hjeq] at heq
      have htb := congrArg (fun n => n.testBit w) heq
      rw [Nat.testBit_xor, Nat.testBit_two_pow] at htb
      simp at htb
    · have hi' : i = (i - 2 ^ w) + 2 ^ w := by omega
      have hj' : j = (j - 2 ^ w) + 2 ^ w := by omega
      have hil : i - 2 ^ w < 2 ^ w := by omega
      have hjl : j - 2 ^ w < 2 ^ w := by omega
      rw [hi', hj', hshift, hshift] at heq
      have hcancel : iterate (hybridStep a b (w + 1)) (i - 2 ^ w) 0 =
          iterate (hybridStep a b (w + 1)) (j - 2 ^ w) 0 := by
        have := congrArg (fun n => n ^^^ 2 ^ w) heq
        simpa [Nat.xor_assoc] using this
      have hm := congrArg (fun n => n % 2 ^ w) hcancel
      rw [iterate_hybridStep_mod_le a b (w + 1) w (i - 2 ^ w) 0 (by omega),
          iterate_hybridStep_mod_le a b (w + 1) w (j - 2 ^ w) 0 (by omega)] at hm
      simp at hm
      have := hinj (i - 2 ^ w) (j - 2 ^ w) hil hjl hm
      omega
  · intro y hy
    rcases hsurj (y % 2 ^ w) (Nat.mod_lt y (Nat.two_pow_pos w)) with ⟨i, hi, hfi⟩
    let v := iterate (hybridStep a b (w + 1)) i 0
    have hv_lt : v < 2 ^ (w + 1) := by
      cases i with
      | zero => exact Nat.two_pow_pos (w + 1)
      | succ i' => dsimp only [v]; rw [iterate_succ_right]; exact hybridStep_lt a b (w + 1) _
    have hv_mod : v % 2 ^ w = y % 2 ^ w := by
      dsimp only [v]
      rw [iterate_hybridStep_mod_le a b (w + 1) w i 0 (by omega)]
      simpa using hfi
    by_cases heq : v = y
    · exact ⟨i, by omega, heq⟩
    · refine ⟨i + 2 ^ w, by omega, ?_⟩
      rw [hshift]
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      by_cases hkw : k < w
      · have htb := congrArg (fun n => n.testBit k) hv_mod
        simp only [Nat.testBit_mod_two_pow, decide_eq_true hkw, Bool.true_and] at htb
        dsimp only [v] at htb
        simp [show w ≠ k by omega, htb]
      · by_cases heqw : k = w
        · subst heqw
          have hne_bit : v.testBit k ≠ y.testBit k := by
            intro hsame
            apply heq
            apply Nat.eq_of_testBit_eq
            intro m
            by_cases hmk : m < k
            · have htb := congrArg (fun n => n.testBit m) hv_mod
              simp only [Nat.testBit_mod_two_pow, decide_eq_true hmk, Bool.true_and] at htb
              exact htb
            · by_cases hmeq : m = k
              · subst hmeq; exact hsame
              · have hltv : v < 2 ^ m := Nat.lt_of_lt_of_le hv_lt (Nat.pow_le_pow_right (by omega) (by omega))
                have hlty : y < 2 ^ m := Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega))
                rw [Nat.testBit_lt_two_pow hltv, Nat.testBit_lt_two_pow hlty]
          simp
          cases hv : v.testBit k <;> cases hyb : y.testBit k <;> simp [hv, hyb] at hne_bit ⊢
        · have hltv : v < 2 ^ k := Nat.lt_of_lt_of_le hv_lt (Nat.pow_le_pow_right (by omega) (by omega))
          have hlty : y < 2 ^ k := Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega))
          rw [Nat.testBit_lt_two_pow hltv, Nat.testBit_lt_two_pow hlty]
          simp [show w ≠ k by omega]

private def hybridStepW2 (a b x : Nat) : Nat :=
  let c := match a with
    | 0 => 0
    | 1 => x
    | 2 => 2 * x
    | _ => x ^^^ (2 * x)
  (c + b) % 4

private theorem hybridStep_w2_eq (a b x : Nat) :
    hybridStep a b 2 x = hybridStepW2 (a % 4) (b % 4) (x % 4) := by
  unfold hybridStep hybridStepW2
  have h4 : (2 : Nat) ^ 2 = 4 := rfl
  rw [h4, Nat.add_mod, clmul_mod_left 2 a x, clmul_mod_right 2 (a % 4) x, h4]
  have ha4 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases ha4 with h0 | h1 | h2 | h3
  · rw [h0, clmul_zero]; simp
  · rw [h1, clmul_one_left]; simp
  · rw [h2, clmul_two_left]; simp; omega
  · rw [h3, clmul_three]; simp

private theorem iterate_hybridStep_w2_eq (a b k : Nat) :
    iterate (hybridStep a b 2) k 0 = iterate (hybridStepW2 (a % 4) (b % 4)) k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_right, iterate_succ_right, ih, hybridStep_w2_eq]
    have hlt : iterate (hybridStepW2 (a % 4) (b % 4)) k 0 < 4 := by
      cases k with
      | zero => simp [iterate]
      | succ k' => rw [iterate_succ_right]; exact Nat.mod_lt _ (by omega)
    rw [Nat.mod_eq_of_lt hlt]

private theorem w2_orbit_repeats :
    ∀ a < 4, ∀ b < 4, ∃ j, j < 4 ∧
      iterate (hybridStepW2 a b) 4 0 = iterate (hybridStepW2 a b) j 0 := by
  decide

private theorem w2_orbit_in_first4 (a b : Nat) (ha : a < 4) (hb : b < 4) :
    ∀ k, ∃ i, i < 4 ∧ iterate (hybridStepW2 a b) k 0 = iterate (hybridStepW2 a b) i 0 := by
  rcases w2_orbit_repeats a ha b hb with ⟨j, hj, hrep⟩
  intro k
  induction k with
  | zero => exact ⟨0, by omega, rfl⟩
  | succ k ih =>
    rcases ih with ⟨i, hi, heq⟩
    rw [iterate_succ_right, heq]
    have hstep : hybridStepW2 a b (iterate (hybridStepW2 a b) i 0) =
        iterate (hybridStepW2 a b) (i + 1) 0 := (iterate_succ_right (hybridStepW2 a b) i 0).symm
    rw [hstep]
    by_cases hi3 : i + 1 < 4
    · exact ⟨i + 1, hi3, rfl⟩
    · have hi4 : i + 1 = 4 := by omega
      rw [hi4, hrep]
      exact ⟨j, hj, rfl⟩

private theorem w2_surj_classification :
    ∀ a < 4, ∀ b < 4,
      (∀ y < 4, ∃ i, i < 4 ∧ iterate (hybridStepW2 a b) i 0 = y) →
      a = 1 ∧ b % 2 = 1 := by
  decide

private theorem w2_base_fullCycle (a b : Nat) (ha : a % 4 = 1) (hb : b % 2 = 1) :
    IsFullCycle (hybridStep a b 2) 4 := by
  have h1 : ∀ k, iterate (hybridStep a b 2) k 0 = iterate (hybridStepW2 1 (b % 4)) k 0 := by
    intro k; rw [iterate_hybridStep_w2_eq a b k, ha]
  have hb4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
  rcases hb4 with hb1 | hb3
  · have hiter : ∀ k, iterate (hybridStep a b 2) k 0 = iterate (hybridStepW2 1 1) k 0 := by
      intro k; rw [h1 k, hb1]
    have hinj : ∀ i < 4, ∀ j < 4,
        iterate (hybridStepW2 1 1) i 0 = iterate (hybridStepW2 1 1) j 0 → i = j := by decide
    have hsurj : ∀ x < 4, ∃ i, i < 4 ∧ iterate (hybridStepW2 1 1) i 0 = x := by decide
    refine ⟨by rw [hiter]; decide, ?_, ?_⟩
    · intro i j hi hj heq; rw [hiter i, hiter j] at heq; exact hinj i hi j hj heq
    · intro x hx; rcases hsurj x hx with ⟨i, hi, heq⟩; exact ⟨i, hi, by rw [hiter]; exact heq⟩
  · have hiter : ∀ k, iterate (hybridStep a b 2) k 0 = iterate (hybridStepW2 1 3) k 0 := by
      intro k; rw [h1 k, hb3]
    have hinj : ∀ i < 4, ∀ j < 4,
        iterate (hybridStepW2 1 3) i 0 = iterate (hybridStepW2 1 3) j 0 → i = j := by decide
    have hsurj : ∀ x < 4, ∃ i, i < 4 ∧ iterate (hybridStepW2 1 3) i 0 = x := by decide
    refine ⟨by rw [hiter]; decide, ?_, ?_⟩
    · intro i j hi hj heq; rw [hiter i, hiter j] at heq; exact hinj i hi j hj heq
    · intro x hx; rcases hsurj x hx with ⟨i, hi, heq⟩; exact ⟨i, hi, by rw [hiter]; exact heq⟩

theorem hybrid_hull_dobell_iff (w a b : Nat) (hw : 2 ≤ w) :
    IsFullCycle (hybridStep a b w) (2 ^ w) ↔ a % 4 = 1 ∧ b % 2 = 1 := by
  constructor
  · intro ⟨_, _, hsurj⟩
    have hhit : ∀ y < 4, ∃ i, i < 4 ∧ iterate (hybridStepW2 (a % 4) (b % 4)) i 0 = y := by
      intro y hy
      have hyw : y < 2 ^ w := Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hw)
      rcases hsurj y hyw with ⟨k, _, hk⟩
      have hk2 : iterate (hybridStepW2 (a % 4) (b % 4)) k 0 = y := by
        rw [← iterate_hybridStep_w2_eq a b k]
        have hm := congrArg (fun n => n % 4) hk
        rw [show (4 : Nat) = 2 ^ 2 from rfl] at hm
        rw [iterate_hybridStep_mod_le a b w 2 k 0 hw] at hm
        simpa [Nat.mod_eq_of_lt hy] using hm
      rcases w2_orbit_in_first4 (a % 4) (b % 4) (Nat.mod_lt a (by omega))
        (Nat.mod_lt b (by omega)) k with ⟨i, hi, hki⟩
      exact ⟨i, hi, by rw [← hki, hk2]⟩
    have hres := w2_surj_classification (a % 4) (Nat.mod_lt a (by omega))
      (b % 4) (Nat.mod_lt b (by omega)) hhit
    exact ⟨hres.1, by omega⟩
  · intro ⟨ha, hb⟩
    have haodd : a % 2 = 1 := by omega
    induction w with
    | zero => omega
    | succ w ih =>
      by_cases hw2 : w + 1 = 2
      · rw [hw2]; exact w2_base_fullCycle a b ha hb
      · exact hybrid_step_lift w a b (by omega) haodd hb (ih (by omega))

/-! ## Section 4: Exact `w`-Step Carry-Vector Rotation Kaprekar Sink -/

private theorem nat_carry_vec_add_two_mul (n : Nat) :
    (((n + 1) ^^^ n) ^^^ 1) + 2 + 2 * n = 2 * (n ||| (n + 1)) := by
  by_cases heven : n % 2 = 0
  · let m := n / 2
    have hn : n = 2 * m := by omega
    have hxor : (2 * m + 1) ^^^ (2 * m) = 1 := by
      apply Nat.eq_of_testBit_eq
      intro k
      cases k with
      | zero => simp [Nat.testBit_zero]
      | succ k =>
        rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        simp [show (2 * m + 1) / 2 = m by omega, show (2 * m) / 2 = m by omega]
    have hor : (2 * m) ||| (2 * m + 1) = 2 * m + 1 := by
      apply Nat.eq_of_testBit_eq
      intro k
      cases k with
      | zero => simp [Nat.testBit_zero]
      | succ k =>
        rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ]
        simp [show (2 * m + 1) / 2 = m by omega, show (2 * m) / 2 = m by omega]
    rw [hn, hxor, hor]
    simp; omega
  · have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
    let m := n / 2
    have hn : n = 2 * m + 1 := by omega
    have hsucc : n + 1 = 2 * (m + 1) := by omega
    have hxor_odd : ((m + 1) ^^^ m) % 2 = 1 := by
      have htb : ((m + 1) ^^^ m).testBit 0 = true := by
        rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero]
        by_cases hm : m % 2 = 0 <;> simp [hm] <;> omega
      rw [Nat.testBit_zero] at htb
      exact of_decide_eq_true htb
    have hxor_m_eq : (m + 1) ^^^ m = (((m + 1) ^^^ m) ^^^ 1) + 1 := by
      apply Nat.eq_of_testBit_eq
      intro k
      have h1 : (((m + 1) ^^^ m) ^^^ 1) % 2 = 0 := by
        have htb : ((((m + 1) ^^^ m) ^^^ 1)).testBit 0 = false := by
          rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero]; simp [hxor_odd]
        rw [Nat.testBit_zero] at htb
        by_cases h0 : ((((m + 1) ^^^ m) ^^^ 1)) % 2 = 0
        · exact h0
        · simp [show ((((m + 1) ^^^ m) ^^^ 1)) % 2 = 1 by omega] at htb
      let q := (((m + 1) ^^^ m) ^^^ 1) / 2
      have hq : (((m + 1) ^^^ m) ^^^ 1) = 2 * q := by omega
      cases k with
      | zero => rw [Nat.testBit_zero, Nat.testBit_zero, hq]; simp [hxor_odd]
      | succ k =>
        rw [Nat.testBit_succ, Nat.testBit_succ, hq]
        have hd1 : (2 * q + 1) / 2 = q := by omega
        have hd2 : ((m + 1) ^^^ m) / 2 = q := by
          have := congrArg (fun z => z / 2) hq
          have hdiv_xor : (((m + 1) ^^^ m) ^^^ 1) / 2 = ((m + 1) ^^^ m) / 2 := by
            apply Nat.eq_of_testBit_eq
            intro j
            rw [← Nat.testBit_succ, ← Nat.testBit_succ, Nat.testBit_xor]
            have h1j : (1 : Nat).testBit (j + 1) = false := by rw [Nat.testBit_succ]; simp
            simp [h1j]
          rw [hdiv_xor] at this
          omega
        rw [hd1, hd2]
    have hxor_n : ((n + 1) ^^^ n) ^^^ 1 = 2 * ((m + 1) ^^^ m) := by
      rw [hsucc, hn]
      apply Nat.eq_of_testBit_eq
      intro k
      cases k with
      | zero => simp [Nat.testBit_zero]
      | succ k =>
        rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ,
          Nat.testBit_succ, Nat.testBit_succ]
        simp [show (2 * (m + 1)) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega,
          show (2 * ((m + 1) ^^^ m)) / 2 = (m + 1) ^^^ m by omega, Nat.testBit_xor]
    have hor_n : n ||| (n + 1) = 2 * (m ||| (m + 1)) + 1 := by
      rw [hsucc, hn]
      apply Nat.eq_of_testBit_eq
      intro k
      cases k with
      | zero => simp [Nat.testBit_zero]
      | succ k =>
        rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        simp [show (2 * m + 1) / 2 = m by omega, show (2 * (m + 1)) / 2 = m + 1 by omega,
          show (2 * (m ||| (m + 1)) + 1) / 2 = m ||| (m + 1) by omega, Nat.testBit_or]
    have ih := nat_carry_vec_add_two_mul m
    rw [hxor_n, hor_n, hxor_m_eq, hn]
    omega
termination_by n

private theorem rotl1_toNat {w : Nat} (hw : 1 ≤ w) (x : BitVec w) :
    (x.rotateLeft 1).toNat = (2 * x.toNat + (if x.msb then 1 else 0)) % 2 ^ w := by
  by_cases hw1 : w = 1
  · subst hw1
    have hx : x = 0#1 ∨ x = 1#1 := by
      have hlt := x.isLt
      by_cases h0 : x.toNat = 0
      · left; apply BitVec.eq_of_toNat_eq; simpa using h0
      · right; apply BitVec.eq_of_toNat_eq; simp; omega
    rcases hx with rfl | rfl <;> decide
  have hw2 : 2 ≤ w := by omega
  have h1m : 1 % w = 1 := Nat.mod_eq_of_lt (by omega)
  apply Nat.eq_of_testBit_eq
  intro k
  rw [← getLsbD_eq_testBit, BitVec.getLsbD_rotateLeft, Nat.testBit_mod_two_pow]
  by_cases hkw : k < w
  · simp only [decide_eq_true hkw, Bool.true_and, h1m]
    cases k with
    | zero =>
      simp only [show 0 < 1 by omega, ↓reduceIte, Nat.add_zero, ← BitVec.msb_eq_getLsbD_last,
        Nat.testBit_zero]
      cases hmsb : x.msb <;> simp
    | succ k =>
      simp only [show ¬ k + 1 < 1 by omega, ↓reduceIte, Nat.add_sub_cancel,
        getLsbD_eq_testBit, Nat.testBit_succ]
      have hdiv : (2 * x.toNat + (if x.msb then 1 else 0)) / 2 = x.toNat := by
        cases x.msb <;> simp <;> omega
      rw [hdiv]
  · simp [hkw, h1m, show ¬ k < 1 by omega]

theorem kaprekarStep_add_one_eq {w : Nat} (hw : 1 ≤ w) (x : BitVec w) :
    kaprekarStep x + 1#w =
      (((x ||| (x + 1#w)) <<< 1) ||| (if x.msb then 1#w else 0#w)) := by
  by_cases hw1 : w = 1
  · subst hw1
    have hx : x = 0#1 ∨ x = 1#1 := by
      have hlt := x.isLt
      by_cases h0 : x.toNat = 0
      · left; apply BitVec.eq_of_toNat_eq; simpa using h0
      · right; apply BitVec.eq_of_toNat_eq; simp; omega
    rcases hx with rfl | rfl <;> decide
  have hw2 : 2 ≤ w := by omega
  have hp4 : 4 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hw2; omega
  have h1lt : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by omega)
  have hrhs : (((x ||| (x + 1#w)) <<< 1) ||| (if x.msb then 1#w else 0#w)).toNat =
      (2 * (x.toNat ||| (x + 1#w).toNat) + (if x.msb then 1 else 0)) % 2 ^ w := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [← getLsbD_eq_testBit, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, Nat.testBit_mod_two_pow]
    by_cases hkw : k < w
    · simp only [decide_eq_true hkw, Bool.true_and]
      cases k with
      | zero =>
        simp only [Nat.testBit_zero]
        cases hmsb : x.msb <;> simp [show 0 < w by omega]
      | succ k =>
        rw [Nat.testBit_succ]
        have hdiv : (2 * (x.toNat ||| (x + 1#w).toNat) + (if x.msb then 1 else 0)) / 2 =
            x.toNat ||| (x + 1#w).toNat := by
          cases x.msb <;> simp <;> omega
        rw [hdiv, Nat.testBit_or]
        have hbit0 : (if x.msb then (1#w : BitVec w) else 0#w).getLsbD (k + 1) = false := by
          cases x.msb <;> simp [BitVec.getLsbD_ofNat]
          rw [Nat.testBit_succ]; simp
        rw [hbit0]
        simp [getLsbD_eq_testBit]
    · simp [hkw, BitVec.getLsbD_of_ge _ _ (by omega : w ≤ k)]
  apply BitVec.eq_of_toNat_eq
  rw [hrhs]
  by_cases hmax : x.toNat = 2 ^ w - 1
  · have hx1 : (x + 1#w).toNat = 0 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, h1lt, hmax]
      rw [show 2 ^ w - 1 + 1 = 2 ^ w by omega, Nat.mod_self]
    have hmsb : x.msb = true := by
      rw [BitVec.msb_eq_getLsbD_last, getLsbD_eq_testBit, hmax]
      have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by
        have : w = (w - 1) + 1 := by omega
        conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
      have hpos : 0 < 2 ^ (w - 1) := Nat.two_pow_pos (w - 1)
      have hdiv_ge : 1 ≤ (2 ^ w - 1) / 2 ^ (w - 1) :=
        (Nat.le_div_iff_mul_le hpos).mpr (by omega)
      have hdiv_lt : (2 ^ w - 1) / 2 ^ (w - 1) < 2 :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      have hdiv : (2 ^ w - 1) / 2 ^ (w - 1) = 1 := by omega
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]; simp
    have hxor1 : (0 ^^^ (2 ^ w - 1)) ^^^ 1 = 2 ^ w - 2 := by
      rw [Nat.zero_xor]
      have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by
        have : w = (w - 1) + 1 := by omega
        conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_xor]
      cases k with
      | zero =>
        rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
        simp [show (2 ^ w - 1) % 2 = 1 by omega, show (2 ^ w - 2) % 2 = 0 by omega]
      | succ k =>
        have h1k : (1 : Nat).testBit (k + 1) = false := by rw [Nat.testBit_succ]; simp
        rw [h1k, Bool.xor_false, Nat.testBit_succ, Nat.testBit_succ]
        rw [show (2 ^ w - 1) / 2 = (2 ^ w - 2) / 2 by omega]
    unfold kaprekarStep
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_xor,
      hx1, hmax, BitVec.toNat_ofNat, h1lt, rotl1_toNat hw, hmax, hmsb, hxor1]
    simp only [↓reduceIte, Nat.or_zero]
    have hr1 : (2 * (2 ^ w - 1) + 1) % 2 ^ w = 2 ^ w - 1 := by
      have : 2 * (2 ^ w - 1) + 1 = (2 ^ w - 1) + 2 ^ w := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hr1]
    have h1 : (2 ^ w - 2) + (2 ^ w - 1) = (2 ^ w - 3) + 2 ^ w := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 2 ^ w - 3 < 2 ^ w)]
    rw [show 2 ^ w - 3 + 1 = 2 ^ w - 2 by omega, Nat.mod_eq_of_lt (by omega : 2 ^ w - 2 < 2 ^ w)]
    rw [show 2 ^ w - 2 + 1 = 2 ^ w - 1 by omega, Nat.mod_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ w)]
  · have hlt : x.toNat + 1 < 2 ^ w := by have := x.isLt; omega
    have hx1 : (x + 1#w).toNat = x.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, h1lt, Nat.mod_eq_of_lt hlt]
    unfold kaprekarStep
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_xor,
      hx1, BitVec.toNat_ofNat, h1lt, rotl1_toNat hw]
    have hnat := nat_carry_vec_add_two_mul x.toNat
    have hmod_simp : ∀ A B : Nat,
        (((A + B % 2 ^ w) % 2 ^ w + 1) % 2 ^ w + 1) % 2 ^ w = (A + 2 + B) % 2 ^ w := by
      intro A B
      have h1 : (A + B % 2 ^ w) % 2 ^ w = (A + B) % 2 ^ w := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [h1]
      have h2 : ((A + B) % 2 ^ w + 1) % 2 ^ w = (A + B + 1) % 2 ^ w := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [h2]
      have h3 : ((A + B + 1) % 2 ^ w + 1) % 2 ^ w = (A + B + 1 + 1) % 2 ^ w := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [h3]
      congr 1; omega
    rw [hmod_simp]
    congr 1; omega

private theorem or_succ_bits_all_one {w : Nat} (hw : 1 ≤ w) (t : Nat) (_ht : t ≤ w - 1) (y : BitVec w)
    (hy : ∀ i, 1 ≤ i → i ≤ t → (y + 1#w).getLsbD i = true) :
    ∀ j, j ≤ t → (y ||| (y + 1#w)).getLsbD j = true := by
  intro j hj
  rw [BitVec.getLsbD_or]
  by_cases hj0 : j = 0
  · subst hj0
    by_cases hy0 : y.getLsbD 0 = true
    · simp [hy0]
    · have hy0f : y.getLsbD 0 = false := by cases h : y.getLsbD 0 <;> simp [h] at hy0 ⊢
      have h1lt : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hw; omega)
      have heven : y.toNat % 2 = 0 := by
        rw [getLsbD_eq_testBit, Nat.testBit_zero] at hy0f
        by_cases h : y.toNat % 2 = 0
        · exact h
        · simp [show y.toNat % 2 = 1 by omega] at hy0f
      have hlt : y.toNat + 1 < 2 ^ w := by
        have hylt := y.isLt
        have hp_even : 2 ^ w % 2 = 0 := by
          have : w = (w - 1) + 1 := by omega
          rw [this, Nat.pow_succ]; omega
        omega
      have hy1 : (y + 1#w).getLsbD 0 = true := by
        rw [getLsbD_eq_testBit, BitVec.toNat_add, BitVec.toNat_ofNat, h1lt,
          Nat.mod_eq_of_lt hlt, Nat.testBit_zero]
        simp [show (y.toNat + 1) % 2 = 1 by omega]
      simp [hy1]
  · rw [hy j (by omega) hj]; simp

theorem kaprekarStep_image_char {w : Nat} (hw : 3 ≤ w) (t : Nat)
    (ht1 : 1 ≤ t) (ht2 : t ≤ w - 1) (y : BitVec w) :
    (∃ x : BitVec w, iterate kaprekarStep t x = y) ↔
      (∀ i, 1 ≤ i → i ≤ t → (y + 1#w).getLsbD i = true) := by
  induction t generalizing y with
  | zero => omega
  | succ t ih =>
    constructor
    · rintro ⟨x, hx⟩
      rw [iterate_succ_right] at hx
      rw [← hx, kaprekarStep_add_one_eq (by omega)]
      intro i hi1 hit
      rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
      have hil : i < w := by omega
      have hnotlt : ¬ i < 1 := by omega
      by_cases ht0 : t = 0
      · subst ht0
        have hi_eq : i = 1 := by omega
        subst hi_eq
        have h0 := or_succ_bits_all_one (by omega) 0 (by omega) x (fun _ h1 h2 => by omega) 0 (by omega)
        simp [iterate, hil, h0]
      · have hprev : ∀ j, 1 ≤ j → j ≤ t → (iterate kaprekarStep t x + 1#w).getLsbD j = true :=
          (ih (by omega) (by omega) (iterate kaprekarStep t x)).mp ⟨x, rfl⟩
        have hor := or_succ_bits_all_one (by omega) t (by omega) (iterate kaprekarStep t x) hprev (i - 1) (by omega)
        simp [hil, hnotlt, hor]
    · intro hy
      let v : BitVec w := y + 1#w
      let hiPart : BitVec w := (v >>> 1) &&& (~~~1#w)
      let msbBit : BitVec w := if v.getLsbD 0 then (1#w <<< (w - 1)) else 0#w
      let z : BitVec w := hiPart ||| msbBit
      have hbit_1w : ∀ k, (1#w : BitVec w).getLsbD k = (decide (k < w) && decide (k = 0)) := by
        intro k
        rw [BitVec.getLsbD_ofNat]
        cases k with
        | zero => simp [show 0 < w by omega]
        | succ k => simp [Nat.testBit_succ]
      have hz_bit : ∀ k, k < w →
          z.getLsbD k =
            if k = 0 then false
            else if k = w - 1 then v.getLsbD 0
            else v.getLsbD (k + 1) := by
        intro k hk
        dsimp only [z, hiPart, msbBit]
        rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not,
          hbit_1w k]
        by_cases hk0 : k = 0
        · subst hk0
          have hmsb0 : (if v.getLsbD 0 then (1#w : BitVec w) <<< (w - 1) else 0#w).getLsbD 0 = false := by
            cases v.getLsbD 0
            · simp
            · simp [BitVec.getLsbD_shiftLeft, show 0 < w - 1 by omega]
          rw [hmsb0]; simp [hk]
        · by_cases hklast : k = w - 1
          · subst hklast
            have hvge : v.getLsbD (1 + (w - 1)) = false :=
              BitVec.getLsbD_of_ge v (1 + (w - 1)) (by omega)
            have hmsb_last : (if v.getLsbD 0 then (1#w : BitVec w) <<< (w - 1) else 0#w).getLsbD (w - 1) =
                v.getLsbD 0 := by
              cases hv0 : v.getLsbD 0
              · simp
              · simp [show w - 1 < w by omega, show ¬ w - 1 < w - 1 by omega]
            rw [hmsb_last, hvge]; simp [hk0, hk]
          · have hmsb_mid : (if v.getLsbD 0 then (1#w : BitVec w) <<< (w - 1) else 0#w).getLsbD k = false := by
              cases v.getLsbD 0
              · simp
              · simp [BitVec.getLsbD_shiftLeft, show k < w - 1 by omega]
            rw [hmsb_mid]; simp [hk0, hklast, hk, Nat.add_comm]
      have hz0 : z.getLsbD 0 = false := by
        have := hz_bit 0 (by omega); simpa using this
      have hz_even : z.toNat % 2 = 0 := by
        rw [getLsbD_eq_testBit, Nat.testBit_zero] at hz0
        by_cases h : z.toNat % 2 = 0
        · exact h
        · simp [show z.toNat % 2 = 1 by omega] at hz0
      have hz_add1_bits : ∀ k, k < w →
          (z + 1#w).getLsbD k = if k = 0 then true else z.getLsbD k := by
        intro k hk
        have h1lt : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by
          have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ w); omega)
        have hlt : z.toNat + 1 < 2 ^ w := by
          have hzlt := z.isLt
          have hp_even : 2 ^ w % 2 = 0 := by
            have : w = (w - 1) + 1 := by omega
            rw [this, Nat.pow_succ]; omega
          omega
        rw [getLsbD_eq_testBit, BitVec.toNat_add, BitVec.toNat_ofNat, h1lt, Nat.mod_eq_of_lt hlt]
        cases k with
        | zero => simp [Nat.testBit_zero, show (z.toNat + 1) % 2 = 1 by omega]
        | succ k =>
          rw [getLsbD_eq_testBit, Nat.testBit_succ, Nat.testBit_succ]
          simp [show (z.toNat + 1) / 2 = z.toNat / 2 by omega]
      have hstep : kaprekarStep z = y := by
        have hadd : kaprekarStep z + 1#w = y + 1#w := by
          rw [kaprekarStep_add_one_eq (by omega)]
          apply BitVec.eq_of_getLsbD_eq
          intro k hk
          rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
          cases k with
          | zero =>
            have hmsb_z : z.msb = v.getLsbD 0 := by
              rw [BitVec.msb_eq_getLsbD_last]
              have := hz_bit (w - 1) (by omega)
              simp [show w - 1 ≠ 0 by omega] at this
              exact this
            rw [hmsb_z]
            cases hv0 : v.getLsbD 0
            · simp [v] at hv0 ⊢
            · simp [show 0 < w by omega, v] at hv0 ⊢
          | succ k =>
            have hbit_rhs : (if z.msb then (1#w : BitVec w) else 0#w).getLsbD (k + 1) = false := by
              cases z.msb <;> simp [hbit_1w]
            rw [hbit_rhs, Bool.or_false]
            simp only [decide_eq_true hk, show ¬ (k + 1 < 1) by omega, decide_false,
              Bool.not_false, Bool.true_and, Nat.add_sub_cancel]
            rw [BitVec.getLsbD_or, hz_add1_bits k (by omega)]
            by_cases hk0 : k = 0
            · subst hk0
              simp only [↓reduceIte, Bool.or_true]
              exact (hy 1 (by omega) (by omega)).symm
            · have hk_lt_last : k ≠ w - 1 := by omega
              have hzk := hz_bit k (by omega)
              simp only [hk0, hk_lt_last, ↓reduceIte] at hzk
              simp [hk0, hzk, v]
        exact bv_add_right_cancel hadd
      by_cases ht0 : t = 0
      · subst ht0; exact ⟨z, hstep⟩
      · have hz_in : ∀ i, 1 ≤ i → i ≤ t → (z + 1#w).getLsbD i = true := by
          intro i hi1 hit
          rw [hz_add1_bits i (by omega)]
          have hi0 : i ≠ 0 := by omega
          have hilast : i ≠ w - 1 := by omega
          simp only [hi0, ↓reduceIte]
          rw [hz_bit i (by omega)]
          simp only [hi0, hilast, ↓reduceIte]
          exact hy (i + 1) (by omega) (by omega)
        rcases (ih (by omega) (by omega) z).mpr hz_in with ⟨x, hx⟩
        exact ⟨x, by rw [iterate_succ_right, hx, hstep]⟩

theorem kaprekarStep_universal_sink {w : Nat} (hw : 3 ≤ w) :
    (∀ x : BitVec w, iterate kaprekarStep w x = ~~~1#w) ∧
    iterate kaprekarStep (w - 1) 0#w ≠ ~~~1#w ∧
    kaprekarStep (~~~1#w) = ~~~1#w := by
  have hp4 : 4 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 2 ≤ w); omega
  have h1lt : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by omega)
  have hallOnes_add : (~~~1#w : BitVec w) + 1#w = BitVec.allOnes w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat, h1lt, BitVec.toNat_allOnes]
    rw [show 2 ^ w - 1 - 1 + 1 = 2 ^ w - 1 by omega, Nat.mod_eq_of_lt (by omega)]
  have hfix : kaprekarStep (~~~1#w) = ~~~1#w := by
    have hadd : kaprekarStep (~~~1#w) + 1#w = (~~~1#w) + 1#w := by
      rw [kaprekarStep_add_one_eq (by omega), hallOnes_add]
      have hmsb : (~~~1#w : BitVec w).msb = true := by
        rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
        have h1 : (1 : Nat).testBit (w - 1) = false := by
          cases hd : w - 1 with
          | zero => omega
          | succ d => rw [Nat.testBit_succ]; simp
        simp [show w - 1 < w by omega, h1]
      rw [hmsb]
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
      cases k with
      | zero => simp [hk]
      | succ k =>
        simp [hk, show k < w by omega]
    exact bv_add_right_cancel hadd
  have hcollapse : ∀ x : BitVec w, iterate kaprekarStep w x = ~~~1#w := by
    intro x
    have hw_eq : w = (w - 1) + 1 := by omega
    have hiter_eq : iterate (@kaprekarStep w) w x = kaprekarStep (iterate (@kaprekarStep w) (w - 1) x) := by
      rw [← iterate_succ_right (@kaprekarStep w) (w - 1) x]
      congr 1
    rw [hiter_eq]
    let y := iterate kaprekarStep (w - 1) x
    have hy_bits : ∀ i, 1 ≤ i → i ≤ w - 1 → (y + 1#w).getLsbD i = true :=
      (kaprekarStep_image_char hw (w - 1) (by omega) (by omega) y).mp ⟨x, rfl⟩
    have hy_msb : y.msb = true := by
      rw [BitVec.msb_eq_getLsbD_last]
      have hv_ge : 2 ^ w - 2 ≤ (y + 1#w).toNat := by
        have hor_val : (y + 1#w).toNat ||| 1 = 2 ^ w - 1 := by
          apply Nat.eq_of_testBit_eq
          intro k
          by_cases hkw : k < w
          · have h2m1 : (2 ^ w - 1).testBit k = true := by
              rw [← BitVec.toNat_allOnes, ← getLsbD_eq_testBit, BitVec.getLsbD_allOnes]
              simp [hkw]
            rw [h2m1, Nat.testBit_or]
            cases k with
            | zero => simp [Nat.testBit_zero]
            | succ k =>
              rw [← getLsbD_eq_testBit, hy_bits (k + 1) (by omega) (by omega)]
              simp
          · have h1lt' : (y + 1#w).toNat < 2 ^ k :=
              Nat.lt_of_lt_of_le (y + 1#w).isLt (Nat.pow_le_pow_right (by omega) (by omega))
            have h2lt' : 2 ^ w - 1 < 2 ^ k := by
              have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : w ≤ k); omega
            have h1k : (1 : Nat).testBit k = false := by
              cases k with
              | zero => omega
              | succ k => rw [Nat.testBit_succ]; simp
            rw [Nat.testBit_or, Nat.testBit_lt_two_pow h1lt', Nat.testBit_lt_two_pow h2lt', h1k]
            rfl
        have hle : (y + 1#w).toNat ||| 1 ≤ (y + 1#w).toNat + 1 := by
          generalize (y + 1#w).toNat = q
          have hq : q ||| 1 = if q % 2 = 0 then q + 1 else q := by
            apply Nat.eq_of_testBit_eq
            intro k
            cases k with
            | zero =>
              rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero]
              by_cases he : q % 2 = 0 <;> simp [he, Nat.testBit_zero] <;> omega
            | succ k =>
              rw [Nat.testBit_or]
              have h1k : (1 : Nat).testBit (k + 1) = false := by rw [Nat.testBit_succ]; simp
              rw [h1k, Bool.or_false]
              by_cases he : q % 2 = 0
              · simp only [he, ↓reduceIte, Nat.testBit_succ]
                rw [show (q + 1) / 2 = q / 2 by omega]
              · simp [he]
          rw [hq]; by_cases h : q % 2 = 0 <;> simp [h] <;> omega
        omega
      have hy_ge : 2 ^ (w - 1) ≤ y.toNat := by
        have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by
          have : w = (w - 1) + 1 := by omega
          conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
        have hp_half : 4 ≤ 2 ^ (w - 1) := by
          have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 2 ≤ w - 1); omega
        by_cases hmax : y.toNat = 2 ^ w - 1
        · omega
        · have hlt : y.toNat + 1 < 2 ^ w := by have := y.isLt; omega
          have hadd1 : (y + 1#w).toNat = y.toNat + 1 := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, h1lt, Nat.mod_eq_of_lt hlt]
          omega
      rw [getLsbD_eq_testBit, Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hdiv : y.toNat / 2 ^ (w - 1) = 1 := by
        have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by
          have : w = (w - 1) + 1 := by omega
          conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
        have hlt := y.isLt
        have hpos : 0 < 2 ^ (w - 1) := Nat.two_pow_pos (w - 1)
        have hle1 : 1 ≤ y.toNat / 2 ^ (w - 1) :=
          (Nat.le_div_iff_mul_le hpos).mpr (by omega)
        have hlt2 : y.toNat / 2 ^ (w - 1) < 2 :=
          Nat.div_lt_of_lt_mul (by omega)
        omega
      rw [hdiv]; simp
    have hadd : kaprekarStep y + 1#w = (~~~1#w) + 1#w := by
      rw [kaprekarStep_add_one_eq (by omega), hy_msb, hallOnes_add]
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
      cases k with
      | zero => simp [hk]
      | succ k =>
        have hor := or_succ_bits_all_one (by omega) (w - 1) (by omega) y hy_bits k (by omega)
        simp [hk, hor]
    exact bv_add_right_cancel hadd
  have hdiam : iterate kaprekarStep (w - 1) 0#w ≠ ~~~1#w := by
    have hzero_inv : ∀ t, t ≤ w - 1 →
        (iterate kaprekarStep t 0#w + 1#w).getLsbD 0 = decide (t = 0) ∧
        ∀ j, t + 1 ≤ j → j < w → (iterate kaprekarStep t 0#w + 1#w).getLsbD j = false := by
      intro t
      induction t with
      | zero =>
        intro _
        simp only [iterate, BitVec.zero_add]
        constructor
        · rw [BitVec.getLsbD_ofNat]; simp [show 0 < w by omega]
        · intro j hj1 _
          rw [BitVec.getLsbD_ofNat]
          cases j with
          | zero => omega
          | succ j => simp [Nat.testBit_succ]
      | succ t ih =>
        intro ht
        rcases ih (by omega) with ⟨h0, hhi⟩
        let u := iterate kaprekarStep t 0#w
        have hu_top : (u + 1#w).getLsbD (w - 1) = false := hhi (w - 1) (by omega) (by omega)
        have hu_ne_max : u.toNat ≠ 2 ^ w - 1 := by
          intro hmax
          have hu1 : (u + 1#w).toNat = 0 := by
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, h1lt, hmax]
            rw [show 2 ^ w - 1 + 1 = 2 ^ w by omega, Nat.mod_self]
          by_cases ht0 : t = 0
          · subst ht0
            have : (u + 1#w).getLsbD 0 = false := by rw [getLsbD_eq_testBit, hu1]; simp
            rw [this] at h0; simp at h0
          · have hb1 : (u + 1#w).getLsbD 1 = true :=
              (kaprekarStep_image_char hw t (by omega) (by omega) u).mp ⟨0#w, rfl⟩ 1 (by omega) (by omega)
            have : (u + 1#w).getLsbD 1 = false := by rw [getLsbD_eq_testBit, hu1]; simp
            rw [this] at hb1; exact Bool.false_ne_true hb1
        have hu1_nat : (u + 1#w).toNat = u.toNat + 1 := by
          have hlt : u.toNat + 1 < 2 ^ w := by have := u.isLt; omega
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, h1lt, Nat.mod_eq_of_lt hlt]
        have hu_msb : u.msb = false := by
          rw [BitVec.msb_eq_getLsbD_last]
          have hu1_lt_half : (u + 1#w).toNat < 2 ^ (w - 1) := by
            rw [getLsbD_eq_testBit, Nat.testBit, Nat.shiftRight_eq_div_pow] at hu_top
            have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by
              have : w = (w - 1) + 1 := by omega
              conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
            have hlt' := (u + 1#w).isLt
            have hdiv_lt : (u + 1#w).toNat / 2 ^ (w - 1) < 2 :=
              Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
            have hdiv0 : (u + 1#w).toNat / 2 ^ (w - 1) = 0 := by
              generalize (u + 1#w).toNat / 2 ^ (w - 1) = q at hdiv_lt hu_top
              by_cases h1 : q = 1
              · rw [h1] at hu_top; simp at hu_top
              · omega
            exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos (w - 1))).mp hdiv0
          rw [getLsbD_eq_testBit]
          exact Nat.testBit_lt_two_pow (by omega : u.toNat < 2 ^ (w - 1))
        rw [iterate_succ_right, kaprekarStep_add_one_eq (by omega), hu_msb]
        simp only [Bool.false_eq_true, ↓reduceIte, BitVec.or_zero]
        constructor
        · simp [BitVec.getLsbD_shiftLeft]
        · intro j hj1 hjw
          rw [BitVec.getLsbD_shiftLeft]
          simp only [decide_eq_true hjw, show ¬ j < 1 by omega, decide_false, Bool.not_false,
            Bool.true_and, BitVec.getLsbD_or]
          have hhi_u1 : (u + 1#w).getLsbD (j - 1) = false := hhi (j - 1) (by omega) (by omega)
          have hhi_u : u.getLsbD (j - 1) = false := by
            have hu1_lt : (u + 1#w).toNat < 2 ^ (j - 1) := by
              have hdiv0 : (u + 1#w).toNat / 2 ^ (j - 1) = 0 := by
                apply Nat.eq_of_testBit_eq
                intro m
                rw [Nat.zero_testBit, Nat.testBit_div_two_pow]
                by_cases hm : m + (j - 1) < w
                · rw [← getLsbD_eq_testBit]
                  exact hhi (m + (j - 1)) (by omega) hm
                · exact Nat.testBit_lt_two_pow
                    (Nat.lt_of_lt_of_le (u + 1#w).isLt (Nat.pow_le_pow_right (by omega) (by omega)))
              exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos (j - 1))).mp hdiv0
            rw [getLsbD_eq_testBit]
            exact Nat.testBit_lt_two_pow (by omega)
          rw [hhi_u, hhi_u1]; rfl
    intro heq
    have hbit0 := (hzero_inv (w - 1) (Nat.le_refl _)).1
    rw [heq, hallOnes_add, BitVec.getLsbD_allOnes] at hbit0
    simp [show 0 < w by omega, show w - 1 ≠ 0 by omega] at hbit0
  exact ⟨hcollapse, hdiam, hfix⟩

theorem kaprekarStep_w2_sharpness :
    kaprekarStep 1#2 = 1#2 ∧ kaprekarStep 2#2 = 2#2 ∧ (1#2 : BitVec 2) ≠ 2#2 := by
  decide

/-! ## Section 5: Exact `m = 3` Carried-vs-Carryless Twin Laws -/

private theorem add_eq_xor_add_two_and (a b : Nat) :
    a + b = (a ^^^ b) + 2 * (a &&& b) := by
  by_cases ha : a = 0
  · subst ha; simp
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    have ih := add_eq_xor_add_two_and (a / 2) (b / 2)
    have hxor_div : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
      apply Nat.eq_of_testBit_eq
      intro k; rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor,
        Nat.testBit_succ, Nat.testBit_succ]
    have hxor_mod : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
      have htb : (a ^^^ b).testBit 0 = ((a % 2) ^^^ (b % 2)).testBit 0 := by
        rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero,
          Nat.testBit_zero, Nat.testBit_zero]; simp
      rw [Nat.testBit_zero, Nat.testBit_zero] at htb
      have h1 : (a % 2) ^^^ (b % 2) < 2 :=
        Nat.xor_lt_two_pow (n := 1) (Nat.mod_lt a (by omega)) (Nat.mod_lt b (by omega))
      by_cases h : (a ^^^ b) % 2 = 1 <;> by_cases h' : ((a % 2) ^^^ (b % 2)) % 2 = 1 <;>
        simp [h, h'] at htb <;> omega
    have hand_div : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
      apply Nat.eq_of_testBit_eq
      intro k; rw [← Nat.testBit_succ, Nat.testBit_and, Nat.testBit_and,
        Nat.testBit_succ, Nat.testBit_succ]
    have hand_mod : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
      have htb : (a &&& b).testBit 0 = ((a % 2) &&& (b % 2)).testBit 0 := by
        rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero,
          Nat.testBit_zero, Nat.testBit_zero]; simp
      rw [Nat.testBit_zero, Nat.testBit_zero] at htb
      have h1 : (a % 2) &&& (b % 2) < 2 :=
        Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt a (by omega))
      by_cases h : (a &&& b) % 2 = 1 <;> by_cases h' : ((a % 2) &&& (b % 2)) % 2 = 1 <;>
        simp [h, h'] at htb <;> omega
    have hbit : a % 2 + b % 2 = ((a % 2) ^^^ (b % 2)) + 2 * ((a % 2) &&& (b % 2)) := by
      have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2 <;> rw [ha2, hb2] <;> decide
    have hda := Nat.div_add_mod a 2
    have hdb := Nat.div_add_mod b 2
    have hdx := Nat.div_add_mod (a ^^^ b) 2
    have hdn := Nat.div_add_mod (a &&& b) 2
    rw [hxor_div, hxor_mod] at hdx
    rw [hand_div, hand_mod] at hdn
    omega
termination_by a

theorem carried_eq_clmul3_iff (x : Nat) :
    3 * x = clmul 3 x ↔ (x &&& (2 * x)) = 0 := by
  rw [clmul_three, show 3 * x = x + 2 * x by omega]
  have h := add_eq_xor_add_two_and x (2 * x)
  omega

private theorem sumNat_add (m n : Nat) (f : Nat → Nat) :
    sumNat (m + n) f = sumNat m f + sumNat n (fun i => f (m + i)) := by
  induction n with
  | zero => simp [sumNat]
  | succ n ih =>
    rw [← Nat.add_assoc, sumNat, sumNat, ih]
    omega

private theorem sumNat_congr (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i = g i) : sumNat n f = sumNat n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumNat, ih (fun i hi => h i (by omega)), h n (by omega)]

private theorem sumNat_zero (n : Nat) (f : Nat → Nat)
    (h : ∀ i, i < n → f i = 0) : sumNat n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [sumNat, ih (fun i hi => h i (by omega)), h n (by omega)]

private theorem zeroCarry3Count_step (w : Nat) :
    zeroCarry3Count (w + 2) = zeroCarry3Count (w + 1) + zeroCarry3Count w := by
  unfold zeroCarry3Count
  have hp1 : 2 ^ (w + 2) = 2 ^ (w + 1) + 2 ^ (w + 1) := by rw [Nat.pow_succ]; omega
  have hp2 : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
  rw [hp1, sumNat_add]
  congr 1
  have hsplit : sumNat (2 ^ (w + 1)) (fun i =>
      if 3 * (2 ^ (w + 1) + i) = clmul 3 (2 ^ (w + 1) + i) then 1 else 0) =
      sumNat (2 ^ w) (fun i =>
        if 3 * (2 ^ (w + 1) + i) = clmul 3 (2 ^ (w + 1) + i) then 1 else 0) +
      sumNat (2 ^ w) (fun j =>
        if 3 * (2 ^ (w + 1) + (2 ^ w + j)) = clmul 3 (2 ^ (w + 1) + (2 ^ w + j)) then 1 else 0) := by
    conv => lhs; arg 1; rw [hp2]
    exact sumNat_add (2 ^ w) (2 ^ w) _
  rw [hsplit]
  have hmid : sumNat (2 ^ w) (fun i =>
      if 3 * (2 ^ (w + 1) + i) = clmul 3 (2 ^ (w + 1) + i) then 1 else 0) =
      sumNat (2 ^ w) (fun i => if 3 * i = clmul 3 i then 1 else 0) := by
    apply sumNat_congr
    intro i hi
    have hiff : 3 * (2 ^ (w + 1) + i) = clmul 3 (2 ^ (w + 1) + i) ↔ 3 * i = clmul 3 i := by
      rw [carried_eq_clmul3_iff, carried_eq_clmul3_iff]
      have hdisj : ((2 ^ (w + 1) + i) &&& (2 * (2 ^ (w + 1) + i))) = (i &&& (2 * i)) := by
        apply Nat.eq_of_testBit_eq
        intro k
        rw [Nat.testBit_and, Nat.testBit_and]
        have h2i_lt : 2 * i < 2 ^ (w + 1) := by rw [hp2]; omega
        have hi_lt : i < 2 ^ (w + 1) := by omega
        have htop_i : (2 ^ (w + 1) + i).testBit k =
            if k = w + 1 then true else if k < w + 1 then i.testBit k else false := by
          by_cases hkw : k < w + 1
          · simp [hkw, show k ≠ w + 1 by omega, testBit_two_pow_add_lt (w + 1) i k hkw]
          · by_cases heq : k = w + 1
            · subst heq
              have hdiv : (2 ^ (w + 1) + i) / 2 ^ (w + 1) = 1 := by
                rw [Nat.add_comm, Nat.add_div_right _ (Nat.two_pow_pos (w + 1)), Nat.div_eq_of_lt hi_lt]
              rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]; simp
            · have hlt2 : 2 ^ (w + 1) + i < 2 ^ k := by
                have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : w + 2 ≤ k)
                rw [hp1] at this; omega
              simp [hkw, heq, Nat.testBit_lt_two_pow hlt2]
        have htop_2i : (2 * (2 ^ (w + 1) + i)).testBit k =
            if k = w + 2 then true else if k < w + 1 then (2 * i).testBit k else false := by
          have hmul : 2 * (2 ^ (w + 1) + i) = 2 ^ (w + 2) + 2 * i := by rw [hp1]; omega
          rw [hmul]
          by_cases hkw : k < w + 1
          · simp [hkw, show k ≠ w + 2 by omega, testBit_two_pow_add_lt (w + 2) (2 * i) k (by omega)]
          · by_cases heq : k = w + 2
            · subst heq
              have hdiv : (2 ^ (w + 2) + 2 * i) / 2 ^ (w + 2) = 1 := by
                rw [Nat.add_comm, Nat.add_div_right _ (Nat.two_pow_pos (w + 2)),
                  Nat.div_eq_of_lt (by omega : 2 * i < 2 ^ (w + 2))]
              rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]; simp
            · by_cases hkw1 : k = w + 1
              · subst hkw1
                have hdiv : (2 ^ (w + 2) + 2 * i) / 2 ^ (w + 1) = 2 := by
                  have h1 : 2 ^ (w + 2) + 2 * i = 2 * i + 2 ^ (w + 1) * 2 := by rw [hp1]; omega
                  rw [h1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos (w + 1)), Nat.div_eq_of_lt h2i_lt]
                rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]; simp
              · have hlt2 : 2 ^ (w + 2) + 2 * i < 2 ^ k := by
                  have h3 : 2 ^ (w + 3) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
                  rw [Nat.pow_succ] at h3; omega
                simp [hkw, heq, Nat.testBit_lt_two_pow hlt2]
        rw [htop_i, htop_2i]
        by_cases hkw : k < w + 1
        · simp [hkw, show k ≠ w + 1 by omega, show k ≠ w + 2 by omega]
        · have hi_f : i.testBit k = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi_lt (Nat.pow_le_pow_right (by omega) (by omega)))
          rw [hi_f, Bool.false_and]
          by_cases hk1 : k = w + 1
          · simp [hk1]
          · simp [hkw, hk1]
      rw [hdisj]
    by_cases h : 3 * i = clmul 3 i <;> simp [hiff, h]
  have hhi : sumNat (2 ^ w) (fun j =>
      if 3 * (2 ^ (w + 1) + (2 ^ w + j)) = clmul 3 (2 ^ (w + 1) + (2 ^ w + j)) then 1 else 0) = 0 := by
    apply sumNat_zero
    intro j hj
    have hne : 3 * (2 ^ (w + 1) + (2 ^ w + j)) ≠ clmul 3 (2 ^ (w + 1) + (2 ^ w + j)) := by
      intro h0
      rw [carried_eq_clmul3_iff] at h0
      have htb := congrArg (fun n => n.testBit (w + 1)) h0
      rw [Nat.testBit_and, Nat.zero_testBit] at htb
      have h1 : (2 ^ (w + 1) + (2 ^ w + j)).testBit (w + 1) = true := by
        have hlt : 2 ^ w + j < 2 ^ (w + 1) := by rw [hp2]; omega
        have hdiv : (2 ^ (w + 1) + (2 ^ w + j)) / 2 ^ (w + 1) = 1 := by
          rw [Nat.add_comm, Nat.add_div_right _ (Nat.two_pow_pos (w + 1)), Nat.div_eq_of_lt hlt]
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]; simp
      have h2 : (2 * (2 ^ (w + 1) + (2 ^ w + j))).testBit (w + 1) = true := by
        have hmul : 2 * (2 ^ (w + 1) + (2 ^ w + j)) = 2 * j + 2 ^ (w + 1) * 3 := by rw [hp2]; omega
        have h2j : 2 * j < 2 ^ (w + 1) := by rw [hp2]; omega
        have hdiv : (2 * (2 ^ (w + 1) + (2 ^ w + j))) / 2 ^ (w + 1) = 3 := by
          rw [hmul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos (w + 1)), Nat.div_eq_of_lt h2j]
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]; simp
      rw [h1, h2] at htb; simp at htb
    simp [hne]
  rw [hmid, hhi, Nat.add_zero]

theorem zeroCarry3Count_eq_fib (w : Nat) :
    zeroCarry3Count w = fib (w + 2) := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
    match w with
    | 0 => simp [zeroCarry3Count, sumNat, clmul_three, fib]
    | 1 => simp [zeroCarry3Count, sumNat, clmul_three, fib]
    | w + 2 =>
      rw [zeroCarry3Count_step w, ih (w + 1) (by omega), ih w (by omega)]
      rfl

/-! ### Exact 3-State Recurrence for `clmul3ParitySum` -/

private theorem popcount_eq_mod_add_div (n : Nat) :
    popcount n = n % 2 + popcount (n / 2) := by
  by_cases hn : n = 0
  · subst hn; unfold popcount; simp
  · conv => lhs; unfold popcount
    simp [hn]

private theorem popcount_zero : popcount 0 = 0 := by
  unfold popcount; simp

private theorem popcount_one : popcount 1 = 1 := by
  rw [popcount_eq_mod_add_div 1]; simp [popcount_zero]

private theorem popcount_two : popcount 2 = 1 := by
  rw [popcount_eq_mod_add_div 2]; simp [popcount_one]

private theorem popcount_three : popcount 3 = 2 := by
  rw [popcount_eq_mod_add_div 3]; simp [popcount_one]

private theorem popcount_two_mul (n : Nat) :
    popcount (2 * n) = popcount n := by
  rw [popcount_eq_mod_add_div (2 * n)]
  simp [show (2 * n) % 2 = 0 by omega, show (2 * n) / 2 = n by omega]

private theorem popcount_two_mul_add_one (n : Nat) :
    popcount (2 * n + 1) = 1 + popcount n := by
  rw [popcount_eq_mod_add_div (2 * n + 1)]
  simp [show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega]

private theorem popcount_xor_parity (a b : Nat) :
    (popcount a + popcount b) % 2 = popcount (a ^^^ b) % 2 := by
  by_cases ha : a = 0
  · subst ha; simp [popcount_zero]
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    have ih := popcount_xor_parity (a / 2) (b / 2)
    rw [popcount_eq_mod_add_div a, popcount_eq_mod_add_div b, popcount_eq_mod_add_div (a ^^^ b)]
    have hxor_div : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
      apply Nat.eq_of_testBit_eq
      intro k; rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor,
        Nat.testBit_succ, Nat.testBit_succ]
    have hxor_mod : (a ^^^ b) % 2 = (a % 2 + b % 2) % 2 := by
      have htb : (a ^^^ b).testBit 0 = ((a % 2) ^^^ (b % 2)).testBit 0 := by
        rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero,
          Nat.testBit_zero, Nat.testBit_zero]; simp
      rw [Nat.testBit_zero, Nat.testBit_zero] at htb
      have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2 <;>
        rw [ha2, hb2] at htb ⊢ <;>
        (by_cases h : (a ^^^ b) % 2 = 1 <;> simp [h] at htb <;> omega)
    rw [hxor_div, hxor_mod]
    omega
termination_by a

private theorem paritySign_xor_one (n : Nat) :
    paritySign (popcount (n ^^^ 1)) = -paritySign (popcount n) := by
  unfold paritySign
  have hp := popcount_xor_parity n 1
  rw [popcount_one] at hp
  by_cases h : popcount n % 2 = 0
  · simp [h, show popcount (n ^^^ 1) % 2 = 1 by omega]
  · simp [h, show popcount (n ^^^ 1) % 2 = 0 by omega]

private theorem paritySign_two_mul_add_one (n : Nat) :
    paritySign (popcount (2 * n + 1)) = -paritySign (popcount n) := by
  rw [popcount_two_mul_add_one]
  unfold paritySign
  by_cases h : popcount n % 2 = 0
  · simp [h, show (1 + popcount n) % 2 = 1 by omega]
  · simp [h, show (1 + popcount n) % 2 = 0 by omega]

private theorem sumInt_congr (n : Nat) (f g : Nat → Int)
    (h : ∀ i, i < n → f i = g i) : sumInt n f = sumInt n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumInt, ih (fun i hi => h i (by omega)), h n (by omega)]

private theorem sumInt_pair (n : Nat) (f : Nat → Int) :
    sumInt (2 * n) f = sumInt n (fun y => f (2 * y)) + sumInt n (fun y => f (2 * y + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h2, sumInt, sumInt, sumInt, sumInt, ih]
    omega

private theorem sumInt_neg (n : Nat) (f : Nat → Int) :
    sumInt n (fun y => -f y) = -sumInt n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumInt, ih]; omega

private def s0 (w : Nat) : Int :=
  sumInt (2 ^ w) (fun x => paritySign (popcount ((3 * x) ^^^ clmul 3 x)))

private def s1 (w : Nat) : Int :=
  sumInt (2 ^ w) (fun x => paritySign (popcount ((3 * x + 1) ^^^ (clmul 3 x ^^^ 1))))

private def s2 (w : Nat) : Int :=
  sumInt (2 ^ w) (fun x => paritySign (popcount ((3 * x + 2) ^^^ (clmul 3 x ^^^ 1))))

private theorem clmul3_two_mul (y : Nat) : clmul 3 (2 * y) = 2 * clmul 3 y := by
  rw [clmul_three, clmul_three]
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp [show (2 * y) / 2 = y by omega, show (2 * (2 * y)) / 2 = 2 * y by omega,
      show (2 * (y ^^^ (2 * y))) / 2 = y ^^^ (2 * y) by omega, Nat.testBit_xor]

private theorem clmul3_two_mul_add_one (y : Nat) :
    clmul 3 (2 * y + 1) = 2 * (clmul 3 y ^^^ 1) + 1 := by
  rw [clmul_three, clmul_three]
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    rw [show (2 * y + 1) / 2 = y by omega, show (2 * (2 * y + 1)) / 2 = 2 * y + 1 by omega,
      show (2 * ((y ^^^ (2 * y)) ^^^ 1) + 1) / 2 = (y ^^^ (2 * y)) ^^^ 1 by omega]
    have h2y1 : 2 * y + 1 = (2 * y) ^^^ 1 := by
      apply Nat.eq_of_testBit_eq
      intro i
      cases i with
      | zero => simp [Nat.testBit_zero]
      | succ i =>
        rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        simp [show (2 * y + 1) / 2 = y by omega, show (2 * y) / 2 = y by omega]
    rw [h2y1, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    cases y.testBit k <;> cases (2 * y).testBit k <;> cases (1 : Nat).testBit k <;> rfl

private theorem xor_two_mul (a b : Nat) : (2 * a) ^^^ (2 * b) = 2 * (a ^^^ b) := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp [show (2 * a) / 2 = a by omega, show (2 * b) / 2 = b by omega,
      show (2 * (a ^^^ b)) / 2 = a ^^^ b by omega, Nat.testBit_xor]

private theorem xor_two_mul_add_one (a b : Nat) :
    (2 * a + 1) ^^^ (2 * b + 1) = 2 * (a ^^^ b) := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp [show (2 * a + 1) / 2 = a by omega, show (2 * b + 1) / 2 = b by omega,
      show (2 * (a ^^^ b)) / 2 = a ^^^ b by omega, Nat.testBit_xor]

private theorem xor_even_odd (a b : Nat) :
    (2 * a) ^^^ (2 * b + 1) = 2 * (a ^^^ b) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp [show (2 * a) / 2 = a by omega, show (2 * b + 1) / 2 = b by omega,
      show (2 * (a ^^^ b) + 1) / 2 = a ^^^ b by omega, Nat.testBit_xor]

private theorem xor_odd_even (a b : Nat) :
    (2 * a + 1) ^^^ (2 * b) = 2 * (a ^^^ b) + 1 := by
  rw [Nat.xor_comm, xor_even_odd, Nat.xor_comm]

private theorem s0_succ (w : Nat) : s0 (w + 1) = s0 w + s1 w := by
  unfold s0 s1
  rw [Nat.pow_succ, Nat.mul_comm, sumInt_pair]
  congr 1
  · apply sumInt_congr
    intro y _
    rw [show 3 * (2 * y) = 2 * (3 * y) by omega, clmul3_two_mul, xor_two_mul, popcount_two_mul]
  · apply sumInt_congr
    intro y _
    rw [show 3 * (2 * y + 1) = 2 * (3 * y + 1) + 1 by omega, clmul3_two_mul_add_one,
      xor_two_mul_add_one, popcount_two_mul]

private theorem s1_succ (w : Nat) : s1 (w + 1) = s0 w + s2 w := by
  unfold s0 s1 s2
  rw [Nat.pow_succ, Nat.mul_comm, sumInt_pair]
  congr 1
  · apply sumInt_congr
    intro y _
    have hcl : clmul 3 (2 * y) ^^^ 1 = 2 * clmul 3 y + 1 := by
      rw [clmul3_two_mul]
      apply Nat.eq_of_testBit_eq
      intro k
      cases k with
      | zero => simp [Nat.testBit_zero]
      | succ k =>
        rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        simp [show (2 * clmul 3 y) / 2 = clmul 3 y by omega,
          show (2 * clmul 3 y + 1) / 2 = clmul 3 y by omega]
    rw [show 3 * (2 * y) + 1 = 2 * (3 * y) + 1 by omega, hcl, xor_two_mul_add_one, popcount_two_mul]
  · apply sumInt_congr
    intro y _
    have hcl : clmul 3 (2 * y + 1) ^^^ 1 = 2 * (clmul 3 y ^^^ 1) := by
      rw [clmul3_two_mul_add_one]
      apply Nat.eq_of_testBit_eq
      intro k
      cases k with
      | zero => simp [Nat.testBit_zero]
      | succ k =>
        rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        simp [show (2 * (clmul 3 y ^^^ 1) + 1) / 2 = clmul 3 y ^^^ 1 by omega,
          show (2 * (clmul 3 y ^^^ 1)) / 2 = clmul 3 y ^^^ 1 by omega]
    rw [show 3 * (2 * y + 1) + 1 = 2 * (3 * y + 2) by omega, hcl, xor_two_mul, popcount_two_mul]

private theorem s2_succ (w : Nat) : s2 (w + 1) = s1 w - s2 w := by
  unfold s1 s2
  rw [Nat.pow_succ, Nat.mul_comm, sumInt_pair]
  have h1 : sumInt (2 ^ w) (fun y =>
      paritySign (popcount ((3 * (2 * y) + 2) ^^^ (clmul 3 (2 * y) ^^^ 1)))) =
      sumInt (2 ^ w) (fun y =>
        paritySign (popcount ((3 * y + 1) ^^^ (clmul 3 y ^^^ 1)))) := by
    apply sumInt_congr
    intro y _
    have hcl : clmul 3 (2 * y) ^^^ 1 = 2 * clmul 3 y + 1 := by
      rw [clmul3_two_mul]
      apply Nat.eq_of_testBit_eq
      intro k
      cases k with
      | zero => simp [Nat.testBit_zero]
      | succ k =>
        rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        simp [show (2 * clmul 3 y) / 2 = clmul 3 y by omega,
          show (2 * clmul 3 y + 1) / 2 = clmul 3 y by omega]
    rw [show 3 * (2 * y) + 2 = 2 * (3 * y + 1) by omega, hcl, xor_even_odd,
      paritySign_two_mul_add_one]
    have hflip : (3 * y + 1) ^^^ clmul 3 y = ((3 * y + 1) ^^^ (clmul 3 y ^^^ 1)) ^^^ 1 := by
      rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [hflip, paritySign_xor_one]
    omega
  have h2 : sumInt (2 ^ w) (fun y =>
      paritySign (popcount ((3 * (2 * y + 1) + 2) ^^^ (clmul 3 (2 * y + 1) ^^^ 1)))) =
      -sumInt (2 ^ w) (fun y =>
        paritySign (popcount ((3 * y + 2) ^^^ (clmul 3 y ^^^ 1)))) := by
    rw [← sumInt_neg]
    apply sumInt_congr
    intro y _
    have hcl : clmul 3 (2 * y + 1) ^^^ 1 = 2 * (clmul 3 y ^^^ 1) := by
      rw [clmul3_two_mul_add_one]
      apply Nat.eq_of_testBit_eq
      intro k
      cases k with
      | zero => simp [Nat.testBit_zero]
      | succ k =>
        rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        simp [show (2 * (clmul 3 y ^^^ 1) + 1) / 2 = clmul 3 y ^^^ 1 by omega,
          show (2 * (clmul 3 y ^^^ 1)) / 2 = clmul 3 y ^^^ 1 by omega]
    rw [show 3 * (2 * y + 1) + 2 = 2 * (3 * y + 2) + 1 by omega, hcl, xor_odd_even,
      paritySign_two_mul_add_one]
  rw [h1, h2]
  omega

private theorem s_triple_closed (k : Nat) :
    (s0 (2 * k + 1) = 2 * (3 : Int) ^ k ∧
     s1 (2 * k + 1) = 2 * (3 : Int) ^ k ∧
     s2 (2 * k + 1) = 0) ∧
    (s0 (2 * k + 2) = 4 * (3 : Int) ^ k ∧
     s1 (2 * k + 2) = 2 * (3 : Int) ^ k ∧
     s2 (2 * k + 2) = 2 * (3 : Int) ^ k) := by
  induction k with
  | zero =>
    have h00 : s0 0 = 1 := by simp [s0, sumInt, clmul_three, popcount_zero, paritySign]
    have h01 : s1 0 = 1 := by simp [s1, sumInt, clmul_three, popcount_zero, paritySign]
    have h02 : s2 0 = 1 := by
      simp [s2, sumInt, clmul_three, show (2 ^^^ 1 : Nat) = 3 by decide, popcount_three, paritySign]
    have h1_0 : s0 1 = 2 := by rw [s0_succ 0]; omega
    have h1_1 : s1 1 = 2 := by rw [s1_succ 0]; omega
    have h1_2 : s2 1 = 0 := by rw [s2_succ 0]; omega
    have h2_0 : s0 2 = 4 := by rw [s0_succ 1]; omega
    have h2_1 : s1 2 = 2 := by rw [s1_succ 1]; omega
    have h2_2 : s2 2 = 2 := by rw [s2_succ 1]; omega
    exact ⟨⟨h1_0, h1_1, h1_2⟩, ⟨h2_0, h2_1, h2_2⟩⟩
  | succ k ih =>
    rcases ih with ⟨_, ⟨he0, he1, he2⟩⟩
    have hpow : (3 : Int) ^ (k + 1) = (3 : Int) ^ k * 3 := Int.pow_succ (3 : Int) k
    have ho0 : s0 (2 * (k + 1) + 1) = 2 * (3 : Int) ^ (k + 1) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega, s0_succ, he0, he1, hpow]; omega
    have ho1 : s1 (2 * (k + 1) + 1) = 2 * (3 : Int) ^ (k + 1) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega, s1_succ, he0, he2, hpow]; omega
    have ho2 : s2 (2 * (k + 1) + 1) = 0 := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega, s2_succ, he1, he2]; omega
    have hn0 : s0 (2 * (k + 1) + 2) = 4 * (3 : Int) ^ (k + 1) := by
      rw [show 2 * (k + 1) + 2 = (2 * (k + 1) + 1) + 1 by omega, s0_succ, ho0, ho1]; omega
    have hn1 : s1 (2 * (k + 1) + 2) = 2 * (3 : Int) ^ (k + 1) := by
      rw [show 2 * (k + 1) + 2 = (2 * (k + 1) + 1) + 1 by omega, s1_succ, ho0, ho2]; omega
    have hn2 : s2 (2 * (k + 1) + 2) = 2 * (3 : Int) ^ (k + 1) := by
      rw [show 2 * (k + 1) + 2 = (2 * (k + 1) + 1) + 1 by omega, s2_succ, ho1, ho2]; omega
    exact ⟨⟨ho0, ho1, ho2⟩, ⟨hn0, hn1, hn2⟩⟩

theorem carried_clmul3_parity_sum (w : Nat) (hw : 1 ≤ w) :
    clmul3ParitySum w =
      if w % 2 = 0 then 4 * (3 : Int) ^ (w / 2 - 1) else 2 * (3 : Int) ^ (w / 2) := by
  have heq : clmul3ParitySum w = s0 w := by
    unfold clmul3ParitySum s0
    apply sumInt_congr
    intro x _
    unfold paritySign
    rw [popcount_xor_parity]
  rw [heq]
  by_cases heven : w % 2 = 0
  · simp only [heven, ↓reduceIte]
    have hw2 : 2 ≤ w := by omega
    have hform : w = 2 * (w / 2 - 1) + 2 := by omega
    conv => lhs; rw [hform]
    exact (s_triple_closed (w / 2 - 1)).2.1
  · simp only [heven, ↓reduceIte]
    have hform : w = 2 * (w / 2) + 1 := by omega
    conv => lhs; rw [hform]
    exact (s_triple_closed (w / 2)).1.1

end ClmulCarryDynamics
