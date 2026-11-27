import BitSlicedCarryHolonomy2adic.Defs

namespace CarryHolonomyEngine
theorem iter_zero (f : Nat → Nat) (x : Nat) : iter f 0 x = x := rfl

theorem iter_succ (f : Nat → Nat) (n x : Nat) : iter f (n + 1) x = f (iter f n x) := rfl

theorem iter_add (f : Nat → Nat) (m n x : Nat) :
    iter f (m + n) x = iter f m (iter f n x) := by
  induction m with
  | zero => simp [iter]
  | succ m ih =>
    rw [Nat.succ_add, iter_succ, iter_succ, ih]

theorem iter_comm (f : Nat → Nat) (n x : Nat) :
    iter f (n + 1) x = iter f n (f x) := by
  have h := iter_add f n 1 x
  simpa [iter] using h

theorem iter_mul (f : Nat → Nat) (p q x : Nat) :
    iter f (p * q) x = iter (iter f p) q x := by
  induction q with
  | zero => simp [iter]
  | succ q ih =>
    rw [Nat.mul_succ, Nat.add_comm, iter_add, iter_succ, ih]

theorem pow2_pos (k : Nat) : 0 < 2 ^ k := Nat.pow_pos (by omega)

theorem testBit_eq_div_mod (x k : Nat) : x.testBit k = ((x / 2 ^ k) % 2 == 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
  cases h : (x / 2 ^ k) % 2 with
  | zero => rfl
  | succ m =>
    have : (x / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by omega)
    have : m = 0 := by omega
    subst this
    rfl

theorem testBit_mod_pow2_of_lt (x k i : Nat) (hi : i < k) :
    (x % 2 ^ k).testBit i = x.testBit i := by
  rw [Nat.testBit_mod_two_pow]
  simp [hi]

theorem testBit_mod_pow2_of_ge (x k i : Nat) (hi : k ≤ i) :
    (x % 2 ^ k).testBit i = false := by
  rw [Nat.testBit_mod_two_pow]
  have : ¬ (i < k) := by omega
  simp [this]

theorem mod_pow2_succ_eq (x k : Nat) :
    x % 2 ^ (k + 1) = x % 2 ^ k + 2 ^ k * (if x.testBit k then 1 else 0) := by
  rw [testBit_eq_div_mod, Nat.pow_succ, Nat.mod_mul]
  have hlt : (x / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by omega)
  cases h : (x / 2 ^ k) % 2 with
  | zero => simp
  | succ m =>
    have hm : m = 0 := by omega
    subst hm
    simp [Nat.mul_comm]

theorem eq_mod_pow2_succ_iff (x y k : Nat) :
    x % 2 ^ (k + 1) = y % 2 ^ (k + 1) ↔
      x % 2 ^ k = y % 2 ^ k ∧ x.testBit k = y.testBit k := by
  constructor
  · intro h
    constructor
    · have h1 : (x % 2 ^ (k + 1)) % 2 ^ k = (y % 2 ^ (k + 1)) % 2 ^ k := by rw [h]
      have hdvd : 2 ^ k ∣ 2 ^ (k + 1) := ⟨2, by rw [Nat.pow_succ]⟩
      simpa [Nat.mod_mod_of_dvd _ hdvd] using h1
    · have h2 : (x % 2 ^ (k + 1)).testBit k = (y % 2 ^ (k + 1)).testBit k := by rw [h]
      rwa [testBit_mod_pow2_of_lt x (k + 1) k (by omega),
           testBit_mod_pow2_of_lt y (k + 1) k (by omega)] at h2
  · rintro ⟨h1, h2⟩
    rw [mod_pow2_succ_eq x k, mod_pow2_succ_eq y k, h1, h2]

theorem testBit_add_pow2_self (x k : Nat) :
    (x + 2 ^ k).testBit k = !x.testBit k := by
  rw [testBit_eq_div_mod, testBit_eq_div_mod]
  have hpos : 0 < 2 ^ k := pow2_pos k
  rw [Nat.add_div_right _ hpos]
  cases h : (x / 2 ^ k) % 2 with
  | zero =>
    have h1 : (x / 2 ^ k + 1) % 2 = 1 := by omega
    simp [h1]
  | succ m =>
    have hm : m = 0 := by omega
    subst hm
    have h1 : (x / 2 ^ k + 1) % 2 = 0 := by omega
    simp [h1]

theorem testBit_add_pow2_lt (x k i : Nat) (hi : i < k) :
    (x + 2 ^ k).testBit i = x.testBit i := by
  rw [← testBit_mod_pow2_of_lt (x + 2 ^ k) k i hi,
      ← testBit_mod_pow2_of_lt x k i hi]
  simp

theorem testBit_add_pow2_succ (x k : Nat) :
    (x + 2 ^ k).testBit (k + 1) = xor (x.testBit (k + 1)) (x.testBit k) := by
  rw [testBit_eq_div_mod, testBit_eq_div_mod, testBit_eq_div_mod]
  have hpos : 0 < 2 ^ k := pow2_pos k
  have hdiv : (x + 2 ^ k) / 2 ^ (k + 1) = (x / 2 ^ k + 1) / 2 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.add_div_right _ hpos]
  have hxdiv : x / 2 ^ (k + 1) = (x / 2 ^ k) / 2 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  rw [hdiv, hxdiv]
  generalize x / 2 ^ k = q
  have hq : q % 4 < 4 := Nat.mod_lt q (by omega)
  have h0 : q % 2 = (q % 4) % 2 := by omega
  have h1 : (q / 2) % 2 = (q % 4) / 2 := by omega
  have h2 : ((q + 1) / 2) % 2 = ((q % 4 + 1) / 2) % 2 := by omega
  rw [h0, h1, h2]
  generalize q % 4 = r at hq ⊢
  match r with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl

theorem mod_pow2_of_testBit_eq (x y k : Nat)
    (h : ∀ i < k, x.testBit i = y.testBit i) : x % 2 ^ k = y % 2 ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [eq_mod_pow2_succ_iff]
    exact ⟨ih (fun i hi => h i (by omega)), h k (by omega)⟩

theorem v2_zero : v2 0 = 0 := by
  unfold v2; simp

theorem v2_of_odd (n : Nat) (h : n % 2 = 1) : v2 n = 0 := by
  unfold v2
  have hne : n ≠ 0 := by omega
  have hne2 : ¬ (n % 2 = 0) := by omega
  simp [hne, hne2]

theorem v2_two_mul (n : Nat) (hn : n ≠ 0) : v2 (2 * n) = 1 + v2 n := by
  conv => lhs; unfold v2
  have hne : 2 * n ≠ 0 := by omega
  have hev : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  simp [hne, hev, hdiv]

theorem v2_mul_pow2 (e m : Nat) (hm : m ≠ 0) : v2 (2 ^ e * m) = e + v2 m := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hmul : 2 ^ (e + 1) * m = 2 * (2 ^ e * m) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_assoc]
    have hne : 2 ^ e * m ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt (pow2_pos e)) hm
    rw [hmul, v2_two_mul _ hne, ih]
    omega

theorem v2_eq_of_mod_testBit (n k : Nat)
    (hmod : n % 2 ^ k = 0) (hbit : n.testBit k = true) : v2 n = k := by
  have hodd : (n / 2 ^ k) % 2 = 1 := by
    rw [testBit_eq_div_mod] at hbit
    cases h : (n / 2 ^ k) % 2 with
    | zero => simp [h] at hbit
    | succ m =>
      have : (n / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by omega)
      omega
  have hne : n / 2 ^ k ≠ 0 := by omega
  have hdecomp : n = 2 ^ k * (n / 2 ^ k) := by
    have := Nat.div_add_mod n (2 ^ k)
    omega
  conv => lhs; rw [hdecomp]
  rw [v2_mul_pow2 k (n / 2 ^ k) hne, v2_of_odd _ hodd]
  omega

theorem v2_decomp (n : Nat) (hn : n ≠ 0) :
    n = 2 ^ v2 n * (n / 2 ^ v2 n) ∧ (n / 2 ^ v2 n) % 2 = 1 := by
  refine Nat.strongRecOn (motive := fun n => n ≠ 0 →
      n = 2 ^ v2 n * (n / 2 ^ v2 n) ∧ (n / 2 ^ v2 n) % 2 = 1) n ?_ hn
  intro n ih hn
  by_cases hev : n % 2 = 0
  · have hne2 : n / 2 ≠ 0 := by omega
    have hlt : n / 2 < n := by omega
    have hv : v2 n = 1 + v2 (n / 2) := by
      conv => lhs; unfold v2
      simp [hn, hev]
    have ⟨hd, ho⟩ := ih (n / 2) hlt hne2
    rw [hv]
    have hpow : 2 ^ (1 + v2 (n / 2)) = 2 * 2 ^ v2 (n / 2) := by
      rw [Nat.add_comm, Nat.pow_succ, Nat.mul_comm]
    have hdiv : n / 2 ^ (1 + v2 (n / 2)) = (n / 2) / 2 ^ v2 (n / 2) := by
      rw [hpow, ← Nat.div_div_eq_div_mul]
    rw [hdiv]
    refine ⟨?_, ho⟩
    rw [hpow, Nat.mul_assoc, ← hd]
    omega
  · have hodd : n % 2 = 1 := by omega
    have hv : v2 n = 0 := v2_of_odd n hodd
    simp [hv, hodd]

theorem v2_of_mod_eq_of_lt (a b k : Nat)
    (heq : a % 2 ^ k = b % 2 ^ k) (hmod : b % 2 ^ (v2 b) = 0)
    (hbit : b.testBit (v2 b) = true) (hlt : v2 b < k) : v2 a = v2 b := by
  have hdvd : 2 ^ (v2 b) ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
  have hamod : a % 2 ^ (v2 b) = 0 := by
    have h1 : (a % 2 ^ k) % 2 ^ (v2 b) = (b % 2 ^ k) % 2 ^ (v2 b) := by rw [heq]
    rw [Nat.mod_mod_of_dvd a hdvd, Nat.mod_mod_of_dvd b hdvd] at h1
    rw [h1, hmod]
  have habit : a.testBit (v2 b) = true := by
    rw [← testBit_mod_pow2_of_lt a k (v2 b) hlt, heq,
        testBit_mod_pow2_of_lt b k (v2 b) hlt, hbit]
  exact v2_eq_of_mod_testBit a (v2 b) hamod habit

theorem v2_mod_zero (n : Nat) (hn : n ≠ 0) : n % 2 ^ v2 n = 0 := by
  have ⟨hd, _⟩ := v2_decomp n hn
  have h1 : (2 ^ v2 n * (n / 2 ^ v2 n)) % 2 ^ v2 n = 0 := Nat.mul_mod_right _ _
  rwa [← hd] at h1

theorem v2_testBit_true (n : Nat) (hn : n ≠ 0) : n.testBit (v2 n) = true := by
  have ⟨_, ho⟩ := v2_decomp n hn
  rw [testBit_eq_div_mod, ho]
  rfl

theorem v2_eq_of_mod_eq_and_lt (a b k : Nat) (hb : b ≠ 0)
    (heq : a % 2 ^ k = b % 2 ^ k) (hlt : v2 b < k) : v2 a = v2 b :=
  v2_of_mod_eq_of_lt a b k heq (v2_mod_zero b hb) (v2_testBit_true b hb) hlt

theorem v2_ne_zero_of_lt_mod (n k : Nat) (h : n % 2 ^ k ≠ 0) : n ≠ 0 := by
  intro hn; subst hn; simp at h

theorem v2_lt_of_mod_ne_zero (n k : Nat) (h : n % 2 ^ k ≠ 0) : v2 n < k := by
  rcases Nat.lt_or_ge (v2 n) k with hlt | hk
  · exact hlt
  · exfalso
    have hn : n ≠ 0 := v2_ne_zero_of_lt_mod n k h
    have hdvd : 2 ^ k ∣ 2 ^ v2 n := Nat.pow_dvd_pow 2 hk
    have h0 : n % 2 ^ v2 n = 0 := v2_mod_zero n hn
    have hmod : n % 2 ^ k = 0 := by
      have := Nat.mod_mod_of_dvd n hdvd
      rw [h0, Nat.zero_mod] at this
      exact this.symm
    exact h hmod

/-! ## Section 2: Finite GF(2) Parity Sums (`xorRange`) & Bijection Invariance -/

theorem xorRange_zero (g : Nat → Bool) : xorRange 0 g = false := rfl

theorem xorRange_succ (n : Nat) (g : Nat → Bool) :
    xorRange (n + 1) g = xor (xorRange n g) (g n) := rfl

theorem xorRange_congr (n : Nat) (g h : Nat → Bool)
    (hgh : ∀ i < n, g i = h i) : xorRange n g = xorRange n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorRange_succ]
    rw [ih (fun i hi => hgh i (by omega)), hgh n (by omega)]

theorem xorRange_false (n : Nat) : xorRange n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [xorRange_succ, ih]

theorem xorRange_const (n : Nat) (b : Bool) :
    xorRange n (fun _ => b) = (if n % 2 == 1 then b else false) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorRange_succ, ih]
    cases b <;> cases h : n % 2 with
    | zero =>
      have h1 : (n + 1) % 2 = 1 := by omega
      simp [h1]
    | succ m =>
      have hm : m = 0 := by omega
      subst hm
      have h1 : (n + 1) % 2 = 0 := by omega
      simp [h1]

theorem xorRange_xor (n : Nat) (g h : Nat → Bool) :
    xorRange n (fun i => xor (g i) (h i)) = xor (xorRange n g) (xorRange n h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorRange_succ, ih]
    cases xorRange n g <;> cases xorRange n h <;> cases g n <;> cases h n <;> rfl

theorem xorRange_add (m n : Nat) (g : Nat → Bool) :
    xorRange (m + n) g = xor (xorRange m g) (xorRange n (fun i => g (m + i))) := by
  induction n with
  | zero => simp [xorRange]
  | succ n ih =>
    rw [← Nat.add_assoc, xorRange_succ, xorRange_succ, ih]
    cases xorRange m g <;> cases xorRange n (fun i => g (m + i)) <;> cases g (m + n) <;> rfl

theorem xorRange_two_mul (L : Nat) (g : Nat → Bool) :
    xorRange (2 * L) g = xorRange L (fun i => xor (g i) (g (i + L))) := by
  have h2 : 2 * L = L + L := by omega
  rw [h2, xorRange_add, xorRange_xor]
  congr 1
  exact xorRange_congr L _ _ (fun i _ => by rw [Nat.add_comm])

theorem xorRange_two_mul_interleave (Q : Nat) (g : Nat → Bool) :
    xorRange (2 * Q) g = xorRange Q (fun t => xor (g (2 * t)) (g (2 * t + 1))) := by
  induction Q with
  | zero => rfl
  | succ Q ih =>
    have h2 : 2 * (Q + 1) = (2 * Q + 1) + 1 := by omega
    rw [h2, xorRange_succ, xorRange_succ, xorRange_succ, ih]
    cases xorRange Q (fun t => xor (g (2 * t)) (g (2 * t + 1))) <;>
      cases g (2 * Q) <;> cases g (2 * Q + 1) <;> rfl

theorem xorRange_comm (m n : Nat) (f : Nat → Nat → Bool) :
    xorRange m (fun i => xorRange n (fun j => f i j)) =
      xorRange n (fun j => xorRange m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [xorRange_zero]
    symm
    exact xorRange_false n
  | succ m ih =>
    rw [xorRange_succ, ih, ← xorRange_xor]
    exact xorRange_congr n _ _ (fun j _ => (xorRange_succ m (fun i => f i j)).symm)

theorem xorRange_ite_eq (n k : Nat) (hk : k < n) (g : Nat → Bool) :
    xorRange n (fun i => if i == k then g i else false) = g k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [xorRange_succ]
    by_cases hkn : k = n
    · subst hkn
      have hpre : xorRange k (fun i => if i == k then g i else false) = false := by
        rw [xorRange_congr k _ (fun _ => false) (fun i hi => by
          have : (i == k) = false := beq_false_of_ne (by omega)
          simp [this])]
        exact xorRange_false k
      rw [hpre]
      simp
    · have hlt : k < n := by omega
      have hne : (n == k) = false := beq_false_of_ne (by omega)
      rw [ih hlt, hne]
      simp

/-- Double-counting bijection invariance of `xorRange` over `[0, N)`. -/
theorem xorRange_bij (N : Nat) (σ τ : Nat → Nat) (g : Nat → Bool)
    (hσ_lt : ∀ i < N, σ i < N)
    (hτ_lt : ∀ j < N, τ j < N)
    (hστ : ∀ j < N, σ (τ j) = j)
    (hτσ : ∀ i < N, τ (σ i) = i) :
    xorRange N (fun i => g (σ i)) = xorRange N g := by
  have h1 : xorRange N (fun i => g (σ i)) =
      xorRange N (fun i => xorRange N (fun j => if j == σ i then g j else false)) := by
    apply xorRange_congr
    intro i hi
    symm
    exact xorRange_ite_eq N (σ i) (hσ_lt i hi) g
  rw [h1, xorRange_comm]
  apply xorRange_congr
  intro j hj
  have h2 : xorRange N (fun i => if j == σ i then g j else false) =
      xorRange N (fun i => if i == τ j then g j else false) := by
    apply xorRange_congr
    intro i hi
    by_cases hij : i = τ j
    · subst hij
      simp [hστ j hj]
    · have hne1 : (i == τ j) = false := beq_false_of_ne hij
      have hne2 : (j == σ i) = false := by
        apply beq_false_of_ne
        intro heq
        have := hτσ i hi
        rw [← heq] at this
        exact hij this.symm
      simp [hne1, hne2]
  rw [h2]
  exact xorRange_ite_eq N (τ j) (hτ_lt j hj) (fun _ => g j)

/-! ## Section 3: Abstract 2-Adic T-Permutations (`TPerm`) & Hensel Inverter -/

theorem TPerm.compat_mod {f : Nat → Nat} (hf : TPerm f) (k x : Nat) :
    f (x % 2 ^ k) % 2 ^ k = f x % 2 ^ k :=
  hf.compat k (x % 2 ^ k) x (Nat.mod_mod _ _)

theorem TPerm.testBit_eq_of_mod_eq {f : Nat → Nat} (hf : TPerm f) {k i x y : Nat}
    (hi : i < k) (hxy : x % 2 ^ k = y % 2 ^ k) :
    (f x).testBit i = (f y).testBit i := by
  rw [← testBit_mod_pow2_of_lt (f x) k i hi,
      ← testBit_mod_pow2_of_lt (f y) k i hi,
      hf.compat k x y hxy]

theorem TPerm.bit_lift {f : Nat → Nat} (hf : TPerm f) (k x : Nat) :
    (f x).testBit k = xor (x.testBit k) ((f (x % 2 ^ k)).testBit k) := by
  have hx := mod_pow2_succ_eq x k
  have hmod : x % 2 ^ (k + 1) = (x % 2 ^ k + 2 ^ k * (if x.testBit k then 1 else 0)) % 2 ^ (k + 1) := by
    rw [← hx, Nat.mod_mod]
  have hbit := hf.testBit_eq_of_mod_eq (k := k + 1) (i := k) (by omega) hmod
  rw [hbit]
  cases x.testBit k with
  | false => simp
  | true =>
    simp [hf.fiber_flip k (x % 2 ^ k)]

theorem TPerm.bit_flip_of_mod_bit {f : Nat → Nat} (hf : TPerm f) (k x y : Nat)
    (hmod : x % 2 ^ k = y % 2 ^ k) (hbit : x.testBit k = !y.testBit k) :
    (f x).testBit k = !(f y).testBit k := by
  rw [hf.bit_lift k x, hf.bit_lift k y, hmod, hbit]
  cases y.testBit k <;> cases (f (y % 2 ^ k)).testBit k <;> rfl

theorem TPerm.comp {f g : Nat → Nat} (hf : TPerm f) (hg : TPerm g) :
    TPerm (fun x => f (g x)) where
  compat k x y hxy := hf.compat k (g x) (g y) (hg.compat k x y hxy)
  fiber_flip k x := by
    apply hf.bit_flip_of_mod_bit k (g (x + 2 ^ k)) (g x)
    · exact hg.compat k (x + 2 ^ k) x (by simp)
    · exact hg.fiber_flip k x

theorem TPerm.iter_tperm {f : Nat → Nat} (hf : TPerm f) (n : Nat) :
    TPerm (iter f n) := by
  induction n with
  | zero =>
    exact {
      compat := fun _ _ _ h => h
      fiber_flip := fun k x => testBit_add_pow2_self x k
    }
  | succ n ih => exact hf.comp ih

theorem TPerm.iter_mod_compat {f : Nat → Nat} (hf : TPerm f) (k n x y : Nat)
    (hxy : x % 2 ^ k = y % 2 ^ k) :
    iter f n x % 2 ^ k = iter f n y % 2 ^ k :=
  (hf.iter_tperm n).compat k x y hxy

theorem tpermInv_lt (f : Nat → Nat) (k y : Nat) : tpermInv f k y < 2 ^ k := by
  induction k generalizing y with
  | zero => simp [tpermInv]
  | succ k ih =>
    simp only [tpermInv]
    have hlt := ih (y % 2 ^ k)
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    split <;> omega

theorem tpermInv_right_inv {f : Nat → Nat} (hf : TPerm f) (k y : Nat) :
    f (tpermInv f k y) % 2 ^ k = y % 2 ^ k := by
  induction k generalizing y with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    simp only [tpermInv]
    have hmod0 : f (tpermInv f k (y % 2 ^ k)) % 2 ^ k = y % 2 ^ k := by
      rw [ih (y % 2 ^ k), Nat.mod_mod]
    rw [eq_mod_pow2_succ_iff]
    split
    · next heq =>
      exact ⟨hmod0, by simpa using heq⟩
    · next hne =>
      refine ⟨?_, ?_⟩
      · rw [hf.compat k (tpermInv f k (y % 2 ^ k) + 2 ^ k) (tpermInv f k (y % 2 ^ k)) (by simp), hmod0]
      · rw [hf.fiber_flip k (tpermInv f k (y % 2 ^ k))]
        cases hb1 : (f (tpermInv f k (y % 2 ^ k))).testBit k <;> cases hb2 : y.testBit k <;> simp_all

theorem tpermInv_left_inv {f : Nat → Nat} (hf : TPerm f) (k x : Nat) (hx : x < 2 ^ k) :
    tpermInv f k (f x % 2 ^ k) = x := by
  induction k generalizing x with
  | zero =>
    simp only [tpermInv]
    omega
  | succ k ih =>
    simp only [tpermInv]
    have hmod_f : (f x % 2 ^ (k + 1)) % 2 ^ k = f (x % 2 ^ k) % 2 ^ k := by
      have hdvd : 2 ^ k ∣ 2 ^ (k + 1) := ⟨2, by rw [Nat.pow_succ]⟩
      rw [Nat.mod_mod_of_dvd _ hdvd, hf.compat_mod]
    rw [hmod_f, ih (x % 2 ^ k) (Nat.mod_lt x (pow2_pos k))]
    have hbit_y : (f x % 2 ^ (k + 1)).testBit k = (f x).testBit k :=
      testBit_mod_pow2_of_lt (f x) (k + 1) k (by omega)
    rw [hbit_y, hf.bit_lift k x]
    have hxdecomp : x = x % 2 ^ k + 2 ^ k * (if x.testBit k then 1 else 0) := by
      have := mod_pow2_succ_eq x k
      rwa [Nat.mod_eq_of_lt hx] at this
    cases hb : x.testBit k with
    | false =>
      simp only [Bool.false_xor, beq_self_eq_true, ↓reduceIte]
      simpa [hb] using hxdecomp.symm
    | true =>
      have hne : ((f (x % 2 ^ k)).testBit k == !(f (x % 2 ^ k)).testBit k) = false := by
        cases (f (x % 2 ^ k)).testBit k <;> rfl
      simp only [Bool.true_xor, hne, Bool.false_eq_true, ↓reduceIte]
      simpa [hb] using hxdecomp.symm

theorem tpermInv_mod_eq {f : Nat → Nat} (hf : TPerm f) (k y : Nat) :
    tpermInv f k (y % 2 ^ k) = tpermInv f k y := by
  have hlt := tpermInv_lt f k y
  have h1 := tpermInv_left_inv hf k (tpermInv f k y) hlt
  rw [tpermInv_right_inv hf k y] at h1
  exact h1

/-- Any `TPerm f` induces a bijection on `[0, 2^k)`, preserving `xorRange (2^k)`. -/
theorem xorRange_tperm_bij {f : Nat → Nat} (hf : TPerm f) (k : Nat) (g : Nat → Bool) :
    xorRange (2 ^ k) (fun x => g (f x % 2 ^ k)) = xorRange (2 ^ k) g := by
  apply xorRange_bij (2 ^ k) (fun x => f x % 2 ^ k) (fun y => tpermInv f k y) g
  · intro i _; exact Nat.mod_lt _ (pow2_pos k)
  · intro j _; exact tpermInv_lt f k j
  · intro j hj; rw [tpermInv_right_inv hf k j, Nat.mod_eq_of_lt hj]
  · intro i hi; exact tpermInv_left_inv hf k i hi

/-! ## Section 4: The Reusable Carry-Holonomy 2-Adic Lifting Engine -/

/-- **Core Engine Theorem A (`holonomy_lift_step`)**:
    For any `TPerm f`, any level `k`, and any `L`, the bit `k` of `iter f L x0` is
    exactly `x0.testBit k ^^ holonomy f k x0 L`! -/
theorem iter_testBit_eq_holonomy {f : Nat → Nat} (hf : TPerm f) (k x0 L : Nat) :
    (iter f L x0).testBit k = xor (x0.testBit k) (holonomy f k x0 L) := by
  induction L with
  | zero => simp [iter, holonomy, xorRange]
  | succ L ih =>
    rw [iter_succ, hf.bit_lift k (iter f L x0), ih]
    unfold holonomy
    rw [xorRange_succ]
    cases x0.testBit k <;>
      cases xorRange L (fun i => (f (iter f i x0 % 2 ^ k)).testBit k) <;>
      cases (f (iter f L x0 % 2 ^ k)).testBit k <;> rfl

/-- If `iter f L x0 ≡ x0 (mod 2^k)` and `holonomy f k x0 L = true`, then:
    (1) `iter f L x0` flips bit `k` relative to `x0` (so period does NOT stay `L`),
    (2) `iter f (2 * L) x0 ≡ x0 (mod 2^(k+1))` (period doubles to `2 * L`)! -/
theorem holonomy_double_cycle {f : Nat → Nat} (hf : TPerm f) (k x0 L : Nat)
    (hcyc : iter f L x0 % 2 ^ k = x0 % 2 ^ k)
    (hhol : holonomy f k x0 L = true) :
    (iter f L x0).testBit k = !x0.testBit k ∧
    iter f (2 * L) x0 % 2 ^ (k + 1) = x0 % 2 ^ (k + 1) := by
  have hflip : (iter f L x0).testBit k = !x0.testBit k := by
    rw [iter_testBit_eq_holonomy hf k x0 L, hhol]
    cases x0.testBit k <;> rfl
  refine ⟨hflip, ?_⟩
  rw [eq_mod_pow2_succ_iff]
  have h2L : 2 * L = L + L := by omega
  constructor
  · rw [h2L, iter_add, hf.iter_mod_compat k L (iter f L x0) x0 hcyc, hcyc]
  · rw [h2L, iter_add]
    have hstep := (hf.iter_tperm L).bit_flip_of_mod_bit k (iter f L x0) x0 hcyc hflip
    rw [hstep, hflip, Bool.not_not]

/-- Fiber-flip propagation along the entire doubled cycle:
    for all `i`, `iter f (i + L) x0` agrees with `iter f i x0` mod `2^k` and flips bit `k`. -/
theorem iter_add_period_fiber_flip {f : Nat → Nat} (hf : TPerm f) (k x0 L i : Nat)
    (hcyc : iter f L x0 % 2 ^ k = x0 % 2 ^ k)
    (hhol : holonomy f k x0 L = true) :
    iter f (i + L) x0 % 2 ^ k = iter f i x0 % 2 ^ k ∧
    (iter f (i + L) x0).testBit k = !(iter f i x0).testBit k := by
  have hflip0 : (iter f L x0).testBit k = !x0.testBit k :=
    (holonomy_double_cycle hf k x0 L hcyc hhol).1
  rw [iter_add]
  exact ⟨hf.iter_mod_compat k i _ _ hcyc,
         (hf.iter_tperm i).bit_flip_of_mod_bit k _ _ hcyc hflip0⟩

/-- **Core Engine Theorem B (`doubled_fiber_holonomy`)**:
    When a cycle of length `L` at level `k` has `holonomy = true` (doubling to `2L` at level `k+1`),
    the next-level holonomy `holonomy f (k+1) x0 (2*L)` collapses cleanly to the fiber-difference
    XOR sum over the half-cycle `i = 0 .. L-1`! -/
theorem doubled_fiber_holonomy {f : Nat → Nat} (hf : TPerm f) (k x0 L : Nat)
    (hcyc : iter f L x0 % 2 ^ k = x0 % 2 ^ k)
    (hhol : holonomy f k x0 L = true) :
    holonomy f (k + 1) x0 (2 * L) =
      xorRange L (fun i =>
        let y := iter f i x0 % 2 ^ k
        xor ((f y).testBit (k + 1)) ((f (y + 2 ^ k)).testBit (k + 1))) := by
  unfold holonomy
  rw [xorRange_two_mul]
  apply xorRange_congr
  intro i _
  have ⟨hmod, hflip⟩ := iter_add_period_fiber_flip hf k x0 L i hcyc hhol
  have hz1 : iter f i x0 % 2 ^ (k + 1) =
      iter f i x0 % 2 ^ k + 2 ^ k * (if (iter f i x0).testBit k then 1 else 0) :=
    mod_pow2_succ_eq (iter f i x0) k
  have hz2 : iter f (i + L) x0 % 2 ^ (k + 1) =
      iter f i x0 % 2 ^ k + 2 ^ k * (if (iter f (i + L) x0).testBit k then 1 else 0) := by
    rw [mod_pow2_succ_eq (iter f (i + L) x0) k, hmod]
  rw [hz1, hz2, hflip]
  cases (iter f i x0).testBit k with
  | false => simp
  | true => simp [Bool.xor_comm]

/-! ### Sub-Engine 1: Universal Majority-Carry Formula for `T(x) = Φ(x) + c` -/

/-- **Majority-Carry Flip Identity**: flipping input bit `a` changes the carry-out by `b ^^ r`! -/
theorem maj_flip_xor (a b r : Bool) : xor (maj (!a) b r) (maj a b r) = xor b r := by
  cases a <;> cases b <;> cases r <;> rfl

/-- Bit `k` of `u + v` equals `u_k ^^ v_k ^^ carry_k(u, v)`, where
    `carry_k(u, v) = decide ((u % 2^k) + (v % 2^k) ≥ 2^k)`. -/
theorem testBit_add_eq (u v k : Nat) :
    (u + v).testBit k =
      xor (xor (u.testBit k) (v.testBit k)) (decide (u % 2 ^ k + v % 2 ^ k ≥ 2 ^ k)) := by
  rw [testBit_eq_div_mod, testBit_eq_div_mod, testBit_eq_div_mod]
  have hpos : 0 < 2 ^ k := pow2_pos k
  have hdu := Nat.div_add_mod u (2 ^ k)
  have hdv := Nat.div_add_mod v (2 ^ k)
  have hmu := Nat.mod_lt u hpos
  have hmv := Nat.mod_lt v hpos
  have hdiv : (u + v) / 2 ^ k = u / 2 ^ k + v / 2 ^ k + (if u % 2 ^ k + v % 2 ^ k ≥ 2 ^ k then 1 else 0) := by
    split
    · next hge =>
      have hmul : 2 ^ k * (u / 2 ^ k + v / 2 ^ k + 1) = 2 ^ k * (u / 2 ^ k) + 2 ^ k * (v / 2 ^ k) + 2 ^ k := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      have : u + v = 2 ^ k * (u / 2 ^ k + v / 2 ^ k + 1) + (u % 2 ^ k + v % 2 ^ k - 2 ^ k) := by
        rw [hmul]; omega
      rw [this, Nat.mul_add_div hpos]
      have hsmall : (u % 2 ^ k + v % 2 ^ k - 2 ^ k) / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
      omega
    · next hlt =>
      have hmul : 2 ^ k * (u / 2 ^ k + v / 2 ^ k) = 2 ^ k * (u / 2 ^ k) + 2 ^ k * (v / 2 ^ k) :=
        Nat.mul_add _ _ _
      have : u + v = 2 ^ k * (u / 2 ^ k + v / 2 ^ k) + (u % 2 ^ k + v % 2 ^ k) := by
        rw [hmul]; omega
      rw [this, Nat.mul_add_div hpos]
      have hsmall : (u % 2 ^ k + v % 2 ^ k) / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
      omega
  rw [hdiv]
  by_cases hge : u % 2 ^ k + v % 2 ^ k ≥ 2 ^ k
  · simp only [hge, ↓reduceIte, decide_true]
    have : (u / 2 ^ k + v / 2 ^ k + 1) % 2 = (u / 2 ^ k % 2 + v / 2 ^ k % 2 + 1) % 2 := by omega
    rw [this]
    have h1 := Nat.mod_lt (u / 2 ^ k) (by omega : 0 < 2)
    have h2 := Nat.mod_lt (v / 2 ^ k) (by omega : 0 < 2)
    generalize u / 2 ^ k % 2 = a at h1 ⊢
    generalize v / 2 ^ k % 2 = b at h2 ⊢
    match a, b with
    | 0, 0 => rfl | 0, 1 => rfl | 1, 0 => rfl | 1, 1 => rfl
  · simp only [hge, ↓reduceIte, decide_false]
    have : (u / 2 ^ k + v / 2 ^ k + 0) % 2 = (u / 2 ^ k % 2 + v / 2 ^ k % 2) % 2 := by omega
    rw [this]
    have h1 := Nat.mod_lt (u / 2 ^ k) (by omega : 0 < 2)
    have h2 := Nat.mod_lt (v / 2 ^ k) (by omega : 0 < 2)
    generalize u / 2 ^ k % 2 = a at h1 ⊢
    generalize v / 2 ^ k % 2 = b at h2 ⊢
    match a, b with
    | 0, 0 => rfl | 0, 1 => rfl | 1, 0 => rfl | 1, 1 => rfl

/-- Carry into bit `k + 1` of `u + v` expressed via `maj` of bit `k` and carry into bit `k`. -/
theorem carry_succ_eq_maj (u v k : Nat) :
    decide (u % 2 ^ (k + 1) + v % 2 ^ (k + 1) ≥ 2 ^ (k + 1)) =
      maj (u.testBit k) (v.testBit k) (decide (u % 2 ^ k + v % 2 ^ k ≥ 2 ^ k)) := by
  have hu := mod_pow2_succ_eq u k
  have hv := mod_pow2_succ_eq v k
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have hmu := Nat.mod_lt u (pow2_pos k)
  have hmv := Nat.mod_lt v (pow2_pos k)
  rw [hu, hv, hpow]
  cases u.testBit k <;> cases v.testBit k <;> by_cases h : u % 2 ^ k + v % 2 ^ k ≥ 2 ^ k <;>
    simp [maj, h] <;> omega

/-- Adding a constant `c` to any `TPerm Φ` preserves `TPerm`. -/
theorem TPerm.add_const {Φ : Nat → Nat} (hΦ : TPerm Φ) (c : Nat) :
    TPerm (fun x => Φ x + c) where
  compat k x y hxy := by
    have h := hΦ.compat k x y hxy
    rw [Nat.add_mod, h, ← Nat.add_mod]
  fiber_flip k x := by
    rw [testBit_add_eq, testBit_add_eq]
    have hmod : Φ (x + 2 ^ k) % 2 ^ k = Φ x % 2 ^ k := hΦ.compat k (x + 2 ^ k) x (by simp)
    rw [hmod, hΦ.fiber_flip k x]
    cases (Φ x).testBit k <;> cases c.testBit k <;>
      cases decide (Φ x % 2 ^ k + c % 2 ^ k ≥ 2 ^ k) <;> rfl

/-- **Universal Fiber-Difference Formula for `T(x) = Φ(x) + c`**:
    For ANY `TPerm Φ`, ANY `c`, ANY `k`, and ANY `y`:
    `(T y).testBit (k+1) ^^ (T (y + 2^k)).testBit (k+1)` equals
    `β_{k+1}(Φ, y) ^^ c.testBit k ^^ decide (Φ y % 2^k + c % 2^k ≥ 2^k)`! -/
theorem add_const_fiber_diff {Φ : Nat → Nat} (hΦ : TPerm Φ) (c k y : Nat) :
    xor ((Φ y + c).testBit (k + 1)) ((Φ (y + 2 ^ k) + c).testBit (k + 1)) =
      xor (xor (xor ((Φ y).testBit (k + 1)) ((Φ (y + 2 ^ k)).testBit (k + 1))) (c.testBit k))
          (decide (Φ y % 2 ^ k + c % 2 ^ k ≥ 2 ^ k)) := by
  rw [testBit_add_eq, testBit_add_eq, carry_succ_eq_maj, carry_succ_eq_maj]
  have hmod : Φ (y + 2 ^ k) % 2 ^ k = Φ y % 2 ^ k := hΦ.compat k (y + 2 ^ k) y (by simp)
  rw [hmod, hΦ.fiber_flip k y]
  have hmaj := maj_flip_xor ((Φ y).testBit k) (c.testBit k) (decide (Φ y % 2 ^ k + c % 2 ^ k ≥ 2 ^ k))
  generalize (Φ y).testBit (k + 1) = p1
  generalize (Φ (y + 2 ^ k)).testBit (k + 1) = p2
  generalize c.testBit (k + 1) = ck1
  generalize (Φ y).testBit k = a
  generalize c.testBit k = b
  generalize decide (Φ y % 2 ^ k + c % 2 ^ k ≥ 2 ^ k) = r at hmaj ⊢
  cases p1 <;> cases p2 <;> cases ck1 <;> cases a <;> cases b <;> cases r <;> rfl

/-- **Core Engine Theorem B1 (`majority_carry_holonomy`)**:
    For ANY `TPerm Φ`, ANY `c`, and ANY doubled cycle `2L` at level `k+1` (with `L` even):
    `holonomy (Φ · + c) (k+1) x0 (2*L)` equals the XOR of the twist derivative `β` and
    the carry-overflow parity over the half-cycle `y_i = iter T i x0 % 2^k`! -/
theorem majority_carry_holonomy {Φ : Nat → Nat} (hΦ : TPerm Φ) (c k x0 L : Nat)
    (hcyc : iter (fun x => Φ x + c) L x0 % 2 ^ k = x0 % 2 ^ k)
    (hhol : holonomy (fun x => Φ x + c) k x0 L = true)
    (heven : L % 2 = 0) :
    holonomy (fun x => Φ x + c) (k + 1) x0 (2 * L) =
      xor
        (xorRange L (fun i =>
          let y := iter (fun x => Φ x + c) i x0 % 2 ^ k
          xor ((Φ y).testBit (k + 1)) ((Φ (y + 2 ^ k)).testBit (k + 1))))
        (xorRange L (fun i =>
          let y := iter (fun x => Φ x + c) i x0 % 2 ^ k
          decide (Φ y % 2 ^ k + c % 2 ^ k ≥ 2 ^ k))) := by
  have hT := hΦ.add_const c
  rw [doubled_fiber_holonomy hT k x0 L hcyc hhol]
  have hrw : xorRange L (fun i =>
      let y := iter (fun x => Φ x + c) i x0 % 2 ^ k
      xor ((Φ y + c).testBit (k + 1)) ((Φ (y + 2 ^ k) + c).testBit (k + 1))) =
    xorRange L (fun i =>
      let y := iter (fun x => Φ x + c) i x0 % 2 ^ k
      xor (xor (xor ((Φ y).testBit (k + 1)) ((Φ (y + 2 ^ k)).testBit (k + 1))) (c.testBit k))
          (decide (Φ y % 2 ^ k + c % 2 ^ k ≥ 2 ^ k))) := by
    apply xorRange_congr
    intro i _
    exact add_const_fiber_diff hΦ c k _
  rw [hrw, xorRange_xor, xorRange_xor, xorRange_const]
  have hne : (L % 2 == 1) = false := by rw [heven]; rfl
  simp [hne]

/-- Exact carry-overflow parity over `[0, N)`: `#{z < N : z + c0 ≥ N} mod 2 = (c0 % 2 == 1)`. -/
theorem xorRange_carry_full (N c0 : Nat) (hc0 : c0 < N) :
    xorRange N (fun z => decide (z + c0 ≥ N)) = (c0 % 2 == 1) := by
  have hsplit : N = (N - c0) + c0 := by omega
  conv => lhs; arg 1; rw [hsplit]
  rw [xorRange_add]
  have hlow : xorRange (N - c0) (fun z => decide (z + c0 ≥ N)) = false := by
    rw [xorRange_congr (N - c0) _ (fun _ => false) (fun z hz => by simp; omega)]
    exact xorRange_false _
  have hhigh : xorRange c0 (fun i => decide ((N - c0 + i) + c0 ≥ N)) = (c0 % 2 == 1) := by
    rw [xorRange_congr c0 _ (fun _ => true) (fun i _ => by simp; omega), xorRange_const]
    cases h : (c0 % 2 == 1) <;> rfl
  rw [hlow, hhigh, Bool.false_xor]

/-! ### Sub-Engine 2: Universal Holonomy-Conservation Compiler -/

/-- **Core Engine Theorem B2 (`holonomy_conservation_lift`)**:
    For ANY `TPerm T`, if on `[0, 2^k)` there exists an odd constant `M` (independent of `y`)
    such that `T (y + 2^k) % 2^(k+2) = (T y + 2^k * M) % 2^(k+2)` for all `y < 2^k`,
    and `L` is even, then holonomy is **EXACTLY CONSERVED**:
    `holonomy T (k + 1) x0 (2 * L) = holonomy T k x0 L`! -/
theorem holonomy_conservation_lift {T : Nat → Nat} (hT : TPerm T) (k x0 L M : Nat)
    (hcyc : iter T L x0 % 2 ^ k = x0 % 2 ^ k)
    (hhol : holonomy T k x0 L = true)
    (heven : L % 2 = 0)
    (hModd : M % 2 = 1)
    (hinc : ∀ y < 2 ^ k, T (y + 2 ^ k) % 2 ^ (k + 2) = (T y + 2 ^ k * M) % 2 ^ (k + 2)) :
    holonomy T (k + 1) x0 (2 * L) = holonomy T k x0 L := by
  rw [doubled_fiber_holonomy hT k x0 L hcyc hhol]
  have hdiff : ∀ y < 2 ^ k,
      xor ((T y).testBit (k + 1)) ((T (y + 2 ^ k)).testBit (k + 1)) =
        xor ((T y).testBit k) (M.testBit 1) := by
    intro y hy
    have hbit : (T (y + 2 ^ k)).testBit (k + 1) = (T y + 2 ^ k * M).testBit (k + 1) := by
      rw [← testBit_mod_pow2_of_lt (T (y + 2 ^ k)) (k + 2) (k + 1) (by omega),
          hinc y hy,
          testBit_mod_pow2_of_lt (T y + 2 ^ k * M) (k + 2) (k + 1) (by omega)]
    rw [hbit, testBit_add_eq (T y) (2 ^ k * M) (k + 1)]
    -- Bit `k+1` of `2^k * M` is `M.testBit 1`.
    have hm_bit : (2 ^ k * M).testBit (k + 1) = M.testBit 1 := by
      rw [testBit_eq_div_mod, testBit_eq_div_mod, Nat.pow_succ, Nat.pow_one]
      have hdiv : (2 ^ k * M) / (2 ^ k * 2) = M / 2 := by
        rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left M (pow2_pos k)]
      rw [hdiv]
    -- Carry into bit `k+1` of `T y + 2^k * M` is `(T y).testBit k` (since `M` is odd!).
    have hm_mod : (2 ^ k * M) % 2 ^ (k + 1) = 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_mod_mul_left, hModd, Nat.mul_one]
    have hcarry : decide (T y % 2 ^ (k + 1) + (2 ^ k * M) % 2 ^ (k + 1) ≥ 2 ^ (k + 1)) =
        (T y).testBit k := by
      rw [hm_mod, mod_pow2_succ_eq (T y) k]
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      have hlt := Nat.mod_lt (T y) (pow2_pos k)
      rw [hpow]
      cases (T y).testBit k <;> simp <;> omega
    rw [hm_bit, hcarry]
    cases (T y).testBit (k + 1) <;> cases (T y).testBit k <;> cases M.testBit 1 <;> rfl
  have hsum : xorRange L (fun i =>
      let y := iter T i x0 % 2 ^ k
      xor ((T y).testBit (k + 1)) ((T (y + 2 ^ k)).testBit (k + 1))) =
    xorRange L (fun i => xor ((T (iter T i x0 % 2 ^ k)).testBit k) (M.testBit 1)) := by
    apply xorRange_congr
    intro i _
    exact hdiff _ (Nat.mod_lt _ (pow2_pos k))
  rw [hsum, xorRange_xor, xorRange_const]
  have hne : (L % 2 == 1) = false := by rw [heven]; rfl
  simp [hne, holonomy]

/-! ### Section 5: Core Engine Theorem C — Tower-to-Valuation & Periodicity Bridge -/

/-- **Constructive Doubled-Fiber Bijection Lifter**:
    If `holonomy f k x0 L = true` and `encode` lifts via `encode (j + L) = encode j + 2^k`,
    then `OrbitBijection` lifts automatically from `(k, L)` to `(k + 1, 2 * L)`! -/
theorem OrbitBijection.lift {f : Nat → Nat} (hf : TPerm f) {k x0 L : Nat} {encode : Nat → Nat}
    (hb : OrbitBijection f k x0 L encode)
    (hhol : holonomy f k x0 L = true)
    (henc_lift : ∀ j < L, encode (j + L) = encode j + 2 ^ k) :
    OrbitBijection f (k + 1) x0 (2 * L) encode := by
  have ⟨_, hcyc2⟩ := holonomy_double_cycle hf k x0 L hb.cyc hhol
  obtain ⟨fwd, inv, hfwd_lt, hinv_lt, hinv_fwd, hfwd_inv, hmod_fwd⟩ := hb.bij
  refine ⟨hcyc2, ?_, ?_⟩
  · intro j hj
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    by_cases hlt : j < L
    · have := hb.encode_lt j hlt; omega
    · have hj' : j - L < L := by omega
      have heq : j = (j - L) + L := by omega
      rw [heq, henc_lift (j - L) hj']
      have := hb.encode_lt (j - L) hj'; omega
  · let fwd2 : Nat → Nat := fun i =>
      if i < L then
        if (iter f i x0).testBit k then fwd i + L else fwd i
      else
        if (iter f (i - L) x0).testBit k then fwd (i - L) else fwd (i - L) + L
    let inv2 : Nat → Nat := fun j =>
      if j < L then
        let i0 := inv j
        if (iter f i0 x0).testBit k then i0 + L else i0
      else
        let i0 := inv (j - L)
        if (iter f i0 x0).testBit k then i0 else i0 + L
    refine ⟨fwd2, inv2, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      dsimp only [fwd2]
      split
      · next hlt => have := hfwd_lt i hlt; split <;> omega
      · next hge => have := hfwd_lt (i - L) (by omega); split <;> omega
    · intro j hj
      dsimp only [inv2]
      split
      · next hlt => have := hinv_lt j hlt; split <;> omega
      · next hge => have := hinv_lt (j - L) (by omega); split <;> omega
    · intro i hi
      dsimp only [fwd2, inv2]
      by_cases hlt : i < L
      · simp only [hlt, ↓reduceIte]
        have hf_lt := hfwd_lt i hlt
        cases hbit : (iter f i x0).testBit k with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, hf_lt, hinv_fwd i hlt, hbit]
        | true =>
          have hge : ¬ (fwd i + L < L) := by omega
          have hsub : fwd i + L - L = fwd i := by omega
          simp only [↓reduceIte, hge, hsub, hinv_fwd i hlt, hbit]
      · simp only [hlt, ↓reduceIte]
        have hi' : i - L < L := by omega
        have hf_lt := hfwd_lt (i - L) hi'
        cases hbit : (iter f (i - L) x0).testBit k with
        | false =>
          have hge : ¬ (fwd (i - L) + L < L) := by omega
          have hsub : fwd (i - L) + L - L = fwd (i - L) := by omega
          simp only [Bool.false_eq_true, ↓reduceIte, hge, hsub, hinv_fwd (i - L) hi', hbit]
          omega
        | true =>
          simp only [↓reduceIte, hf_lt, hinv_fwd (i - L) hi', hbit]
          omega
    · intro j hj
      dsimp only [fwd2, inv2]
      by_cases hlt : j < L
      · simp only [hlt, ↓reduceIte]
        have hi_lt := hinv_lt j hlt
        cases hbit : (iter f (inv j) x0).testBit k with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, hi_lt, hbit, hfwd_inv j hlt]
        | true =>
          have hge : ¬ (inv j + L < L) := by omega
          have hsub : inv j + L - L = inv j := by omega
          simp only [↓reduceIte, hge, hsub, hbit, hfwd_inv j hlt]
      · simp only [hlt, ↓reduceIte]
        have hj' : j - L < L := by omega
        have hi_lt := hinv_lt (j - L) hj'
        cases hbit : (iter f (inv (j - L)) x0).testBit k with
        | false =>
          have hge : ¬ (inv (j - L) + L < L) := by omega
          have hsub : inv (j - L) + L - L = inv (j - L) := by omega
          simp only [Bool.false_eq_true, ↓reduceIte, hge, hsub, hbit, hfwd_inv (j - L) hj']
          omega
        | true =>
          simp only [↓reduceIte, hi_lt, hbit, hfwd_inv (j - L) hj']
          omega
    · intro i hi
      dsimp only [fwd2]
      by_cases hlt : i < L
      · simp only [hlt, ↓reduceIte]
        have hf_lt := hfwd_lt i hlt
        rw [mod_pow2_succ_eq, hmod_fwd i hlt]
        cases hbit : (iter f i x0).testBit k with
        | false => simp
        | true => simp [henc_lift (fwd i) hf_lt]
      · simp only [hlt, ↓reduceIte]
        have hi' : i - L < L := by omega
        have hi_eq : i = (i - L) + L := by omega
        have hf_lt := hfwd_lt (i - L) hi'
        have ⟨hmod_plus, hflip_plus⟩ := iter_add_period_fiber_flip hf k x0 L (i - L) hb.cyc hhol
        rw [hi_eq, mod_pow2_succ_eq, hmod_plus, hmod_fwd (i - L) hi', hflip_plus]
        cases hbit : (iter f (i - L) x0).testBit k with
        | false =>
          simp [hbit, henc_lift (fwd (i - L)) hf_lt]
        | true =>
          simp [hbit]

/-- Using `OrbitBijection`, any `xorRange L` over the orbit reindexes to `xorRange L` over `encode`. -/
theorem OrbitBijection.xorRange_orbit_eq {f : Nat → Nat} {k x0 L : Nat} {encode : Nat → Nat}
    (hb : OrbitBijection f k x0 L encode) (g : Nat → Bool) :
    xorRange L (fun i => g (iter f i x0 % 2 ^ k)) = xorRange L (fun j => g (encode j)) := by
  obtain ⟨fwd, inv, hfwd_lt, hinv_lt, hinv_fwd, hfwd_inv, hmod_fwd⟩ := hb.bij
  rw [xorRange_congr L _ (fun i => g (encode (fwd i))) (fun i hi => by rw [hmod_fwd i hi])]
  exact xorRange_bij L fwd inv (fun j => g (encode j)) hfwd_lt hinv_lt hfwd_inv hinv_fwd

/-- Orbit periodicity: if `iter f L x0 ≡ x0 (mod 2^k)`, then `iter f (L * q + r) x0 ≡ iter f r x0 (mod 2^k)`. -/
theorem TPerm.iter_mod_periodic {f : Nat → Nat} (hf : TPerm f) (k x0 L : Nat)
    (hcyc : iter f L x0 % 2 ^ k = x0 % 2 ^ k) (q r : Nat) :
    iter f (L * q + r) x0 % 2 ^ k = iter f r x0 % 2 ^ k := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hstep : L * (q + 1) + r = L + (L * q + r) := by rw [Nat.mul_succ]; omega
    rw [hstep, iter_add, hf.iter_mod_compat k L _ _ ih]
    rw [← iter_add, Nat.add_comm, iter_add, hf.iter_mod_compat k r _ _ hcyc]

/-- **Core Engine Theorem C1 (`tower_to_valuation`)**:
    Given ANY `TPerm f` and a certified infinite holonomy-doubling tower starting at `(k0, L0)`:
    - `hcyc_base : iter f L0 0 % 2 ^ k0 = 0`
    - `hhol_tower : ∀ m, holonomy f (k0 + m) 0 (L0 * 2 ^ m) = true`
    Then:
    1. For ALL `m : Nat`: `iter f (L0 * 2 ^ m) 0 % 2 ^ (k0 + m) = 0` and bit `k0 + m` is `true`.
    2. For ALL `n ≥ 1` with `L0 ∣ n`: `v2 (iter f n 0) = k0 + v2 (n / L0)`.
    3. For ALL `n : Nat` with `¬ (L0 ∣ n)` and `iter f (n % L0) 0 % 2 ^ k0 ≠ 0`:
       `v2 (iter f n 0) = v2 (iter f (n % L0) 0)`.
    4. For ALL `m : Nat` and ALL `0 < d < L0 * 2 ^ m` (provided `∀ 0 < r < L0, iter f r 0 % 2 ^ k0 ≠ 0`):
       `iter f d 0 % 2 ^ (k0 + m) ≠ 0`, i.e., `L0 * 2 ^ m` is the **EXACT minimal period** mod `2 ^ (k0 + m)`! -/
theorem tower_level_spec {f : Nat → Nat} (hf : TPerm f) (k0 L0 : Nat)
    (hcyc0 : iter f L0 0 % 2 ^ k0 = 0)
    (hhol : ∀ m, holonomy f (k0 + m) 0 (L0 * 2 ^ m) = true) :
    ∀ m, iter f (L0 * 2 ^ m) 0 % 2 ^ (k0 + m) = 0 ∧
         (iter f (L0 * 2 ^ m) 0).testBit (k0 + m) = true := by
  intro m
  induction m with
  | zero =>
    simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
    refine ⟨hcyc0, ?_⟩
    have hb := iter_testBit_eq_holonomy hf k0 0 L0
    have h0 : (0 : Nat).testBit k0 = false := Nat.zero_testBit k0
    have hh := hhol 0
    simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one] at hh
    rw [hb, h0, hh]
    rfl
  | succ m ih =>
    have hcyc_m : iter f (L0 * 2 ^ m) 0 % 2 ^ (k0 + m) = 0 % 2 ^ (k0 + m) := by
      simp [ih.1]
    have ⟨_, hcyc_next⟩ := holonomy_double_cycle hf (k0 + m) 0 (L0 * 2 ^ m) hcyc_m (hhol m)
    have hmul : L0 * 2 ^ (m + 1) = 2 * (L0 * 2 ^ m) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, ← Nat.mul_assoc, Nat.mul_comm L0 2, Nat.mul_assoc]
    have hadd : k0 + (m + 1) = (k0 + m) + 1 := by omega
    have hcyc_next' : iter f (L0 * 2 ^ (m + 1)) 0 % 2 ^ (k0 + (m + 1)) = 0 := by
      rw [hmul, hadd, hcyc_next]; simp
    refine ⟨hcyc_next', ?_⟩
    have hb := iter_testBit_eq_holonomy hf (k0 + (m + 1)) 0 (L0 * 2 ^ (m + 1))
    have h0 : (0 : Nat).testBit (k0 + (m + 1)) = false := Nat.zero_testBit _
    rw [hb, h0, hhol (m + 1)]
    rfl

/-- Odd-multiple bit-flip lemma: if `g` is a `TPerm` with `g 0 % 2^K = 0` and `(g 0).testBit K = true`,
    then for ALL `q`, `iter g q 0 % 2^K = 0` and `(iter g q 0).testBit K = (q % 2 == 1)`! -/
theorem TPerm.iter_zero_bit_parity {g : Nat → Nat} (hg : TPerm g) (K : Nat)
    (hmod0 : g 0 % 2 ^ K = 0) (hbit0 : (g 0).testBit K = true) (q : Nat) :
    iter g q 0 % 2 ^ K = 0 ∧ (iter g q 0).testBit K = (q % 2 == 1) := by
  induction q with
  | zero => simp [iter]
  | succ q ih =>
    rw [iter_succ]
    refine ⟨?_, ?_⟩
    · rw [hg.compat K (iter g q 0) 0 (by simp [ih.1]), hmod0]
    · rw [hg.bit_lift K (iter g q 0), ih.1, ih.2, hbit0]
      cases hq : q % 2 with
      | zero =>
        have h1 : (q + 1) % 2 = 1 := by omega
        simp [h1]
      | succ m =>
        have hm : m = 0 := by omega
        subst hm
        have h1 : (q + 1) % 2 = 0 := by omega
        simp [h1]

/-- Helper: exact bit-`k0 + v2(n/L0)` is `true` and lower bits are `0` for `L0 ∣ n`, `n ≠ 0`. -/
theorem tower_dvd_mod_testBit {f : Nat → Nat} (hf : TPerm f) (k0 L0 : Nat)
    (hL0 : 0 < L0)
    (hcyc0 : iter f L0 0 % 2 ^ k0 = 0)
    (hhol : ∀ m, holonomy f (k0 + m) 0 (L0 * 2 ^ m) = true)
    (n : Nat) (hn : n ≠ 0) (hdvd : L0 ∣ n) :
    iter f n 0 % 2 ^ (k0 + v2 (n / L0)) = 0 ∧
    (iter f n 0).testBit (k0 + v2 (n / L0)) = true := by
  have hdiv_ne : n / L0 ≠ 0 := by
    obtain ⟨t, ht⟩ := hdvd
    have ht0 : t ≠ 0 := by intro h; subst h; simp at ht; exact hn ht
    rw [ht, Nat.mul_div_cancel_left t hL0]
    exact ht0
  let m := v2 (n / L0)
  let q := (n / L0) / 2 ^ m
  have ⟨hdecomp, hqodd⟩ := v2_decomp (n / L0) hdiv_ne
  have hn_eq : n = (L0 * 2 ^ m) * q := by
    obtain ⟨t, ht⟩ := hdvd
    have hdiv_eq : n / L0 = t := by rw [ht, Nat.mul_div_cancel_left t hL0]
    rw [ht, ← hdiv_eq, Nat.mul_assoc]
    exact congrArg (L0 * ·) hdecomp
  have ⟨hmodK, hbitK⟩ := tower_level_spec hf k0 L0 hcyc0 hhol m
  have ⟨hmod_q, hbit_q⟩ := (hf.iter_tperm (L0 * 2 ^ m)).iter_zero_bit_parity (k0 + m) hmodK hbitK q
  have hiter : iter f n 0 = iter (iter f (L0 * 2 ^ m)) q 0 := by rw [hn_eq, iter_mul]
  rw [hiter]
  refine ⟨hmod_q, ?_⟩
  rw [hbit_q, hqodd]
  rfl

/-- **Core Engine Theorem C1 (Valuation on Multiples of `L0`)**:
    For ANY `TPerm f` with certified doubling tower from `(k0, L0)`,
    for EVERY `n ≥ 1` with `L0 ∣ n`, `v2 (iter f n 0) = k0 + v2 (n / L0)`! -/
theorem tower_to_valuation_dvd {f : Nat → Nat} (hf : TPerm f) (k0 L0 : Nat)
    (hL0 : 0 < L0)
    (hcyc0 : iter f L0 0 % 2 ^ k0 = 0)
    (hhol : ∀ m, holonomy f (k0 + m) 0 (L0 * 2 ^ m) = true)
    (n : Nat) (hn : n ≠ 0) (hdvd : L0 ∣ n) :
    v2 (iter f n 0) = k0 + v2 (n / L0) := by
  have ⟨hmod, hbit⟩ := tower_dvd_mod_testBit hf k0 L0 hL0 hcyc0 hhol n hn hdvd
  exact v2_eq_of_mod_testBit _ _ hmod hbit

/-- **Core Engine Theorem C2 (Valuation on Non-Multiples of `L0`)**:
    For any `n` with `iter f (n % L0) 0 % 2 ^ k0 ≠ 0`, `v2 (iter f n 0) = v2 (iter f (n % L0) 0)`. -/
theorem tower_to_valuation_ndvd {f : Nat → Nat} (hf : TPerm f) (k0 L0 : Nat)
    (hcyc0 : iter f L0 0 % 2 ^ k0 = 0)
    (n : Nat) (hrem : iter f (n % L0) 0 % 2 ^ k0 ≠ 0) :
    v2 (iter f n 0) = v2 (iter f (n % L0) 0) := by
  have hdiv : n = L0 * (n / L0) + n % L0 := (Nat.div_add_mod n L0).symm
  have hmod : iter f n 0 % 2 ^ k0 = iter f (n % L0) 0 % 2 ^ k0 := by
    conv => lhs; rw [hdiv]
    exact hf.iter_mod_periodic k0 0 L0 (by simpa using hcyc0) (n / L0) (n % L0)
  exact v2_eq_of_mod_eq_and_lt _ _ k0 (v2_ne_zero_of_lt_mod _ k0 hrem) hmod (v2_lt_of_mod_ne_zero _ k0 hrem)

/-- **Core Engine Theorem C3 (Exact Minimal Periodicity Mod `2^(k0 + m)`)**:
    Under the certified doubling tower plus base minimality (`∀ 0 < r < L0, iter f r 0 % 2^k0 ≠ 0`),
    for EVERY `m : Nat`, `L0 * 2 ^ m` is the **EXACT minimal period** of `iter f · 0` modulo `2 ^ (k0 + m)`! -/
theorem tower_to_min_period {f : Nat → Nat} (hf : TPerm f) (k0 L0 : Nat)
    (hL0 : 0 < L0)
    (hcyc0 : iter f L0 0 % 2 ^ k0 = 0)
    (hmin0 : ∀ r, 0 < r → r < L0 → iter f r 0 % 2 ^ k0 ≠ 0)
    (hhol : ∀ m, holonomy f (k0 + m) 0 (L0 * 2 ^ m) = true)
    (m : Nat) :
    iter f (L0 * 2 ^ m) 0 % 2 ^ (k0 + m) = 0 ∧
    ∀ d, 0 < d → d < L0 * 2 ^ m → iter f d 0 % 2 ^ (k0 + m) ≠ 0 := by
  refine ⟨(tower_level_spec hf k0 L0 hcyc0 hhol m).1, ?_⟩
  intro d hdpos hdlt hzero
  by_cases hdvd : L0 ∣ d
  · have ⟨_, hbit⟩ := tower_dvd_mod_testBit hf k0 L0 hL0 hcyc0 hhol d (by omega) hdvd
    have hdiv_lt : d / L0 < 2 ^ m := by
      obtain ⟨t, ht⟩ := hdvd
      rw [ht, Nat.mul_div_cancel_left t hL0]
      exact (Nat.mul_lt_mul_left hL0).mp (ht ▸ hdlt)
    have hdiv_pos : d / L0 ≠ 0 := by
      obtain ⟨t, ht⟩ := hdvd
      rw [ht, Nat.mul_div_cancel_left t hL0]
      intro h0; subst h0; simp at ht; omega
    have hv_lt : v2 (d / L0) < m := by
      have ⟨hd2, ho⟩ := v2_decomp (d / L0) hdiv_pos
      have hqpos : 0 < (d / L0) / 2 ^ v2 (d / L0) := by
        cases hq0 : (d / L0) / 2 ^ v2 (d / L0) with
        | zero => rw [hq0] at ho; simp at ho
        | succ _ => exact Nat.succ_pos _
      have hge : 2 ^ v2 (d / L0) ≤ d / L0 := by
        calc 2 ^ v2 (d / L0) = 2 ^ v2 (d / L0) * 1 := (Nat.mul_one _).symm
          _ ≤ 2 ^ v2 (d / L0) * ((d / L0) / 2 ^ v2 (d / L0)) := Nat.mul_le_mul_left _ hqpos
          _ = d / L0 := hd2.symm
      rcases Nat.lt_or_ge (v2 (d / L0)) m with hlt | hmle
      · exact hlt
      · have hpowle : 2 ^ m ≤ 2 ^ v2 (d / L0) := Nat.pow_le_pow_right (by omega) hmle
        omega
    have hfalse : (iter f d 0).testBit (k0 + v2 (d / L0)) = false := by
      rw [← testBit_mod_pow2_of_lt (iter f d 0) (k0 + m) (k0 + v2 (d / L0)) (by omega), hzero]
      exact Nat.zero_testBit _
    rw [hbit] at hfalse
    cases hfalse
  · have hrpos : 0 < d % L0 := by
      rcases Nat.eq_zero_or_pos (d % L0) with h0 | hpos
      · exact absurd (Nat.dvd_of_mod_eq_zero h0) hdvd
      · exact hpos
    have hrlt : d % L0 < L0 := Nat.mod_lt d hL0
    have hdiv : d = L0 * (d / L0) + d % L0 := (Nat.div_add_mod d L0).symm
    have hmod_r : iter f d 0 % 2 ^ k0 = iter f (d % L0) 0 % 2 ^ k0 := by
      conv => lhs; rw [hdiv]
      exact hf.iter_mod_periodic k0 0 L0 (by simpa using hcyc0) (d / L0) (d % L0)
    have hdvd_pow : 2 ^ k0 ∣ 2 ^ (k0 + m) := Nat.pow_dvd_pow 2 (by omega)
    have hzero_k0 : iter f d 0 % 2 ^ k0 = 0 := by
      have := Nat.mod_mod_of_dvd (iter f d 0) hdvd_pow
      rw [hzero, Nat.zero_mod] at this
      exact this.symm
    rw [hzero_k0] at hmod_r
    exact hmin0 (d % L0) hrpos hrlt hmod_r.symm

/-- **Core Engine Theorem C4 (`shift_homogeneity_lift`)**:
    If `f (2^e * x) = 2^e * g x` for all `x`, then `iter f n 0 = 2^e * iter g n 0`,
    and hence `v2 (iter f n 0) = e + v2 (iter g n 0)` whenever `iter g n 0 ≠ 0`! -/
theorem iter_shift_homogeneous (f g : Nat → Nat) (e : Nat)
    (hhom : ∀ x, f (2 ^ e * x) = 2 ^ e * g x) (n : Nat) :
    iter f n 0 = 2 ^ e * iter g n 0 := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
    rw [iter_succ, iter_succ, ih, hhom]

theorem v2_shift_homogeneous (f g : Nat → Nat) (e n : Nat)
    (hhom : ∀ x, f (2 ^ e * x) = 2 ^ e * g x) (hne : iter g n 0 ≠ 0) :
    v2 (iter f n 0) = e + v2 (iter g n 0) := by
  rw [iter_shift_homogeneous f g e hhom n, v2_mul_pow2 e _ hne]

end CarryHolonomyEngine
namespace CarryHolonomyEngine
theorem testBit_pow2_mul (s x k : Nat) :
    (2 ^ s * x).testBit k = (if s ≤ k then x.testBit (k - s) else false) := by
  rw [testBit_eq_div_mod]
  by_cases h : s ≤ k
  · simp only [h, ↓reduceIte, testBit_eq_div_mod]
    have hpow : 2 ^ k = 2 ^ s * 2 ^ (k - s) := by
      rw [← Nat.pow_add]
      congr 1; omega
    rw [hpow, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left x (pow2_pos s)]
  · simp only [h, ↓reduceIte]
    have hlt : k < s := by omega
    have hpow : 2 ^ s = 2 ^ k * (2 * 2 ^ (s - k - 1)) := by
      rw [Nat.mul_comm 2, ← Nat.pow_succ, ← Nat.pow_add]
      congr 1; omega
    rw [hpow, Nat.mul_assoc, Nat.mul_div_cancel_left _ (pow2_pos k)]
    have hev : (2 * (2 ^ (s - k - 1) * x)) % 2 = 0 := by omega
    rw [Nat.mul_assoc, hev]
    rfl

theorem pow2_mul_xor (e x y : Nat) :
    (2 ^ e * x) ^^^ (2 ^ e * y) = 2 ^ e * (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, testBit_pow2_mul, testBit_pow2_mul, testBit_pow2_mul]
  by_cases h : e ≤ k
  · simp [h, Nat.testBit_xor]
  · simp [h]

theorem pow2_mul_and (e x y : Nat) :
    (2 ^ e * x) &&& (2 ^ e * y) = 2 ^ e * (x &&& y) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, testBit_pow2_mul, testBit_pow2_mul, testBit_pow2_mul]
  by_cases h : e ≤ k
  · simp [h, Nat.testBit_and]
  · simp [h]

theorem testBit_add_pow2_of_lt_bound (y k : Nat) (hy : y < 2 ^ k) :
    (y + 2 ^ k).testBit (k + 1) = false ∧ y.testBit (k + 1) = false := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  have h1 : (y + 2 ^ k) / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
  have h2 : y / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
  rw [testBit_eq_div_mod, testBit_eq_div_mod, h1, h2]
  exact ⟨rfl, rfl⟩

theorem testBit_of_lt_pow2 (y k i : Nat) (hy : y < 2 ^ k) (hi : k ≤ i) :
    y.testBit i = false := by
  rw [← Nat.mod_eq_of_lt hy, testBit_mod_pow2_of_ge y k i hi]

theorem xor_add_pow2_of_lt (y c k : Nat) (hy : y < 2 ^ k) :
    ((y + 2 ^ k) ^^^ c) % 2 ^ (k + 2) =
      ((y ^^^ c) + 2 ^ k * (if c.testBit k then 3 else 1)) % 2 ^ (k + 2) := by
  -- Compare bit-by-bit for `i < k + 2`!
  -- Actually even simpler: relate `(y + 2^k) ^^^ c` directly to `y ^^^ c` as exact `Nat`!
  have hlow : ∀ i < k, ((y + 2 ^ k) ^^^ c).testBit i = (y ^^^ c).testBit i := by
    intro i hi
    rw [Nat.testBit_xor, Nat.testBit_xor, testBit_add_pow2_lt y k i hi]
  have hbitk_y : y.testBit k = false := testBit_of_lt_pow2 y k k hy (Nat.le_refl k)
  have hbitk_yp : (y + 2 ^ k).testBit k = true := by
    rw [testBit_add_pow2_self, hbitk_y]; rfl
  have hhigh : ∀ i, k < i → ((y + 2 ^ k) ^^^ c).testBit i = (y ^^^ c).testBit i := by
    intro i hi
    rw [Nat.testBit_xor, Nat.testBit_xor]
    have hpow : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
    have hlt1 : y + 2 ^ k < 2 ^ i := by
      have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      omega
    have hlt2 : y < 2 ^ i := by omega
    rw [testBit_of_lt_pow2 (y + 2 ^ k) i i hlt1 (Nat.le_refl i),
        testBit_of_lt_pow2 y i i hlt2 (Nat.le_refl i)]
  cases hc : c.testBit k with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_one]
    have heq : (y + 2 ^ k) ^^^ c = (y ^^^ c) + 2 ^ k := by
      apply Nat.eq_of_testBit_eq
      intro i
      rcases Nat.lt_trichotomy i k with hlt | heqk | hgt
      · rw [hlow i hlt, testBit_add_pow2_lt _ k i hlt]
      · subst heqk
        rw [Nat.testBit_xor, hbitk_yp, hc, testBit_add_pow2_self, Nat.testBit_xor, hbitk_y, hc]
        rfl
      · rw [hhigh i hgt]
        -- Since `(y ^^^ c).testBit k = false`, adding `2^k` causes NO carry above bit `k`!
        have hno_carry : ((y ^^^ c) + 2 ^ k).testBit i = (y ^^^ c).testBit i := by
          rw [testBit_eq_div_mod, testBit_eq_div_mod]
          have hdiv : ((y ^^^ c) + 2 ^ k) / 2 ^ i = (y ^^^ c) / 2 ^ i := by
            have hdecomp := Nat.div_add_mod (y ^^^ c) (2 ^ i)
            have hpow : 2 ^ (k + 1) ∣ 2 ^ i := Nat.pow_dvd_pow 2 hgt
            have hmod_lt : (y ^^^ c) % 2 ^ i + 2 ^ k < 2 ^ i := by
              -- Bit `k` of `y ^^^ c` is `false`, so `(y ^^^ c) % 2^i + 2^k < 2^i`!
              have hbit_false : ((y ^^^ c) % 2 ^ i).testBit k = false := by
                rw [testBit_mod_pow2_of_lt _ i k hgt, Nat.testBit_xor, hbitk_y, hc]; rfl
              have hle : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hgt
              -- Write `z := (y ^^^ c) % 2^i = 2^(k+1) * (z / 2^(k+1)) + z % 2^(k+1)`.
              -- Since bit `k` of `z` is `false`, `z % 2^(k+1) = z % 2^k < 2^k`!
              let z := (y ^^^ c) % 2 ^ i
              have hz_lt : z < 2 ^ i := Nat.mod_lt _ (pow2_pos i)
              have hz_mod : z % 2 ^ (k + 1) = z % 2 ^ k := by
                rw [mod_pow2_succ_eq z k, hbit_false]; simp
              have hz_div_lt : z / 2 ^ (k + 1) < 2 ^ i / 2 ^ (k + 1) := by
                obtain ⟨q, hq⟩ := hpow
                rw [hq, Nat.mul_div_cancel_left q (pow2_pos (k + 1))]
                have : 2 ^ (k + 1) * (z / 2 ^ (k + 1)) ≤ z := Nat.mul_div_le z _
                have hqlt : 2 ^ (k + 1) * (z / 2 ^ (k + 1)) < 2 ^ (k + 1) * q := by rw [← hq]; omega
                exact (Nat.mul_lt_mul_left (pow2_pos (k + 1))).mp hqlt
              have hdiv_add := Nat.div_add_mod z (2 ^ (k + 1))
              have hz_mk : z % 2 ^ k < 2 ^ k := Nat.mod_lt z (pow2_pos k)
              have h2k1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
              obtain ⟨q, hq⟩ := hpow
              have hqeq : 2 ^ i / 2 ^ (k + 1) = q := by rw [hq, Nat.mul_div_cancel_left q (pow2_pos (k + 1))]
              rw [hqeq] at hz_div_lt
              have hstep : 2 ^ (k + 1) * (z / 2 ^ (k + 1) + 1) ≤ 2 ^ i := by
                rw [hq]
                exact Nat.mul_le_mul_left _ hz_div_lt
              rw [Nat.mul_add, Nat.mul_one] at hstep
              omega
            have hadd_eq : (y ^^^ c) + 2 ^ k = 2 ^ i * ((y ^^^ c) / 2 ^ i) + ((y ^^^ c) % 2 ^ i + 2 ^ k) := by
              omega
            rw [hadd_eq, Nat.mul_add_div (pow2_pos i), Nat.div_eq_of_lt hmod_lt, Nat.add_zero]
          rw [hdiv]
        exact hno_carry.symm
    rw [heq]
  | true =>
    simp only [↓reduceIte]
    -- Here `((y + 2^k) ^^^ c) + 2^k = y ^^^ c`!
    have heq : ((y + 2 ^ k) ^^^ c) + 2 ^ k = y ^^^ c := by
      apply Nat.eq_of_testBit_eq
      intro i
      rcases Nat.lt_trichotomy i k with hlt | heqk | hgt
      · rw [testBit_add_pow2_lt _ k i hlt, hlow i hlt]
      · subst heqk
        rw [testBit_add_pow2_self, Nat.testBit_xor, Nat.testBit_xor, hbitk_yp, hbitk_y, hc]
        rfl
      · have hbit_false : (((y + 2 ^ k) ^^^ c) % 2 ^ i).testBit k = false := by
          rw [testBit_mod_pow2_of_lt _ i k hgt, Nat.testBit_xor, hbitk_yp, hc]; rfl
        have hno_carry : (((y + 2 ^ k) ^^^ c) + 2 ^ k).testBit i = ((y + 2 ^ k) ^^^ c).testBit i := by
          rw [testBit_eq_div_mod, testBit_eq_div_mod]
          have hpow : 2 ^ (k + 1) ∣ 2 ^ i := Nat.pow_dvd_pow 2 hgt
          let z := ((y + 2 ^ k) ^^^ c) % 2 ^ i
          have hz_lt : z < 2 ^ i := Nat.mod_lt _ (pow2_pos i)
          have hz_mod : z % 2 ^ (k + 1) = z % 2 ^ k := by
            rw [mod_pow2_succ_eq z k, hbit_false]; simp
          obtain ⟨q, hq⟩ := hpow
          have hz_div_lt : z / 2 ^ (k + 1) < q := by
            have : 2 ^ (k + 1) * (z / 2 ^ (k + 1)) ≤ z := Nat.mul_div_le z _
            have hqlt : 2 ^ (k + 1) * (z / 2 ^ (k + 1)) < 2 ^ (k + 1) * q := by rw [← hq]; omega
            exact (Nat.mul_lt_mul_left (pow2_pos (k + 1))).mp hqlt
          have hdiv_add := Nat.div_add_mod z (2 ^ (k + 1))
          have hz_mk : z % 2 ^ k < 2 ^ k := Nat.mod_lt z (pow2_pos k)
          have h2k1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
          have hstep : 2 ^ (k + 1) * (z / 2 ^ (k + 1) + 1) ≤ 2 ^ i := by
            rw [hq]; exact Nat.mul_le_mul_left _ hz_div_lt
          rw [Nat.mul_add, Nat.mul_one] at hstep
          have hmod_lt : z + 2 ^ k < 2 ^ i := by omega
          have hdecomp := Nat.div_add_mod ((y + 2 ^ k) ^^^ c) (2 ^ i)
          have hadd_eq : ((y + 2 ^ k) ^^^ c) + 2 ^ k =
              2 ^ i * (((y + 2 ^ k) ^^^ c) / 2 ^ i) + (z + 2 ^ k) := by omega
          rw [hadd_eq, Nat.mul_add_div (pow2_pos i), Nat.div_eq_of_lt hmod_lt, Nat.add_zero]
        rw [hno_carry, hhigh i hgt]
    -- Now `((y + 2^k) ^^^ c) + 2^(k+2) = (y ^^^ c) + 2^k * 3`!
    have hpow2 : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
    have hsum : ((y + 2 ^ k) ^^^ c) + 2 ^ (k + 2) = (y ^^^ c) + 2 ^ k * 3 := by
      rw [← heq, hpow2]; omega
    rw [← Nat.add_mod_right _ (2 ^ (k + 2)), hsum]

/-! ## Section 7: Theorem 1 — Complete Gray-Carry Phase-Transition Dichotomy -/

theorem grayPhi_zero (s : Nat) : grayPhi s 0 = 0 := by simp [grayPhi]

theorem grayPhi_tperm (s : Nat) (hs : 1 ≤ s) : TPerm (grayPhi s) where
  compat k x y hxy := by
    apply mod_pow2_of_testBit_eq
    intro i hi
    simp only [grayPhi, Nat.testBit_xor, testBit_pow2_mul]
    have hxi : x.testBit i = y.testBit i := by
      rw [← testBit_mod_pow2_of_lt x k i hi, hxy, testBit_mod_pow2_of_lt y k i hi]
    rw [hxi]
    by_cases hsi : s ≤ i
    · simp only [hsi, ↓reduceIte]
      have hxis : x.testBit (i - s) = y.testBit (i - s) := by
        rw [← testBit_mod_pow2_of_lt x k (i - s) (by omega), hxy,
            testBit_mod_pow2_of_lt y k (i - s) (by omega)]
      rw [hxis]
    · simp [hsi]
  fiber_flip k x := by
    simp only [grayPhi, Nat.testBit_xor, testBit_pow2_mul, testBit_add_pow2_self]
    by_cases hsk : s ≤ k
    · simp only [hsk, ↓reduceIte, testBit_add_pow2_lt x k (k - s) (by omega)]
      cases x.testBit k <;> cases x.testBit (k - s) <;> rfl
    · simp [hsk]

theorem grayCarryStep_tperm (s c : Nat) (hs : 1 ≤ s) : TPerm (grayCarryStep s c) :=
  (grayPhi_tperm s hs).add_const c

/-- Shift-homogeneity of Gray-carry: scaling `x` and `c` by `2^e` scales the output by `2^e`. -/
theorem grayCarryStep_shift_hom (s e c0 x : Nat) :
    grayCarryStep s (2 ^ e * c0) (2 ^ e * x) = 2 ^ e * grayCarryStep s c0 x := by
  simp only [grayCarryStep, grayPhi]
  have h1 : 2 ^ s * (2 ^ e * x) = 2 ^ e * (2 ^ s * x) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ s) (2 ^ e), Nat.mul_assoc]
  rw [h1, pow2_mul_xor, Nat.mul_add]

/-! ### Regime I: `s ≥ 2` (Universal 2-Adic Ergodicity & Exact `v2(a_n) = v2(c) + v2(n)`) -/

theorem grayPhi_beta_ge2 (s k y : Nat) (hs : 2 ≤ s) (hy : y < 2 ^ k) :
    xor ((grayPhi s y).testBit (k + 1)) ((grayPhi s (y + 2 ^ k)).testBit (k + 1)) = false := by
  simp only [grayPhi, Nat.testBit_xor, testBit_pow2_mul]
  have ⟨h1, h2⟩ := testBit_add_pow2_of_lt_bound y k hy
  rw [h1, h2]
  by_cases hsk : s ≤ k + 1
  · simp only [hsk, ↓reduceIte, testBit_add_pow2_lt y k (k + 1 - s) (by omega)]
    cases y.testBit (k + 1 - s) <;> rfl
  · simp [hsk]

/-- Certified infinite ergodic holonomy tower for `grayCarryStep s c` when `s ≥ 2` and `c` odd. -/
theorem grayCarry_ge2_tower (s c : Nat) (hs : 2 ≤ s) (hc : c % 2 = 1) :
    ∀ k, OrbitBijection (grayCarryStep s c) k 0 (2 ^ k) id ∧
         holonomy (grayCarryStep s c) k 0 (2 ^ k) = true := by
  have hΦ := grayPhi_tperm s (by omega)
  have hT := grayCarryStep_tperm s c (by omega)
  intro k
  induction k with
  | zero =>
    refine ⟨⟨by simp [Nat.mod_one], fun j hj => hj,
      ⟨id, id, fun _ h => h, fun _ h => h, fun _ _ => rfl, fun _ _ => rfl,
        fun i hi => by simp [Nat.mod_one]; omega⟩⟩, ?_⟩
    simp only [holonomy, Nat.pow_zero, xorRange, Nat.mod_one, grayCarryStep, grayPhi_zero, Nat.zero_add]
    rw [testBit_eq_div_mod, Nat.pow_zero, Nat.div_one, hc]
    rfl
  | succ k ih =>
    obtain ⟨hb_k, hhol_k⟩ := ih
    have hb_next : OrbitBijection (grayCarryStep s c) (k + 1) 0 (2 ^ (k + 1)) id := by
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [h2]
      exact hb_k.lift hT hhol_k (fun j _ => rfl)
    refine ⟨hb_next, ?_⟩
    cases k with
    | zero =>
      simp only [holonomy, Nat.pow_one, xorRange, iter, Nat.zero_mod, grayCarryStep, grayPhi_zero, Nat.zero_add]
      rw [hc]
      have hphi1_mod4 : grayPhi s 1 % 2 ^ 2 = 1 % 2 ^ 2 := by
        apply mod_pow2_of_testBit_eq _ _ 2
        intro i hi
        simp only [grayPhi, Nat.testBit_xor, testBit_pow2_mul]
        have hns : ¬ (s ≤ i) := by omega
        simp [hns]
      have hbit1 : (grayPhi s 1 + c).testBit 1 = (1 + c).testBit 1 := by
        rw [← testBit_mod_pow2_of_lt (grayPhi s 1 + c) 2 1 (by omega),
            ← testBit_mod_pow2_of_lt (1 + c) 2 1 (by omega),
            Nat.add_mod (grayPhi s 1) c (2 ^ 2), hphi1_mod4, ← Nat.add_mod 1 c (2 ^ 2)]
      rw [hbit1, testBit_eq_div_mod, testBit_eq_div_mod]
      have hc4 := Nat.mod_lt c (by omega : 0 < 4)
      have hdiv1 : (c / 2) % 2 = (c % 4) / 2 := by omega
      have hdiv2 : ((1 + c) / 2) % 2 = ((1 + c % 4) / 2) % 2 := by omega
      have hodd4 : (c % 4) % 2 = 1 := by omega
      rw [Nat.pow_one, hdiv1, hdiv2]
      generalize c % 4 = r at hc4 hodd4 ⊢
      match r with
      | 1 => rfl
      | 3 => rfl
    | succ k' =>
      have h2 : 2 ^ (k' + 1 + 1) = 2 * 2 ^ (k' + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [h2]
      have heven : 2 ^ (k' + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
      change holonomy (fun x => grayPhi s x + c) (k' + 1 + 1) 0 (2 * 2 ^ (k' + 1)) = true
      rw [majority_carry_holonomy hΦ c (k' + 1) 0 (2 ^ (k' + 1)) hb_k.cyc hhol_k heven]
      have hbeta : xorRange (2 ^ (k' + 1)) (fun i =>
          let y := iter (fun x => grayPhi s x + c) i 0 % 2 ^ (k' + 1)
          xor ((grayPhi s y).testBit (k' + 1 + 1)) ((grayPhi s (y + 2 ^ (k' + 1))).testBit (k' + 1 + 1))) = false := by
        rw [xorRange_congr (2 ^ (k' + 1)) _ (fun _ => false)
          (fun i _ => grayPhi_beta_ge2 s (k' + 1) _ hs (Nat.mod_lt _ (pow2_pos _)))]
        exact xorRange_false _
      rw [hbeta, Bool.false_xor]
      change xorRange (2 ^ (k' + 1)) (fun i =>
        decide (grayPhi s (iter (grayCarryStep s c) i 0 % 2 ^ (k' + 1)) % 2 ^ (k' + 1) +
          c % 2 ^ (k' + 1) ≥ 2 ^ (k' + 1))) = true
      rw [hb_k.xorRange_orbit_eq (fun y => decide (grayPhi s y % 2 ^ (k' + 1) + c % 2 ^ (k' + 1) ≥ 2 ^ (k' + 1)))]
      simp only [id]
      rw [xorRange_tperm_bij hΦ (k' + 1) (fun z => decide (z + c % 2 ^ (k' + 1) ≥ 2 ^ (k' + 1)))]
      rw [xorRange_carry_full (2 ^ (k' + 1)) (c % 2 ^ (k' + 1)) (Nat.mod_lt c (pow2_pos _))]
      have hodd_mod : (c % 2 ^ (k' + 1)) % 2 = 1 := by
        have hdvd : 2 ∣ 2 ^ (k' + 1) := ⟨2 ^ k', by rw [Nat.pow_succ, Nat.mul_comm]⟩
        rw [Nat.mod_mod_of_dvd c hdvd, hc]
      rw [hodd_mod]; rfl

/-- **Theorem 1A (Gray-Carry Ergodicity for `s ≥ 2`, odd `c`)**:
    For ALL `s ≥ 2`, ALL odd `c`, and ALL `k : Nat`, the orbit modulo `2^k` has exact minimal period `2^k`,
    and for ALL `n ≥ 1`, `v2 (iter (grayCarryStep s c) n 0) = v2 n`! -/
theorem grayCarry_ge2_odd_period (s c k : Nat) (hs : 2 ≤ s) (hc : c % 2 = 1) :
    iter (grayCarryStep s c) (2 ^ k) 0 % 2 ^ k = 0 ∧
    ∀ d, 0 < d → d < 2 ^ k → iter (grayCarryStep s c) d 0 % 2 ^ k ≠ 0 := by
  have hT := grayCarryStep_tperm s c (by omega)
  have htow := grayCarry_ge2_tower s c hs hc
  have h := tower_to_min_period hT 0 1 (by omega) (by simp [Nat.mod_one])
    (fun r hr1 hr2 => by omega) (fun m => by simpa using (htow m).2) k
  simpa using h

theorem grayCarry_ge2_odd_v2 (s c n : Nat) (hs : 2 ≤ s) (hc : c % 2 = 1) (hn : n ≠ 0) :
    v2 (iter (grayCarryStep s c) n 0) = v2 n := by
  have hT := grayCarryStep_tperm s c (by omega)
  have htow := grayCarry_ge2_tower s c hs hc
  have h := tower_to_valuation_dvd hT 0 1 (by omega) (by simp [Nat.mod_one])
    (fun m => by simpa using (htow m).2) n hn (Nat.one_dvd n)
  simpa using h

/-- **Theorem 1A (Full General Form, ALL `c ≥ 1`, ALL `s ≥ 2`, ALL `n ≥ 1`)**:
    `v2 (iter (grayCarryStep s c) n 0) = v2 c + v2 n`! -/
theorem grayCarry_ge2_v2 (s c n : Nat) (hs : 2 ≤ s) (hc : c ≠ 0) (hn : n ≠ 0) :
    v2 (iter (grayCarryStep s c) n 0) = v2 c + v2 n := by
  have ⟨hdecomp, hodd⟩ := v2_decomp c hc
  let e := v2 c
  let c0 := c / 2 ^ e
  have hne : iter (grayCarryStep s c0) n 0 ≠ 0 := by
    have hT := grayCarryStep_tperm s c0 (by omega)
    have htow := grayCarry_ge2_tower s c0 hs hodd
    have ⟨_, hbit⟩ := tower_dvd_mod_testBit hT 0 1 (by omega) (by simp [Nat.mod_one])
      (fun m => by simpa using (htow m).2) n hn (Nat.one_dvd n)
    intro h0; rw [h0, Nat.zero_testBit] at hbit; cases hbit
  conv => lhs; rw [hdecomp]
  rw [v2_shift_homogeneous (grayCarryStep s (2 ^ e * c0)) (grayCarryStep s c0) e n
        (grayCarryStep_shift_hom s e c0) hne]
  rw [grayCarry_ge2_odd_v2 s c0 n hs hodd hn]

/-! ### Regime II: `s = 1` (Valuation-Shifted Coset-Holonomy Tower!) -/

theorem grayCoset_lift (r m j : Nat) :
    grayCoset r (j + 2 * 2 ^ m) = grayCoset r j + 2 ^ (r + 1 + m) := by
  simp only [grayCoset]
  have hmod : (j + 2 * 2 ^ m) % 2 = j % 2 := by omega
  have hdiv : (j + 2 * 2 ^ m) / 2 = j / 2 + 2 ^ m := by omega
  rw [hmod, hdiv, Nat.mul_add, ← Nat.pow_add]
  omega

theorem grayPhi1_on_2r_sub_1 (r : Nat) (hr : 1 ≤ r) :
    grayPhi 1 (2 ^ r - 1) % 2 ^ (r + 1) = 2 ^ r + 1 := by
  have h2r_lt : 2 ^ r + 1 < 2 ^ (r + 1) := by
    have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [Nat.pow_succ]; omega
    have hge : 2 ≤ 2 ^ r := by
      have := Nat.pow_le_pow_right (by omega : 0 < 2) hr; simpa using this
    omega
  rw [← Nat.mod_eq_of_lt h2r_lt]
  apply mod_pow2_of_testBit_eq _ _ (r + 1)
  intro i hi
  have hpow : 0 < 2 ^ r := pow2_pos r
  have hbit_m1 : ∀ j, (2 ^ r - 1).testBit j = decide (j < r) := by
    intro j
    rw [testBit_eq_div_mod]
    by_cases hj : j < r
    · simp only [hj, decide_true]
      have hdiv : (2 ^ r - 1) / 2 ^ j = 2 ^ (r - j) - 1 := by
        have hp : 2 ^ r = 2 ^ j * 2 ^ (r - j) := by rw [← Nat.pow_add]; congr 1; omega
        have hpos1 : 0 < 2 ^ (r - j) := pow2_pos _
        have hpos2 : 0 < 2 ^ j := pow2_pos j
        have heq : 2 ^ r - 1 = 2 ^ j * (2 ^ (r - j) - 1) + (2 ^ j - 1) := by
          rw [hp, Nat.mul_sub_left_distrib, Nat.mul_one]
          have : 2 ^ j ≤ 2 ^ j * 2 ^ (r - j) := Nat.le_mul_of_pos_right _ hpos1
          omega
        rw [heq, Nat.mul_add_div hpos2, Nat.div_eq_of_lt (by omega), Nat.add_zero]
      rw [hdiv]
      have heven : 2 ^ (r - j) % 2 = 0 := by
        have : r - j = (r - j - 1) + 1 := by omega
        rw [this, Nat.pow_succ]; omega
      have hpos : 0 < 2 ^ (r - j) := pow2_pos _
      have hodd : (2 ^ (r - j) - 1) % 2 = 1 := by omega
      rw [hodd]; rfl
    · simp only [hj, decide_false]
      have hle : 2 ^ r ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.div_eq_of_lt (by omega)]; rfl
  have hbit_p1 : ∀ j < r + 1, (2 ^ r + 1).testBit j = (decide (j = 0) || decide (j = r)) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp only [decide_true, Bool.true_or, testBit_eq_div_mod, Nat.pow_zero, Nat.div_one]
      have hev : 2 ^ r % 2 = 0 := by
        have : r = (r - 1) + 1 := by omega
        rw [this, Nat.pow_succ]; omega
      have : (2 ^ r + 1) % 2 = 1 := by omega
      rw [this]; rfl
    · by_cases hjr : j = r
      · subst hjr
        simp only [decide_true, Bool.or_true, testBit_eq_div_mod]
        have hdiv : (2 ^ j + 1) / 2 ^ j = 1 := by
          have : 2 ^ j + 1 = 2 ^ j * 1 + 1 := by omega
          rw [this, Nat.mul_add_div (pow2_pos j), Nat.div_eq_of_lt (by
            have : 2 ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hr
            omega)]
        rw [hdiv]; rfl
      · have hjlt : j < r := by omega
        have hne0 : decide (j = 0) = false := by simp; omega
        have hner : decide (j = r) = false := by simp; omega
        rw [hne0, hner, Bool.false_or, testBit_eq_div_mod]
        have hp : 2 ^ r = 2 ^ j * 2 ^ (r - j) := by rw [← Nat.pow_add]; congr 1; omega
        have h1lt : 1 < 2 ^ j := by
          have : 2 ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hjpos
          omega
        rw [hp, Nat.mul_add_div (pow2_pos j), Nat.div_eq_of_lt h1lt, Nat.add_zero]
        have hev : 2 ^ (r - j) % 2 = 0 := by
          have : r - j = (r - j - 1) + 1 := by omega
          rw [this, Nat.pow_succ]; omega
        rw [hev]; rfl
  rw [grayPhi, Nat.testBit_xor, testBit_pow2_mul, hbit_m1 i, hbit_p1 i hi]
  by_cases hi1 : 1 ≤ i
  · simp only [hi1, ↓reduceIte, hbit_m1 (i - 1)]
    by_cases hir : i = r
    · subst hir
      have h2 : decide (i - 1 < i) = true := by simp; omega
      simp [h2]
    · have hilt : i < r := by omega
      have h1 : decide (i < r) = true := by simp [hilt]
      have h2 : decide (i - 1 < r) = true := by simp; omega
      have h3 : decide (i = 0) = false := by simp; omega
      have h4 : decide (i = r) = false := by simp [hir]
      simp [h1, h2, h3, h4]
  · have hi0 : i = 0 := by omega
    subst hi0
    have h1 : decide (0 < r) = true := by simp; omega
    simp [h1]

/-- Exact base-step valuation for `s = 1` Gray-carry: for ANY odd `c`, letting `r = v2 (c + 1)`,
    `iter (grayCarryStep 1 c) 2 0` is divisible by `2^(r+1)` AND has bit `r+1` equal to `true`! -/
theorem grayCarry1_base_step (c : Nat) (hc : c % 2 = 1) :
    let r := v2 (c + 1)
    1 ≤ r ∧
    c % 2 ^ (r + 1) = 2 ^ r - 1 ∧
    iter (grayCarryStep 1 c) 2 0 % 2 ^ (r + 1) = 0 ∧
    (iter (grayCarryStep 1 c) 2 0).testBit (r + 1) = true := by
  dsimp only
  have hcp1_ne : c + 1 ≠ 0 := by omega
  have hr_ge1 : 1 ≤ v2 (c + 1) := by
    have hev : (c + 1) % 2 = 0 := by omega
    have hv : v2 (c + 1) = 1 + v2 ((c + 1) / 2) := by
      conv => lhs; unfold v2
      simp [hev]
    omega
  have ⟨hdecomp, hqodd⟩ := v2_decomp (c + 1) hcp1_ne
  have hq_eq : (c + 1) / 2 ^ v2 (c + 1) = 2 * (((c + 1) / 2 ^ v2 (c + 1)) / 2) + 1 := by omega
  have hc_eq : c = 2 ^ (v2 (c + 1) + 1) * (((c + 1) / 2 ^ v2 (c + 1)) / 2) + (2 ^ v2 (c + 1) - 1) := by
    have hpow : 2 ^ (v2 (c + 1) + 1) = 2 ^ v2 (c + 1) * 2 := Nat.pow_succ 2 (v2 (c + 1))
    have h1 : c + 1 = 2 ^ (v2 (c + 1) + 1) * (((c + 1) / 2 ^ v2 (c + 1)) / 2) + 2 ^ v2 (c + 1) := by
      calc c + 1 = 2 ^ v2 (c + 1) * ((c + 1) / 2 ^ v2 (c + 1)) := hdecomp
        _ = 2 ^ v2 (c + 1) * (2 * (((c + 1) / 2 ^ v2 (c + 1)) / 2) + 1) := congrArg (2 ^ v2 (c + 1) * ·) hq_eq
        _ = 2 ^ v2 (c + 1) * (2 * (((c + 1) / 2 ^ v2 (c + 1)) / 2)) + 2 ^ v2 (c + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = 2 ^ (v2 (c + 1) + 1) * (((c + 1) / 2 ^ v2 (c + 1)) / 2) + 2 ^ v2 (c + 1) := by
          rw [hpow, Nat.mul_assoc]
    have hpos : 0 < 2 ^ v2 (c + 1) := pow2_pos _
    omega
  have hc_mod : c % 2 ^ (v2 (c + 1) + 1) = 2 ^ v2 (c + 1) - 1 := by
    have hpow : 2 ^ (v2 (c + 1) + 1) = 2 ^ v2 (c + 1) + 2 ^ v2 (c + 1) := by rw [Nat.pow_succ]; omega
    have hlt : 2 ^ v2 (c + 1) - 1 < 2 ^ (v2 (c + 1) + 1) := by have := pow2_pos (v2 (c + 1)); omega
    conv => lhs; arg 1; rw [hc_eq]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  have hphi_mod : grayPhi 1 c % 2 ^ (v2 (c + 1) + 1) = 2 ^ v2 (c + 1) + 1 := by
    rw [← (grayPhi_tperm 1 (by omega)).compat_mod (v2 (c + 1) + 1) c, hc_mod]
    exact grayPhi1_on_2r_sub_1 (v2 (c + 1)) hr_ge1
  have hiter2 : iter (grayCarryStep 1 c) 2 0 = grayPhi 1 c + c := by
    simp [iter, grayCarryStep, grayPhi_zero]
  have hmod2 : (grayPhi 1 c + c) % 2 ^ (v2 (c + 1) + 1) = 0 := by
    rw [Nat.add_mod, hphi_mod, hc_mod]
    have hpow : 2 ^ (v2 (c + 1) + 1) = 2 ^ v2 (c + 1) + 2 ^ v2 (c + 1) := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ v2 (c + 1) := pow2_pos _
    have hsum : (2 ^ v2 (c + 1) + 1) + (2 ^ v2 (c + 1) - 1) = 2 ^ (v2 (c + 1) + 1) := by omega
    rw [hsum, Nat.mod_self]
  have hc_bit_r : c.testBit (v2 (c + 1)) = false := by
    rw [← testBit_mod_pow2_of_lt c (v2 (c + 1) + 1) (v2 (c + 1)) (by omega), hc_mod, testBit_eq_div_mod]
    have hpos : 0 < 2 ^ v2 (c + 1) := pow2_pos _
    rw [Nat.div_eq_of_lt (by omega)]; rfl
  have hphi_bit : (grayPhi 1 c).testBit (v2 (c + 1) + 1) = c.testBit (v2 (c + 1) + 1) := by
    simp only [grayPhi, Nat.testBit_xor, testBit_pow2_mul]
    have hge : 1 ≤ v2 (c + 1) + 1 := by omega
    have hsub : v2 (c + 1) + 1 - 1 = v2 (c + 1) := by omega
    simp [hge, hsub, hc_bit_r]
  have hbit2 : (grayPhi 1 c + c).testBit (v2 (c + 1) + 1) = true := by
    rw [testBit_add_eq, hphi_bit, hphi_mod, hc_mod]
    have hpow : 2 ^ (v2 (c + 1) + 1) = 2 ^ v2 (c + 1) + 2 ^ v2 (c + 1) := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ v2 (c + 1) := pow2_pos _
    have hge : (2 ^ v2 (c + 1) + 1) + (2 ^ v2 (c + 1) - 1) ≥ 2 ^ (v2 (c + 1) + 1) := by omega
    simp only [hge, decide_true]
    cases c.testBit (v2 (c + 1) + 1) <;> rfl
  exact ⟨hr_ge1, hc_mod, by rw [hiter2]; exact hmod2, by rw [hiter2]; exact hbit2⟩

theorem grayPhi_beta_eq1 (k y : Nat) (hy : y < 2 ^ k) :
    xor ((grayPhi 1 y).testBit (k + 1)) ((grayPhi 1 (y + 2 ^ k)).testBit (k + 1)) = true := by
  simp only [grayPhi, Nat.testBit_xor, testBit_pow2_mul]
  have ⟨h1, h2⟩ := testBit_add_pow2_of_lt_bound y k hy
  have hge : 1 ≤ k + 1 := by omega
  have hsub : k + 1 - 1 = k := by omega
  simp only [hge, ↓reduceIte, hsub, h1, h2, testBit_add_pow2_self]
  cases y.testBit k <;> rfl

/-- Bijection between `grayCoset r` and `grayImgCoset r` induced by `grayPhi 1` modulo `2^(r + 1 + m)`. -/
theorem xorRange_grayPhi1_coset (r m : Nat) (hr : 1 ≤ r) (g : Nat → Bool) :
    xorRange (2 * 2 ^ m) (fun j => g (grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m))) =
      xorRange (2 * 2 ^ m) (fun j => g (grayImgCoset r j)) := by
  have hΦ := grayPhi_tperm 1 (by omega)
  have hN_eq : 2 ^ (r + 1 + m) = 2 ^ (r + 1) * 2 ^ m := Nat.pow_add 2 (r + 1) m
  have hdvd : 2 ^ (r + 1) ∣ 2 ^ (r + 1 + m) := ⟨2 ^ m, hN_eq⟩
  have hM2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [Nat.pow_succ]; omega
  have h2r_ge2 : 2 ≤ 2 ^ r := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hr; simpa using this
  have h2r_sub_lt : 2 ^ r - 1 < 2 ^ (r + 1) := by omega
  have h2r_add_lt : 2 ^ r + 1 < 2 ^ (r + 1) := by omega
  let σ : Nat → Nat := fun j =>
    let z := grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m)
    2 * (z / 2 ^ (r + 1)) + (if z % 2 ^ (r + 1) == 0 then 0 else 1)
  let τ : Nat → Nat := fun j =>
    let x := tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j)
    2 * (x / 2 ^ (r + 1)) + (if x % 2 ^ (r + 1) == 0 then 0 else 1)
  have hcoset_lt : ∀ j < 2 * 2 ^ m, grayCoset r j < 2 ^ (r + 1 + m) := by
    intro j hj
    simp only [grayCoset]
    have hdiv : j / 2 < 2 ^ m := by omega
    have hmul : 2 ^ (r + 1) * (j / 2 + 1) ≤ 2 ^ (r + 1 + m) := by
      rw [hN_eq]; exact Nat.mul_le_mul_left _ hdiv
    rw [Nat.mul_add, Nat.mul_one] at hmul
    split <;> omega
  have himg_lt : ∀ j < 2 * 2 ^ m, grayImgCoset r j < 2 ^ (r + 1 + m) := by
    intro j hj
    simp only [grayImgCoset]
    have hdiv : j / 2 < 2 ^ m := by omega
    have hmul : 2 ^ (r + 1) * (j / 2 + 1) ≤ 2 ^ (r + 1 + m) := by
      rw [hN_eq]; exact Nat.mul_le_mul_left _ hdiv
    rw [Nat.mul_add, Nat.mul_one] at hmul
    split <;> omega
  have hcoset_modM : ∀ j, grayCoset r j % 2 ^ (r + 1) = (if j % 2 == 0 then 0 else 2 ^ r - 1) := by
    intro j
    simp only [grayCoset]
    rw [Nat.mul_add_mod]
    split
    · simp
    · exact Nat.mod_eq_of_lt h2r_sub_lt
  have himg_modM : ∀ j, grayImgCoset r j % 2 ^ (r + 1) = (if j % 2 == 0 then 0 else 2 ^ r + 1) := by
    intro j
    simp only [grayImgCoset]
    rw [Nat.mul_add_mod]
    split
    · simp
    · exact Nat.mod_eq_of_lt h2r_add_lt
  have himg_eq_sigma : ∀ j < 2 * 2 ^ m,
      grayImgCoset r (σ j) = grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m) := by
    intro j _
    have hz_modM : (grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m)) % 2 ^ (r + 1) =
        (if j % 2 == 0 then 0 else 2 ^ r + 1) := by
      rw [Nat.mod_mod_of_dvd _ hdvd, ← hΦ.compat_mod (r + 1), hcoset_modM]
      split
      · simp [grayPhi_zero]
      · exact grayPhi1_on_2r_sub_1 r hr
    have hdecomp := Nat.div_add_mod (grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m)) (2 ^ (r + 1))
    dsimp only [grayImgCoset, σ]
    cases hpar : (j % 2 == 0) with
    | true =>
      have hz0 : (grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m)) % 2 ^ (r + 1) = 0 := by
        simpa [hpar] using hz_modM
      rw [hz0]
      simp only [beq_self_eq_true, ↓reduceIte, Nat.add_zero]
      have h1 : 2 * (grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m) / 2 ^ (r + 1)) / 2 =
          grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m) / 2 ^ (r + 1) := by omega
      have h2 : (2 * (grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m) / 2 ^ (r + 1))) % 2 = 0 := by omega
      rw [h1, h2]
      simp only [beq_self_eq_true, ↓reduceIte, Nat.add_zero]
      omega
    | false =>
      have hz1 : (grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m)) % 2 ^ (r + 1) = 2 ^ r + 1 := by
        simpa [hpar] using hz_modM
      have hne0 : ((grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m)) % 2 ^ (r + 1) == 0) = false := by
        rw [hz1]; apply beq_false_of_ne; omega
      rw [hne0]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h1 : (2 * (grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m) / 2 ^ (r + 1)) + 1) / 2 =
          grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m) / 2 ^ (r + 1) := by omega
      have h2 : ((2 * (grayPhi 1 (grayCoset r j) % 2 ^ (r + 1 + m) / 2 ^ (r + 1)) + 1) % 2 == 0) = false := by
        apply beq_false_of_ne; omega
      rw [h1, h2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
  have hcoset_eq_tau : ∀ j < 2 * 2 ^ m,
      grayCoset r (τ j) = tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) := by
    intro j hj
    have hfx : grayPhi 1 (tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j)) % 2 ^ (r + 1 + m) =
        grayImgCoset r j := by
      rw [tpermInv_right_inv hΦ (r + 1 + m), Nat.mod_eq_of_lt (himg_lt j hj)]
    have hfxM : grayPhi 1 (tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j)) % 2 ^ (r + 1) =
        (if j % 2 == 0 then 0 else 2 ^ r + 1) := by
      have h1 : (grayPhi 1 (tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j)) % 2 ^ (r + 1 + m)) % 2 ^ (r + 1) =
          grayImgCoset r j % 2 ^ (r + 1) := by rw [hfx]
      rwa [Nat.mod_mod_of_dvd _ hdvd, himg_modM] at h1
    have hx_modM : tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) % 2 ^ (r + 1) =
        (if j % 2 == 0 then 0 else 2 ^ r - 1) := by
      have hlt : tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) % 2 ^ (r + 1) < 2 ^ (r + 1) :=
        Nat.mod_lt _ (pow2_pos (r + 1))
      have hinv := tpermInv_left_inv hΦ (r + 1) _ hlt
      rw [hΦ.compat_mod (r + 1), hfxM] at hinv
      cases hpar : (j % 2 == 0) with
      | true =>
        simp only [hpar, ↓reduceIte] at hinv ⊢
        have h0 := tpermInv_left_inv hΦ (r + 1) 0 (pow2_pos (r + 1))
        simp only [grayPhi_zero, Nat.zero_mod] at h0
        rw [← hinv, h0]
      | false =>
        simp only [hpar, Bool.false_eq_true, ↓reduceIte] at hinv ⊢
        have h1 := tpermInv_left_inv hΦ (r + 1) (2 ^ r - 1) h2r_sub_lt
        rw [grayPhi1_on_2r_sub_1 r hr] at h1
        rw [← hinv, h1]
    have hdecomp := Nat.div_add_mod (tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j)) (2 ^ (r + 1))
    dsimp only [grayCoset, τ]
    cases hpar : (j % 2 == 0) with
    | true =>
      have hx0 : tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) % 2 ^ (r + 1) = 0 := by
        simpa [hpar] using hx_modM
      rw [hx0]
      simp only [beq_self_eq_true, ↓reduceIte, Nat.add_zero]
      have h1 : 2 * (tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) / 2 ^ (r + 1)) / 2 =
          tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) / 2 ^ (r + 1) := by omega
      have h2 : (2 * (tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) / 2 ^ (r + 1))) % 2 = 0 := by omega
      rw [h1, h2]
      simp only [beq_self_eq_true, ↓reduceIte, Nat.add_zero]
      omega
    | false =>
      have hx1 : tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) % 2 ^ (r + 1) = 2 ^ r - 1 := by
        simpa [hpar] using hx_modM
      have hne0 : (tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) % 2 ^ (r + 1) == 0) = false := by
        rw [hx1]; apply beq_false_of_ne; omega
      rw [hne0]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h1 : (2 * (tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) / 2 ^ (r + 1)) + 1) / 2 =
          tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) / 2 ^ (r + 1) := by omega
      have h2 : ((2 * (tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) / 2 ^ (r + 1)) + 1) % 2 == 0) = false := by
        apply beq_false_of_ne; omega
      rw [h1, h2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
  have hσ_lt : ∀ i < 2 * 2 ^ m, σ i < 2 * 2 ^ m := by
    intro i _
    dsimp only [σ]
    have hlt : grayPhi 1 (grayCoset r i) % 2 ^ (r + 1 + m) < 2 ^ (r + 1 + m) := Nat.mod_lt _ (pow2_pos _)
    have hdiv_lt : grayPhi 1 (grayCoset r i) % 2 ^ (r + 1 + m) / 2 ^ (r + 1) < 2 ^ m := by
      have hle := Nat.mul_div_le (grayPhi 1 (grayCoset r i) % 2 ^ (r + 1 + m)) (2 ^ (r + 1))
      exact (Nat.mul_lt_mul_left (pow2_pos (r + 1))).mp (by rw [← hN_eq]; omega)
    split <;> omega
  have hτ_lt : ∀ j < 2 * 2 ^ m, τ j < 2 * 2 ^ m := by
    intro j _
    dsimp only [τ]
    have hlt := tpermInv_lt (grayPhi 1) (r + 1 + m) (grayImgCoset r j)
    have hdiv_lt : tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j) / 2 ^ (r + 1) < 2 ^ m := by
      have hle := Nat.mul_div_le (tpermInv (grayPhi 1) (r + 1 + m) (grayImgCoset r j)) (2 ^ (r + 1))
      exact (Nat.mul_lt_mul_left (pow2_pos (r + 1))).mp (by rw [← hN_eq]; omega)
    split <;> omega
  rw [xorRange_congr (2 * 2 ^ m) _ (fun j => g (grayImgCoset r (σ j)))
        (fun j hj => by rw [himg_eq_sigma j hj])]
  apply xorRange_bij (2 * 2 ^ m) σ τ (fun j => g (grayImgCoset r j)) hσ_lt hτ_lt
  · intro j hj
    have h1 : grayImgCoset r (σ (τ j)) = grayImgCoset r j := by
      rw [himg_eq_sigma (τ j) (hτ_lt j hj), hcoset_eq_tau j hj, tpermInv_right_inv hΦ (r + 1 + m),
          Nat.mod_eq_of_lt (himg_lt j hj)]
    have hdiv : grayImgCoset r (σ (τ j)) / 2 ^ (r + 1) = grayImgCoset r j / 2 ^ (r + 1) := by rw [h1]
    have hmod : grayImgCoset r (σ (τ j)) % 2 ^ (r + 1) = grayImgCoset r j % 2 ^ (r + 1) := by rw [h1]
    have hdiv_eval : ∀ a, grayImgCoset r a / 2 ^ (r + 1) = a / 2 := by
      intro a; simp only [grayImgCoset]; rw [Nat.mul_add_div (pow2_pos (r + 1))]
      split
      · simp
      · rw [Nat.div_eq_of_lt h2r_add_lt, Nat.add_zero]
    rw [hdiv_eval, hdiv_eval] at hdiv
    rw [himg_modM, himg_modM] at hmod
    cases hp1 : (σ (τ j) % 2 == 0) <;> cases hp2 : (j % 2 == 0) <;> simp_all <;> omega
  · intro i hi
    have h1 : grayCoset r (τ (σ i)) = grayCoset r i := by
      rw [hcoset_eq_tau (σ i) (hσ_lt i hi), himg_eq_sigma i hi,
          tpermInv_left_inv hΦ (r + 1 + m) _ (hcoset_lt i hi)]
    have hdiv : grayCoset r (τ (σ i)) / 2 ^ (r + 1) = grayCoset r i / 2 ^ (r + 1) := by rw [h1]
    have hmod : grayCoset r (τ (σ i)) % 2 ^ (r + 1) = grayCoset r i % 2 ^ (r + 1) := by rw [h1]
    have hdiv_eval : ∀ a, grayCoset r a / 2 ^ (r + 1) = a / 2 := by
      intro a; simp only [grayCoset]; rw [Nat.mul_add_div (pow2_pos (r + 1))]
      split
      · simp
      · rw [Nat.div_eq_of_lt h2r_sub_lt, Nat.add_zero]
    rw [hdiv_eval, hdiv_eval] at hdiv
    rw [hcoset_modM, hcoset_modM] at hmod
    cases hp1 : (τ (σ i) % 2 == 0) <;> cases hp2 : (i % 2 == 0) <;> simp_all <;> omega

/-- Exact coset carry-overflow parity for `s = 1` Gray-carry: pairs `2*t` and `2*t + 1` cancel
    everywhere except at the unique threshold `t = 2^m - 1 - q`, yielding `true`! -/
theorem xorRange_grayImgCoset_carry (r m c : Nat) (_hr : 1 ≤ r)
    (hc_mod : c % 2 ^ (r + 1) = 2 ^ r - 1) :
    xorRange (2 * 2 ^ m) (fun j =>
      decide (grayImgCoset r j + c % 2 ^ (r + 1 + m) ≥ 2 ^ (r + 1 + m))) = true := by
  have hN_eq : 2 ^ (r + 1 + m) = 2 ^ (r + 1) * 2 ^ m := Nat.pow_add 2 (r + 1) m
  have hdvd : 2 ^ (r + 1) ∣ 2 ^ (r + 1 + m) := ⟨2 ^ m, hN_eq⟩
  have hM2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [Nat.pow_succ]; omega
  have hpos_r : 0 < 2 ^ r := pow2_pos r
  have hc0_lt : c % 2 ^ (r + 1 + m) < 2 ^ (r + 1 + m) := Nat.mod_lt c (pow2_pos _)
  have hc0_modM : (c % 2 ^ (r + 1 + m)) % 2 ^ (r + 1) = 2 ^ r - 1 := by
    rw [Nat.mod_mod_of_dvd c hdvd, hc_mod]
  have hc0_eq : c % 2 ^ (r + 1 + m) =
      2 ^ (r + 1) * (c % 2 ^ (r + 1 + m) / 2 ^ (r + 1)) + (2 ^ r - 1) := by
    have := Nat.div_add_mod (c % 2 ^ (r + 1 + m)) (2 ^ (r + 1))
    rw [hc0_modM] at this; exact this.symm
  have hq_lt : c % 2 ^ (r + 1 + m) / 2 ^ (r + 1) < 2 ^ m := by
    have hle := Nat.mul_div_le (c % 2 ^ (r + 1 + m)) (2 ^ (r + 1))
    exact (Nat.mul_lt_mul_left (pow2_pos (r + 1))).mp (by rw [← hN_eq]; omega)
  rw [xorRange_two_mul_interleave (2 ^ m)]
  have hpair : ∀ t < 2 ^ m,
      xor (decide (grayImgCoset r (2 * t) + c % 2 ^ (r + 1 + m) ≥ 2 ^ (r + 1 + m)))
          (decide (grayImgCoset r (2 * t + 1) + c % 2 ^ (r + 1 + m) ≥ 2 ^ (r + 1 + m))) =
      (if t == 2 ^ m - 1 - (c % 2 ^ (r + 1 + m) / 2 ^ (r + 1)) then true else false) := by
    intro t ht
    have h2t : grayImgCoset r (2 * t) = 2 ^ (r + 1) * t := by
      simp only [grayImgCoset]
      have h1 : 2 * t / 2 = t := by omega
      have h2 : 2 * t % 2 = 0 := by omega
      simp [h1, h2]
    have h2t1 : grayImgCoset r (2 * t + 1) = 2 ^ (r + 1) * t + (2 ^ r + 1) := by
      simp only [grayImgCoset]
      have h1 : (2 * t + 1) / 2 = t := by omega
      simp [h1]
    rw [h2t, h2t1]
    conv => lhs; rw [hc0_eq]
    generalize c % 2 ^ (r + 1 + m) / 2 ^ (r + 1) = q at hq_lt ⊢
    rw [hN_eq]
    have hcond1 : (2 ^ (r + 1) * t + (2 ^ (r + 1) * q + (2 ^ r - 1)) ≥ 2 ^ (r + 1) * 2 ^ m) ↔
        (t + q ≥ 2 ^ m) := by
      have h1 : 2 ^ (r + 1) * t + (2 ^ (r + 1) * q + (2 ^ r - 1)) =
          2 ^ (r + 1) * (t + q) + (2 ^ r - 1) := by
        rw [Nat.mul_add]; omega
      rw [h1]
      constructor
      · intro hge
        rcases Nat.lt_or_ge (t + q) (2 ^ m) with hlt | hok
        · have hstep : 2 ^ (r + 1) * (t + q + 1) ≤ 2 ^ (r + 1) * 2 ^ m := Nat.mul_le_mul_left _ hlt
          rw [Nat.mul_add, Nat.mul_one] at hstep
          omega
        · exact hok
      · intro hge
        have : 2 ^ (r + 1) * 2 ^ m ≤ 2 ^ (r + 1) * (t + q) := Nat.mul_le_mul_left _ hge
        omega
    have hcond2 : (2 ^ (r + 1) * t + (2 ^ r + 1) + (2 ^ (r + 1) * q + (2 ^ r - 1)) ≥ 2 ^ (r + 1) * 2 ^ m) ↔
        (t + q + 1 ≥ 2 ^ m) := by
      have h2 : 2 ^ (r + 1) * t + (2 ^ r + 1) + (2 ^ (r + 1) * q + (2 ^ r - 1)) =
          2 ^ (r + 1) * (t + q + 1) := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
      rw [h2]
      exact ⟨fun h => Nat.le_of_mul_le_mul_left h (pow2_pos (r + 1)),
             fun h => Nat.mul_le_mul_left _ h⟩
    have hd1 : decide (2 ^ (r + 1) * t + (2 ^ (r + 1) * q + (2 ^ r - 1)) ≥ 2 ^ (r + 1) * 2 ^ m) =
        decide (t + q ≥ 2 ^ m) := by
      by_cases h : t + q ≥ 2 ^ m
      · simp [h, hcond1.mpr h]
      · have hn : ¬ (2 ^ (r + 1) * t + (2 ^ (r + 1) * q + (2 ^ r - 1)) ≥ 2 ^ (r + 1) * 2 ^ m) :=
          fun hc => h (hcond1.mp hc)
        simp [h, hn]
    have hd2 : decide (2 ^ (r + 1) * t + (2 ^ r + 1) + (2 ^ (r + 1) * q + (2 ^ r - 1)) ≥ 2 ^ (r + 1) * 2 ^ m) =
        decide (t + q + 1 ≥ 2 ^ m) := by
      by_cases h : t + q + 1 ≥ 2 ^ m
      · simp [h, hcond2.mpr h]
      · have hn : ¬ (2 ^ (r + 1) * t + (2 ^ r + 1) + (2 ^ (r + 1) * q + (2 ^ r - 1)) ≥ 2 ^ (r + 1) * 2 ^ m) :=
          fun hc => h (hcond2.mp hc)
        simp [h, hn]
    rw [hd1, hd2]
    by_cases h1 : t + q ≥ 2 ^ m
    · have h2 : t + q + 1 ≥ 2 ^ m := by omega
      have hne : (t == 2 ^ m - 1 - q) = false := beq_false_of_ne (by omega)
      simp [h1, h2, hne]
    · by_cases h2 : t + q + 1 ≥ 2 ^ m
      · have heq : t = 2 ^ m - 1 - q := by omega
        have h1d : decide (t + q ≥ 2 ^ m) = false := decide_eq_false h1
        have h2d : decide (t + q + 1 ≥ 2 ^ m) = true := decide_eq_true h2
        rw [h1d, h2d, heq]
        simp
      · have hne : (t == 2 ^ m - 1 - q) = false := beq_false_of_ne (by omega)
        simp [h1, h2, hne]
  rw [xorRange_congr (2 ^ m) _ _ hpair]
  have hlt_idx : 2 ^ m - 1 - (c % 2 ^ (r + 1 + m) / 2 ^ (r + 1)) < 2 ^ m :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (pow2_pos m) (by omega))
  exact xorRange_ite_eq (2 ^ m) (2 ^ m - 1 - (c % 2 ^ (r + 1 + m) / 2 ^ (r + 1))) hlt_idx (fun _ => true)

/-- Certified infinite coset-holonomy tower for `s = 1` Gray-carry and ANY odd `c`! -/
theorem grayCarry1_coset_tower (c : Nat) (hc : c % 2 = 1) :
    ∀ m, OrbitBijection (grayCarryStep 1 c) (v2 (c + 1) + 1 + m) 0 (2 * 2 ^ m) (grayCoset (v2 (c + 1))) ∧
         holonomy (grayCarryStep 1 c) (v2 (c + 1) + 1 + m) 0 (2 * 2 ^ m) = true := by
  have ⟨hr_ge1, hc_mod, hbase_mod, hbase_bit⟩ := grayCarry1_base_step c hc
  have hΦ := grayPhi_tperm 1 (by omega)
  have hT := grayCarryStep_tperm 1 c (by omega)
  intro m
  induction m with
  | zero =>
    have hhol0 : holonomy (grayCarryStep 1 c) (v2 (c + 1) + 1) 0 2 = true := by
      have hb := iter_testBit_eq_holonomy hT (v2 (c + 1) + 1) 0 2
      rw [hbase_bit, Nat.zero_testBit, Bool.false_xor] at hb
      exact hb.symm
    have h2r_lt : 2 ^ v2 (c + 1) - 1 < 2 ^ (v2 (c + 1) + 1) := by
      have : 2 ^ (v2 (c + 1) + 1) = 2 ^ v2 (c + 1) + 2 ^ v2 (c + 1) := by rw [Nat.pow_succ]; omega
      have := pow2_pos (v2 (c + 1)); omega
    simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
    refine ⟨⟨by simpa using hbase_mod, ?_,
      ⟨id, id, fun _ h => h, fun _ h => h, fun _ _ => rfl, fun _ _ => rfl, fun i hi => ?_⟩⟩, hhol0⟩
    · intro j hj
      match j with
      | 0 => simp [grayCoset]; exact pow2_pos _
      | 1 => simp [grayCoset]; exact h2r_lt
    · match i with
      | 0 => simp [iter, grayCoset]
      | 1 => simp [iter, grayCarryStep, grayPhi_zero, grayCoset, hc_mod]
  | succ m ih =>
    obtain ⟨hb_m, hhol_m⟩ := ih
    have hmul : 2 * 2 ^ (m + 1) = 2 * (2 * 2 ^ m) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, ← Nat.mul_assoc, Nat.mul_comm 2 2, Nat.mul_assoc]
    have hadd : v2 (c + 1) + 1 + (m + 1) = (v2 (c + 1) + 1 + m) + 1 := by omega
    have hb_next : OrbitBijection (grayCarryStep 1 c) (v2 (c + 1) + 1 + (m + 1)) 0 (2 * 2 ^ (m + 1))
        (grayCoset (v2 (c + 1))) := by
      rw [hadd, hmul]
      exact hb_m.lift hT hhol_m (fun j _ => grayCoset_lift (v2 (c + 1)) m j)
    refine ⟨hb_next, ?_⟩
    rw [hadd, hmul]
    have heven : (2 * 2 ^ m) % 2 = 0 := by omega
    change holonomy (fun x => grayPhi 1 x + c) (v2 (c + 1) + 1 + m + 1) 0 (2 * (2 * 2 ^ m)) = true
    rw [majority_carry_holonomy hΦ c (v2 (c + 1) + 1 + m) 0 (2 * 2 ^ m) hb_m.cyc hhol_m heven]
    have hbeta : xorRange (2 * 2 ^ m) (fun i =>
        let y := iter (fun x => grayPhi 1 x + c) i 0 % 2 ^ (v2 (c + 1) + 1 + m)
        xor ((grayPhi 1 y).testBit (v2 (c + 1) + 1 + m + 1))
            ((grayPhi 1 (y + 2 ^ (v2 (c + 1) + 1 + m))).testBit (v2 (c + 1) + 1 + m + 1))) = false := by
      rw [xorRange_congr (2 * 2 ^ m) _ (fun _ => true)
            (fun i _ => grayPhi_beta_eq1 (v2 (c + 1) + 1 + m) _ (Nat.mod_lt _ (pow2_pos _))),
          xorRange_const]
      have hne : ((2 * 2 ^ m) % 2 == 1) = false := by rw [heven]; rfl
      simp
    rw [hbeta, Bool.false_xor]
    change xorRange (2 * 2 ^ m) (fun i =>
      decide (grayPhi 1 (iter (grayCarryStep 1 c) i 0 % 2 ^ (v2 (c + 1) + 1 + m)) %
        2 ^ (v2 (c + 1) + 1 + m) + c % 2 ^ (v2 (c + 1) + 1 + m) ≥
        2 ^ (v2 (c + 1) + 1 + m))) = true
    rw [hb_m.xorRange_orbit_eq (fun y =>
          decide (grayPhi 1 y % 2 ^ (v2 (c + 1) + 1 + m) + c % 2 ^ (v2 (c + 1) + 1 + m) ≥
            2 ^ (v2 (c + 1) + 1 + m)))]
    rw [xorRange_grayPhi1_coset (v2 (c + 1)) m hr_ge1
          (fun z => decide (z + c % 2 ^ (v2 (c + 1) + 1 + m) ≥ 2 ^ (v2 (c + 1) + 1 + m)))]
    exact xorRange_grayImgCoset_carry (v2 (c + 1)) m c hr_ge1 hc_mod

/-- **Theorem 1B (Gray-Carry Valuation & Periodicity for `s = 1`, odd `c`)**:
    For ALL odd `c` (with `r = v2 (c + 1)`):
    1. Exact minimal period mod `2 ^ (r + 1 + m)` is `2 * 2 ^ m` for ALL `m : Nat`.
    2. For ALL `n ≥ 1`: `v2 (iter (grayCarryStep 1 c) n 0) = if n % 2 = 1 then 0 else v2 n + r`! -/
theorem grayCarry1_odd_period (c m : Nat) (hc : c % 2 = 1) :
    iter (grayCarryStep 1 c) (2 * 2 ^ m) 0 % 2 ^ (v2 (c + 1) + 1 + m) = 0 ∧
    ∀ d, 0 < d → d < 2 * 2 ^ m → iter (grayCarryStep 1 c) d 0 % 2 ^ (v2 (c + 1) + 1 + m) ≠ 0 := by
  have ⟨hr_ge1, hc_mod, hbase_mod, _⟩ := grayCarry1_base_step c hc
  have hT := grayCarryStep_tperm 1 c (by omega)
  have htow := grayCarry1_coset_tower c hc
  have hmin0 : ∀ j, 0 < j → j < 2 → iter (grayCarryStep 1 c) j 0 % 2 ^ (v2 (c + 1) + 1) ≠ 0 := by
    intro j hj1 hj2
    have hj : j = 1 := by omega
    subst hj
    simp only [iter, grayCarryStep, grayPhi_zero, Nat.zero_add]
    rw [hc_mod]
    have hge : 2 ≤ 2 ^ v2 (c + 1) := by
      have := Nat.pow_le_pow_right (by omega : 0 < 2) hr_ge1; simpa using this
    omega
  exact tower_to_min_period hT (v2 (c + 1) + 1) 2 (by omega) hbase_mod hmin0 (fun k => (htow k).2) m

theorem grayCarry1_odd_v2 (c n : Nat) (hc : c % 2 = 1) (hn : n ≠ 0) :
    v2 (iter (grayCarryStep 1 c) n 0) =
      if n % 2 = 1 then 0 else v2 n + v2 (c + 1) := by
  have ⟨hr_ge1, hc_mod, hbase_mod, _⟩ := grayCarry1_base_step c hc
  have hT := grayCarryStep_tperm 1 c (by omega)
  have htow := grayCarry1_coset_tower c hc
  by_cases hodd : n % 2 = 1
  · simp only [hodd, ↓reduceIte]
    have hrem : iter (grayCarryStep 1 c) (n % 2) 0 % 2 ^ (v2 (c + 1) + 1) ≠ 0 := by
      rw [hodd]
      simp only [iter, grayCarryStep, grayPhi_zero, Nat.zero_add]
      rw [hc_mod]
      have hge : 2 ≤ 2 ^ v2 (c + 1) := by
        have := Nat.pow_le_pow_right (by omega : 0 < 2) hr_ge1; simpa using this
      omega
    rw [tower_to_valuation_ndvd hT (v2 (c + 1) + 1) 2 hbase_mod n hrem, hodd]
    simp only [iter, grayCarryStep, grayPhi_zero, Nat.zero_add]
    exact v2_of_odd c hc
  · simp only [hodd, ↓reduceIte]
    have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
    rw [tower_to_valuation_dvd hT (v2 (c + 1) + 1) 2 (by omega) hbase_mod (fun m => (htow m).2) n hn hdvd]
    have hv : v2 n = 1 + v2 (n / 2) := by
      conv => lhs; unfold v2
      simp [hn, show n % 2 = 0 by omega]
    omega

/-- **Theorem 1B (Full General Form, `s = 1`, ALL `c ≥ 1`, ALL `n ≥ 1`)**:
    `v2 (iter (grayCarryStep 1 c) n 0) = if n % 2 = 1 then v2 c else v2 n + v2 c + v2 (c / 2^(v2 c) + 1)`! -/
theorem grayCarry1_v2 (c n : Nat) (hc : c ≠ 0) (hn : n ≠ 0) :
    v2 (iter (grayCarryStep 1 c) n 0) =
      if n % 2 = 1 then v2 c else v2 n + v2 c + v2 (c / 2 ^ v2 c + 1) := by
  have ⟨hdecomp, hodd⟩ := v2_decomp c hc
  let e := v2 c
  let c0 := c / 2 ^ e
  have hne : iter (grayCarryStep 1 c0) n 0 ≠ 0 := by
    have ⟨hr_ge1, hc_mod, hbase_mod, _⟩ := grayCarry1_base_step c0 hodd
    have hT := grayCarryStep_tperm 1 c0 (by omega)
    have htow := grayCarry1_coset_tower c0 hodd
    by_cases hno : n % 2 = 1
    · intro h0
      have hdiv : n = 2 * (n / 2) + 1 := by omega
      have hmod := hT.iter_mod_periodic (v2 (c0 + 1) + 1) 0 2 (by simpa using hbase_mod) (n / 2) 1
      rw [← hdiv, h0, Nat.zero_mod] at hmod
      simp only [iter, grayCarryStep, grayPhi_zero, Nat.zero_add, hc_mod] at hmod
      have hge : 2 ≤ 2 ^ v2 (c0 + 1) := by
        have := Nat.pow_le_pow_right (by omega : 0 < 2) hr_ge1; simpa using this
      omega
    · have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
      have ⟨_, hbit⟩ := tower_dvd_mod_testBit hT (v2 (c0 + 1) + 1) 2 (by omega) hbase_mod
        (fun m => (htow m).2) n hn hdvd
      intro h0; rw [h0, Nat.zero_testBit] at hbit; cases hbit
  conv => lhs; rw [hdecomp]
  rw [v2_shift_homogeneous (grayCarryStep 1 (2 ^ e * c0)) (grayCarryStep 1 c0) e n
        (grayCarryStep_shift_hom 1 e c0) hne]
  rw [grayCarry1_odd_v2 c0 n hodd hn]
  by_cases hno : n % 2 = 1
  · simp [hno, e]
  · simp [hno, e, c0]; omega

/-! ## Section 8: Theorem 2 — Nonlinear Quadratic Bitwise-AND Carry Ergodicity -/

theorem quadAndPhi_zero (s t : Nat) : quadAndPhi s t 0 = 0 := by simp [quadAndPhi]

theorem quadAndPhi_tperm (s t : Nat) (hs : 1 ≤ s) (ht : 1 ≤ t) : TPerm (quadAndPhi s t) where
  compat k x y hxy := by
    apply mod_pow2_of_testBit_eq
    intro i hi
    simp only [quadAndPhi, Nat.testBit_xor, Nat.testBit_and, testBit_pow2_mul]
    have hxi : x.testBit i = y.testBit i := by
      rw [← testBit_mod_pow2_of_lt x k i hi, hxy, testBit_mod_pow2_of_lt y k i hi]
    rw [hxi]
    by_cases hsi : s ≤ i
    · have h1 : x.testBit (i - s) = y.testBit (i - s) := by
        rw [← testBit_mod_pow2_of_lt x k (i - s) (by omega), hxy,
            testBit_mod_pow2_of_lt y k (i - s) (by omega)]
      by_cases hti : t ≤ i
      · have h2 : x.testBit (i - t) = y.testBit (i - t) := by
          rw [← testBit_mod_pow2_of_lt x k (i - t) (by omega), hxy,
              testBit_mod_pow2_of_lt y k (i - t) (by omega)]
        simp [hsi, hti, h1, h2]
      · simp [hsi, hti]
    · simp [hsi]
  fiber_flip k x := by
    simp only [quadAndPhi, Nat.testBit_xor, Nat.testBit_and, testBit_pow2_mul, testBit_add_pow2_self]
    by_cases hsk : s ≤ k
    · by_cases htk : t ≤ k
      · simp only [hsk, htk, ↓reduceIte,
          testBit_add_pow2_lt x k (k - s) (by omega),
          testBit_add_pow2_lt x k (k - t) (by omega)]
        cases x.testBit k <;> cases x.testBit (k - s) <;> cases x.testBit (k - t) <;> rfl
      · simp [hsk, htk]
    · simp [hsk]

theorem quadAndStep_tperm (s t c : Nat) (hs : 1 ≤ s) (ht : 1 ≤ t) : TPerm (quadAndStep s t c) :=
  (quadAndPhi_tperm s t hs ht).add_const c

theorem quadAndStep_shift_hom (s t e c0 x : Nat) :
    quadAndStep s t (2 ^ e * c0) (2 ^ e * x) = 2 ^ e * quadAndStep s t c0 x := by
  simp only [quadAndStep, quadAndPhi]
  have h1 : 2 ^ s * (2 ^ e * x) = 2 ^ e * (2 ^ s * x) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ s) (2 ^ e), Nat.mul_assoc]
  have h2 : 2 ^ t * (2 ^ e * x) = 2 ^ e * (2 ^ t * x) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ t) (2 ^ e), Nat.mul_assoc]
  rw [h1, h2, pow2_mul_and, pow2_mul_xor, Nat.mul_add]

/-- Pairing cancellation lemma: for any `b < m - 1`, `xorRange (2^m) (fun y => y.testBit b) = false`! -/
theorem xorRange_testBit_zero (m b : Nat) (hb : b + 1 < m) :
    xorRange (2 ^ m) (fun y => y.testBit b) = false := by
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have : m = (m - 1) + 1 := by omega
    conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
  rw [hpow, xorRange_two_mul]
  rw [xorRange_congr (2 ^ (m - 1)) _ (fun _ => false) (fun y _ => by
    rw [testBit_add_pow2_lt y (m - 1) b (by omega)]
    cases y.testBit b <;> rfl)]
  exact xorRange_false _

/-- Total quadratic twist derivative vanishes over `[0, 2^k)` whenever `1 ≤ s < t`, `t ≥ 3`, `k ≥ 1`! -/
theorem quadAndPhi_beta_sum_zero (s t k : Nat) (hs : 1 ≤ s) (hst : s < t) (ht : 3 ≤ t) (hk : 1 ≤ k) :
    xorRange (2 ^ k) (fun y =>
      xor ((quadAndPhi s t y).testBit (k + 1)) ((quadAndPhi s t (y + 2 ^ k)).testBit (k + 1))) = false := by
  by_cases hs2 : 2 ≤ s
  · -- When `s ≥ 2`, `β` is pointwise `false`!
    rw [xorRange_congr (2 ^ k) _ (fun _ => false) (fun y hy => by
      simp only [quadAndPhi, Nat.testBit_xor, Nat.testBit_and, testBit_pow2_mul]
      have ⟨h1, h2⟩ := testBit_add_pow2_of_lt_bound y k hy
      rw [h1, h2]
      by_cases hsk : s ≤ k + 1
      · by_cases htk : t ≤ k + 1
        · simp only [hsk, htk, ↓reduceIte,
            testBit_add_pow2_lt y k (k + 1 - s) (by omega),
            testBit_add_pow2_lt y k (k + 1 - t) (by omega)]
          cases y.testBit (k + 1 - s) <;> cases y.testBit (k + 1 - t) <;> rfl
        · simp [hsk, htk]
      · simp [hsk])]
    exact xorRange_false _
  · -- `s = 1`, `t ≥ 3`:
    have hs1 : s = 1 := by omega
    subst hs1
    by_cases htk : t ≤ k + 1
    · -- `β_{k+1}(y) = y.testBit (k + 1 - t)`, with `k + 1 - t + 1 < k` (since `t ≥ 3`)!
      rw [xorRange_congr (2 ^ k) _ (fun y => y.testBit (k + 1 - t)) (fun y hy => by
        simp only [quadAndPhi, Nat.testBit_xor, Nat.testBit_and, testBit_pow2_mul]
        have ⟨h1, h2⟩ := testBit_add_pow2_of_lt_bound y k hy
        have h1le : 1 ≤ k + 1 := by omega
        have hsub1 : k + 1 - 1 = k := by omega
        have hyk : y.testBit k = false := testBit_of_lt_pow2 y k k hy (Nat.le_refl k)
        simp only [h1, h2, h1le, htk, ↓reduceIte, hsub1, hyk, testBit_add_pow2_self,
          testBit_add_pow2_lt y k (k + 1 - t) (by omega)]
        cases y.testBit (k + 1 - t) <;> rfl)]
      exact xorRange_testBit_zero k (k + 1 - t) (by omega)
    · -- `k + 1 < t`: bit `k + 1` of `2^t * _` is `false`, so `β` is pointwise `false`!
      rw [xorRange_congr (2 ^ k) _ (fun _ => false) (fun y hy => by
        simp only [quadAndPhi, Nat.testBit_xor, Nat.testBit_and, testBit_pow2_mul]
        have ⟨h1, h2⟩ := testBit_add_pow2_of_lt_bound y k hy
        simp [h1, h2, htk])]
      exact xorRange_false _

/-- Certified infinite ergodic holonomy tower for nonlinear quadratic AND-carry (`t ≥ 3`, odd `c`). -/
theorem quadAnd_tower (s t c : Nat) (hs : 1 ≤ s) (hst : s < t) (ht : 3 ≤ t) (hc : c % 2 = 1) :
    ∀ k, OrbitBijection (quadAndStep s t c) k 0 (2 ^ k) id ∧
         holonomy (quadAndStep s t c) k 0 (2 ^ k) = true := by
  have hΦ := quadAndPhi_tperm s t hs (by omega)
  have hT := quadAndStep_tperm s t c hs (by omega)
  intro k
  induction k with
  | zero =>
    refine ⟨⟨by simp [Nat.mod_one], fun j hj => hj,
      ⟨id, id, fun _ h => h, fun _ h => h, fun _ _ => rfl, fun _ _ => rfl,
        fun i hi => by simp [Nat.mod_one]; omega⟩⟩, ?_⟩
    simp only [holonomy, Nat.pow_zero, xorRange, Nat.mod_one, quadAndStep, quadAndPhi_zero, Nat.zero_add]
    rw [testBit_eq_div_mod, Nat.pow_zero, Nat.div_one, hc]
    rfl
  | succ k ih =>
    obtain ⟨hb_k, hhol_k⟩ := ih
    have hb_next : OrbitBijection (quadAndStep s t c) (k + 1) 0 (2 ^ (k + 1)) id := by
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [h2]
      exact hb_k.lift hT hhol_k (fun j _ => rfl)
    refine ⟨hb_next, ?_⟩
    cases k with
    | zero =>
      simp only [holonomy, Nat.pow_one, xorRange, iter, Nat.zero_mod, quadAndStep, quadAndPhi_zero, Nat.zero_add]
      rw [hc]
      have hphi1 : quadAndPhi s t 1 = 1 := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [quadAndPhi, Nat.testBit_xor, Nat.testBit_and, testBit_pow2_mul]
        by_cases hsi : s ≤ i
        · by_cases hti : t ≤ i
          · simp only [hsi, hti, ↓reduceIte]
            have hne : i - s ≠ i - t := by omega
            cases hb1 : (1 : Nat).testBit (i - s) with
            | false => simp
            | true =>
              have his0 : i - s = 0 := by
                rcases Nat.eq_zero_or_pos (i - s) with h0 | hpos
                · exact h0
                · exfalso
                  rw [testBit_eq_div_mod] at hb1
                  have hge2 : 2 ≤ 2 ^ (i - s) := by
                    have := Nat.pow_le_pow_right (by omega : 0 < 2) hpos; simpa using this
                  rw [Nat.div_eq_of_lt (by omega)] at hb1; simp at hb1
              omega
          · simp [hsi, hti]
        · simp [hsi]
      rw [hphi1, testBit_eq_div_mod, testBit_eq_div_mod]
      have hc4 := Nat.mod_lt c (by omega : 0 < 4)
      have hdiv1 : (c / 2) % 2 = (c % 4) / 2 := by omega
      have hdiv2 : ((1 + c) / 2) % 2 = ((1 + c % 4) / 2) % 2 := by omega
      have hodd4 : (c % 4) % 2 = 1 := by omega
      rw [Nat.pow_one, hdiv1, hdiv2]
      generalize c % 4 = r at hc4 hodd4 ⊢
      match r with
      | 1 => rfl
      | 3 => rfl
    | succ k' =>
      have h2 : 2 ^ (k' + 1 + 1) = 2 * 2 ^ (k' + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [h2]
      have heven : 2 ^ (k' + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
      change holonomy (fun x => quadAndPhi s t x + c) (k' + 1 + 1) 0 (2 * 2 ^ (k' + 1)) = true
      rw [majority_carry_holonomy hΦ c (k' + 1) 0 (2 ^ (k' + 1)) hb_k.cyc hhol_k heven]
      change xor
        (xorRange (2 ^ (k' + 1)) (fun i =>
          xor ((quadAndPhi s t (iter (quadAndStep s t c) i 0 % 2 ^ (k' + 1))).testBit (k' + 1 + 1))
              ((quadAndPhi s t (iter (quadAndStep s t c) i 0 % 2 ^ (k' + 1) + 2 ^ (k' + 1))).testBit (k' + 1 + 1))))
        (xorRange (2 ^ (k' + 1)) (fun i =>
          decide (quadAndPhi s t (iter (quadAndStep s t c) i 0 % 2 ^ (k' + 1)) % 2 ^ (k' + 1) +
            c % 2 ^ (k' + 1) ≥ 2 ^ (k' + 1)))) = true
      rw [hb_k.xorRange_orbit_eq (fun y =>
            xor ((quadAndPhi s t y).testBit (k' + 1 + 1)) ((quadAndPhi s t (y + 2 ^ (k' + 1))).testBit (k' + 1 + 1))),
          hb_k.xorRange_orbit_eq (fun y =>
            decide (quadAndPhi s t y % 2 ^ (k' + 1) + c % 2 ^ (k' + 1) ≥ 2 ^ (k' + 1)))]
      simp only [id]
      rw [quadAndPhi_beta_sum_zero s t (k' + 1) hs hst ht (by omega), Bool.false_xor]
      rw [xorRange_tperm_bij hΦ (k' + 1) (fun z => decide (z + c % 2 ^ (k' + 1) ≥ 2 ^ (k' + 1)))]
      rw [xorRange_carry_full (2 ^ (k' + 1)) (c % 2 ^ (k' + 1)) (Nat.mod_lt c (pow2_pos _))]
      have hodd_mod : (c % 2 ^ (k' + 1)) % 2 = 1 := by
        have hdvd : 2 ∣ 2 ^ (k' + 1) := ⟨2 ^ k', by rw [Nat.pow_succ, Nat.mul_comm]⟩
        rw [Nat.mod_mod_of_dvd c hdvd, hc]
      rw [hodd_mod]; rfl

/-- **Theorem 2 (Nonlinear Quadratic Bitwise-AND Ergodicity & Exact `v2` Law)**:
    For ALL `1 ≤ s < t` with `t ≥ 3`, ALL `c ≥ 1`, and ALL `n ≥ 1`:
    1. If `c` is odd, exact minimal period mod `2^k` is `2^k` for ALL `k : Nat`.
    2. For ALL `c ≥ 1` and ALL `n ≥ 1`, `v2 (iter (quadAndStep s t c) n 0) = v2 c + v2 n`! -/
theorem quadAnd_odd_period (s t c k : Nat) (hs : 1 ≤ s) (hst : s < t) (ht : 3 ≤ t) (hc : c % 2 = 1) :
    iter (quadAndStep s t c) (2 ^ k) 0 % 2 ^ k = 0 ∧
    ∀ d, 0 < d → d < 2 ^ k → iter (quadAndStep s t c) d 0 % 2 ^ k ≠ 0 := by
  have hT := quadAndStep_tperm s t c hs (by omega)
  have htow := quadAnd_tower s t c hs hst ht hc
  have h := tower_to_min_period hT 0 1 (by omega) (by simp [Nat.mod_one])
    (fun r hr1 hr2 => by omega) (fun m => by simpa using (htow m).2) k
  simpa using h

theorem quadAnd_v2 (s t c n : Nat) (hs : 1 ≤ s) (hst : s < t) (ht : 3 ≤ t) (hc : c ≠ 0) (hn : n ≠ 0) :
    v2 (iter (quadAndStep s t c) n 0) = v2 c + v2 n := by
  have ⟨hdecomp, hodd⟩ := v2_decomp c hc
  let e := v2 c
  let c0 := c / 2 ^ e
  have hT := quadAndStep_tperm s t c0 hs (by omega)
  have htow := quadAnd_tower s t c0 hs hst ht hodd
  have hne : iter (quadAndStep s t c0) n 0 ≠ 0 := by
    have ⟨_, hbit⟩ := tower_dvd_mod_testBit hT 0 1 (by omega) (by simp [Nat.mod_one])
      (fun m => by simpa using (htow m).2) n hn (Nat.one_dvd n)
    intro h0; rw [h0, Nat.zero_testBit] at hbit; cases hbit
  have hodd_v2 : v2 (iter (quadAndStep s t c0) n 0) = v2 n := by
    have h := tower_to_valuation_dvd hT 0 1 (by omega) (by simp [Nat.mod_one])
      (fun m => by simpa using (htow m).2) n hn (Nat.one_dvd n)
    simpa using h
  conv => lhs; rw [hdecomp]
  rw [v2_shift_homogeneous (quadAndStep s t (2 ^ e * c0)) (quadAndStep s t c0) e n
        (quadAndStep_shift_hom s t e c0) hne, hodd_v2]

/-! ## Section 9: Theorem 3 — Complete Classification of Affine-XOR Recurrences -/

theorem affineXorStep_tperm (A c : Nat) (hA : A % 2 = 0) : TPerm (affineXorStep A c) where
  compat k x y hxy := by
    have hxor : (x ^^^ c) % 2 ^ k = (y ^^^ c) % 2 ^ k := by
      apply mod_pow2_of_testBit_eq
      intro i hi
      rw [Nat.testBit_xor, Nat.testBit_xor,
          ← testBit_mod_pow2_of_lt x k i hi, hxy, testBit_mod_pow2_of_lt y k i hi]
    simp only [affineXorStep]
    rw [Nat.add_mod, Nat.mul_mod, hxy, ← Nat.mul_mod, hxor, ← Nat.add_mod]
  fiber_flip k x := by
    simp only [affineXorStep]
    rw [testBit_add_eq, testBit_add_eq]
    have hAx_mod : (A * (x + 2 ^ k)) % 2 ^ k = (A * x) % 2 ^ k := by
      rw [Nat.mul_add, Nat.mul_comm A (2 ^ k), Nat.add_mul_mod_self_left]
    have hxor_mod : ((x + 2 ^ k) ^^^ c) % 2 ^ k = (x ^^^ c) % 2 ^ k := by
      apply mod_pow2_of_testBit_eq
      intro i hi
      rw [Nat.testBit_xor, Nat.testBit_xor, testBit_add_pow2_lt x k i hi]
    have hAx_bit : (A * (x + 2 ^ k)).testBit k = (A * x).testBit k := by
      -- Since `A` is even, `A * 2^k` is a multiple of `2^(k+1)`!
      have hA2 : A = 2 * (A / 2) := by omega
      have hpow : A * (x + 2 ^ k) = A * x + 2 ^ (k + 1) * (A / 2) := by
        rw [Nat.mul_add]
        have : A * 2 ^ k = 2 ^ (k + 1) * (A / 2) := by
          rw [Nat.pow_succ]; conv => lhs; rw [hA2]
          rw [Nat.mul_comm 2 (A / 2), Nat.mul_assoc, Nat.mul_comm (A / 2) (2 * 2 ^ k),
              Nat.mul_comm 2 (2 ^ k)]
        omega
      rw [← testBit_mod_pow2_of_lt (A * (x + 2 ^ k)) (k + 1) k (by omega),
          ← testBit_mod_pow2_of_lt (A * x) (k + 1) k (by omega),
          hpow, Nat.add_mul_mod_self_left]
    have hxor_bit : ((x + 2 ^ k) ^^^ c).testBit k = !((x ^^^ c).testBit k) := by
      rw [Nat.testBit_xor, Nat.testBit_xor, testBit_add_pow2_self]
      cases x.testBit k <;> cases c.testBit k <;> rfl
    rw [hAx_mod, hxor_mod, hAx_bit, hxor_bit]
    cases (A * x).testBit k <;> cases (x ^^^ c).testBit k <;>
      cases decide ((A * x) % 2 ^ k + (x ^^^ c) % 2 ^ k ≥ 2 ^ k) <;> rfl

theorem affineXorStep_shift_hom (A e c0 x : Nat) :
    affineXorStep A (2 ^ e * c0) (2 ^ e * x) = 2 ^ e * affineXorStep A c0 x := by
  simp only [affineXorStep]
  have h1 : A * (2 ^ e * x) = 2 ^ e * (A * x) := by
    rw [← Nat.mul_assoc, Nat.mul_comm A (2 ^ e), Nat.mul_assoc]
  rw [h1, pow2_mul_xor, Nat.mul_add]

/-- Constant odd doubled-fiber increment for `affineXorStep A c` on `[0, 2^k)` (feeds Sub-Engine 2!). -/
theorem affineXorStep_const_inc (A c k : Nat) :
    ∀ y < 2 ^ k,
      affineXorStep A c (y + 2 ^ k) % 2 ^ (k + 2) =
        (affineXorStep A c y + 2 ^ k * (A + if c.testBit k then 3 else 1)) % 2 ^ (k + 2) := by
  intro y hy
  simp only [affineXorStep]
  rw [Nat.add_mod, xor_add_pow2_of_lt y c k hy, ← Nat.add_mod]
  congr 1
  rw [Nat.mul_add, Nat.mul_add]
  have : A * 2 ^ k = 2 ^ k * A := Nat.mul_comm A (2 ^ k)
  omega

/-- Certified infinite holonomy tower for `affineXorStep A c` (even `A ≥ 2`, odd `c`)
    proved via Sub-Engine 2 (`holonomy_conservation_lift`)! -/
theorem affineXor_tower (A c : Nat) (hApos : A ≠ 0) (hAev : A % 2 = 0) (hc : c % 2 = 1) :
    ∀ m, iter (affineXorStep A c) (2 * 2 ^ m) 0 % 2 ^ (v2 A + m) = 0 ∧
         holonomy (affineXorStep A c) (v2 A + m) 0 (2 * 2 ^ m) = true := by
  have hT := affineXorStep_tperm A c hAev
  have hiter2 : iter (affineXorStep A c) 2 0 = A * c := by
    simp [iter, affineXorStep]
  have hvAc : v2 (A * c) = v2 A := by
    have ⟨hd, ho⟩ := v2_decomp A hApos
    have hprod : A * c = 2 ^ v2 A * ((A / 2 ^ v2 A) * c) := by
      conv => lhs; rw [hd]
      exact Nat.mul_assoc _ _ _
    have hodd_prod : ((A / 2 ^ v2 A) * c) % 2 = 1 := by
      rw [Nat.mul_mod, ho, hc]
    have hne_prod : (A / 2 ^ v2 A) * c ≠ 0 := by omega
    rw [hprod, v2_mul_pow2 (v2 A) _ hne_prod, v2_of_odd _ hodd_prod, Nat.add_zero]
  have hAc_ne : A * c ≠ 0 := Nat.mul_ne_zero hApos (by omega)
  have hbase_mod : iter (affineXorStep A c) 2 0 % 2 ^ v2 A = 0 := by
    rw [hiter2, ← hvAc]; exact v2_mod_zero (A * c) hAc_ne
  have hbase_bit : (iter (affineXorStep A c) 2 0).testBit (v2 A) = true := by
    rw [hiter2, ← hvAc]; exact v2_testBit_true (A * c) hAc_ne
  intro m
  induction m with
  | zero =>
    simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
    refine ⟨hbase_mod, ?_⟩
    have hb := iter_testBit_eq_holonomy hT (v2 A) 0 2
    rw [hbase_bit, Nat.zero_testBit, Bool.false_xor] at hb
    exact hb.symm
  | succ m ih =>
    obtain ⟨hcyc_m, hhol_m⟩ := ih
    have hmul : 2 * 2 ^ (m + 1) = 2 * (2 * 2 ^ m) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, ← Nat.mul_assoc, Nat.mul_comm 2 2, Nat.mul_assoc]
    have hadd : v2 A + (m + 1) = (v2 A + m) + 1 := by omega
    have ⟨_, hcyc_next⟩ := holonomy_double_cycle hT (v2 A + m) 0 (2 * 2 ^ m) (by simpa using hcyc_m) hhol_m
    refine ⟨by rw [hmul, hadd, hcyc_next]; simp, ?_⟩
    rw [hmul, hadd]
    let M := A + if c.testBit (v2 A + m) then 3 else 1
    have hModd : M % 2 = 1 := by
      dsimp only [M]; split <;> omega
    have hcons := holonomy_conservation_lift hT (v2 A + m) 0 (2 * 2 ^ m) M
      (by simpa using hcyc_m) hhol_m (by omega) hModd (affineXorStep_const_inc A c (v2 A + m))
    rw [hcons, hhol_m]

/-- **Theorem 3A (Affine-XOR Exact Minimal Periodicity for even `A ≥ 2`, odd `c`)**:
    For ALL even `A ≥ 2`, ALL odd `c`, and ALL `m : Nat`, the exact minimal period mod `2^(v2 A + m)`
    is `2 * 2^m` (in particular, 2-adically ergodic iff `v2 A = 1`, i.e., `A % 4 = 2`)! -/
theorem affineXor_even_odd_period (A c m : Nat) (hApos : A ≠ 0) (hAev : A % 2 = 0) (hc : c % 2 = 1) :
    iter (affineXorStep A c) (2 * 2 ^ m) 0 % 2 ^ (v2 A + m) = 0 ∧
    ∀ d, 0 < d → d < 2 * 2 ^ m → iter (affineXorStep A c) d 0 % 2 ^ (v2 A + m) ≠ 0 := by
  have hT := affineXorStep_tperm A c hAev
  have htow := affineXor_tower A c hApos hAev hc
  have hbase_mod : iter (affineXorStep A c) 2 0 % 2 ^ v2 A = 0 := by simpa using (htow 0).1
  have hvA_ge1 : 1 ≤ v2 A := by
    have hv : v2 A = 1 + v2 (A / 2) := by
      conv => lhs; unfold v2
      simp [hApos, hAev]
    omega
  have hmin0 : ∀ r, 0 < r → r < 2 → iter (affineXorStep A c) r 0 % 2 ^ v2 A ≠ 0 := by
    intro r hr1 hr2
    have hr : r = 1 := by omega
    subst hr
    simp only [iter, affineXorStep, Nat.mul_zero, Nat.zero_add, Nat.zero_xor]
    intro h0
    have hdvd : 2 ∣ 2 ^ v2 A := Nat.pow_dvd_pow 2 hvA_ge1
    have h1 := Nat.mod_mod_of_dvd c hdvd
    rw [h0, Nat.zero_mod] at h1
    omega
  exact tower_to_min_period hT (v2 A) 2 (by omega) hbase_mod hmin0 (fun k => (htow k).2) m

/-- **Theorem 3B (Affine-XOR Exact Valuation Law for ALL even `A ≥ 2`, ALL `c ≥ 1`, ALL `n ≥ 1`)**:
    `v2 (iter (affineXorStep A c) n 0) = if n % 2 = 1 then v2 c else v2 n + v2 c + v2 A - 1`! -/
theorem affineXor_even_v2 (A c n : Nat) (hApos : A ≠ 0) (hAev : A % 2 = 0) (hc : c ≠ 0) (hn : n ≠ 0) :
    v2 (iter (affineXorStep A c) n 0) =
      if n % 2 = 1 then v2 c else v2 n + v2 c + v2 A - 1 := by
  have ⟨hdecomp, hodd⟩ := v2_decomp c hc
  let e := v2 c
  let c0 := c / 2 ^ e
  have hT := affineXorStep_tperm A c0 hAev
  have htow := affineXor_tower A c0 hApos hAev hodd
  have hbase_mod : iter (affineXorStep A c0) 2 0 % 2 ^ v2 A = 0 := by simpa using (htow 0).1
  have hvA_ge1 : 1 ≤ v2 A := by
    have hv : v2 A = 1 + v2 (A / 2) := by
      conv => lhs; unfold v2
      simp [hApos, hAev]
    omega
  have hrem1 : iter (affineXorStep A c0) 1 0 % 2 ^ v2 A ≠ 0 := by
    simp only [iter, affineXorStep, Nat.mul_zero, Nat.zero_add, Nat.zero_xor]
    intro h0
    have hdvd : 2 ∣ 2 ^ v2 A := Nat.pow_dvd_pow 2 hvA_ge1
    have h1 := Nat.mod_mod_of_dvd c0 hdvd
    rw [h0, Nat.zero_mod] at h1
    dsimp only [c0, e] at h1
    omega
  have hne : iter (affineXorStep A c0) n 0 ≠ 0 := by
    by_cases hno : n % 2 = 1
    · intro h0
      have hdiv : n = 2 * (n / 2) + 1 := by omega
      have hmod := hT.iter_mod_periodic (v2 A) 0 2 (by simpa using hbase_mod) (n / 2) 1
      rw [← hdiv, h0, Nat.zero_mod] at hmod
      exact hrem1 hmod.symm
    · have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
      have ⟨_, hbit⟩ := tower_dvd_mod_testBit hT (v2 A) 2 (by omega) hbase_mod
        (fun k => (htow k).2) n hn hdvd
      intro h0; rw [h0, Nat.zero_testBit] at hbit; cases hbit
  conv => lhs; rw [hdecomp]
  rw [v2_shift_homogeneous (affineXorStep A (2 ^ e * c0)) (affineXorStep A c0) e n
        (affineXorStep_shift_hom A e c0) hne]
  by_cases hno : n % 2 = 1
  · simp only [hno, ↓reduceIte]
    have hv0 : v2 (iter (affineXorStep A c0) n 0) = 0 := by
      rw [tower_to_valuation_ndvd hT (v2 A) 2 hbase_mod n (by rw [hno]; exact hrem1), hno]
      simp only [iter, affineXorStep, Nat.mul_zero, Nat.zero_add, Nat.zero_xor]
      exact v2_of_odd c0 hodd
    rw [hv0]; omega
  · simp only [hno, ↓reduceIte]
    have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
    rw [tower_to_valuation_dvd hT (v2 A) 2 (by omega) hbase_mod (fun k => (htow k).2) n hn hdvd]
    have hv : v2 n = 1 + v2 (n / 2) := by
      conv => lhs; unfold v2
      simp [hn, show n % 2 = 0 by omega]
    dsimp only [e]
    omega

/-! ## Section 10: Sharpness Counterexamples & Kernel-Checked Non-Vacuity Witnesses -/

/-- **Sharpness 1 (`A = 1` in Affine-XOR, i.e. `a_{n+1} = a_n + (a_n ^^^ c)`)**:
    Odd `A` violates `TPerm` (2-adic contraction); for `A = 1`, the orbit stabilizes at `c` for all `n ≥ 1`! -/
theorem sharpness_affineXor_A1_stabilizes (c n : Nat) (hn : 1 ≤ n) :
    iter (affineXorStep 1 c) n 0 = c := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp [iter, affineXorStep]
    | succ m' =>
      rw [iter_succ, ih (by omega)]
      simp [affineXorStep]

/-- **Sharpness 2 (`A = 0` in Affine-XOR, i.e. `a_{n+1} = a_n ^^^ c`)**:
    `A = 0` has zero holonomy at every level: exact period 2 forever (`d_{2m} = 0`, `d_{2m+1} = c`)! -/
theorem sharpness_affineXor_A0_period2 (c m : Nat) :
    iter (affineXorStep 0 c) (2 * m) 0 = 0 ∧
    iter (affineXorStep 0 c) (2 * m + 1) 0 = c := by
  induction m with
  | zero => simp [iter, affineXorStep]
  | succ m ih =>
    have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    have hev : iter (affineXorStep 0 c) (2 * (m + 1)) 0 = 0 := by
      rw [h1, iter_succ, ih.2]; simp [affineXorStep]
    refine ⟨hev, ?_⟩
    rw [iter_succ, hev]; simp [affineXorStep]

/-- **Sharpness 3 (`(s, t) = (1, 2)` boundary in Theorem 2)**:
    Relaxing `t ≥ 3` to `(s, t) = (1, 2)` breaks `v2(b_n) = v2(c) + v2(n)` at `n = 4`
    (because `β_2(y) = y.testBit 0` sums to `1` over `[0, 2)`, flipping holonomy at `k = 2` to `false`)! -/
theorem sharpness_quadAnd_1_2_counterexample :
    iter (quadAndStep 1 2 1) 4 0 = 8 ∧
    v2 (iter (quadAndStep 1 2 1) 4 0) = 3 ∧
    v2 (iter (quadAndStep 1 2 1) 4 0) ≠ v2 1 + v2 4 ∧
    holonomy (quadAndStep 1 2 1) 2 0 4 = false := by
  have hval : iter (quadAndStep 1 2 1) 4 0 = 8 := by decide
  have hv8 : v2 8 = 3 := v2_eq_of_mod_testBit 8 3 (by decide) (by decide)
  have hv1 : v2 1 = 0 := v2_eq_of_mod_testBit 1 0 (by decide) (by decide)
  have hv4 : v2 4 = 2 := v2_eq_of_mod_testBit 4 2 (by decide) (by decide)
  have hhol : holonomy (quadAndStep 1 2 1) 2 0 4 = false := by decide
  refine ⟨hval, ?_, ?_, hhol⟩
  · rw [hval, hv8]
  · rw [hval, hv8, hv1, hv4]; omega

theorem sharpness_carryless_gray_period_collapse :
    iter (carrylessGrayStep 1) 4 0 = 8 ∧
    iter (carrylessGrayStep 1) 4 0 % 8 = 0 ∧
    holonomy (carrylessGrayStep 1) 2 0 4 = false ∧
    v2 (iter (carrylessGrayStep 1) 4 0) = 3 ∧
    v2 (iter (carrylessGrayStep 1) 4 0) ≠ v2 1 + v2 4 := by
  have hval : iter (carrylessGrayStep 1) 4 0 = 8 := by decide
  have hv8 : v2 8 = 3 := v2_eq_of_mod_testBit 8 3 (by decide) (by decide)
  have hv1 : v2 1 = 0 := v2_eq_of_mod_testBit 1 0 (by decide) (by decide)
  have hv4 : v2 4 = 2 := v2_eq_of_mod_testBit 4 2 (by decide) (by decide)
  have hmod : iter (carrylessGrayStep 1) 4 0 % 8 = 0 := by decide
  have hhol : holonomy (carrylessGrayStep 1) 2 0 4 = false := by decide
  refine ⟨hval, hmod, hhol, ?_, ?_⟩
  · rw [hval, hv8]
  · rw [hval, hv8, hv1, hv4]; omega

/-- **Non-Vacuity Gate**: Constructive kernel-checked witnesses proving every hypothesis
    (of `TPerm`, `OrbitBijection`, and all three main infinite theorems) is genuinely inhabited! -/
example : Nonempty (TPerm (grayCarryStep 1 7)) := ⟨grayCarryStep_tperm 1 7 (by omega)⟩
example : Nonempty (TPerm (quadAndStep 1 3 5)) := ⟨quadAndStep_tperm 1 3 5 (by omega) (by omega)⟩
example : Nonempty (TPerm (affineXorStep 6 11)) := ⟨affineXorStep_tperm 6 11 (by decide)⟩

/-- Concrete kernel-checked instantiations of Theorems 1A, 1B, 2, 3B: -/
example : v2 (iter (grayCarryStep 2 6) 12 0) = 3 := by
  rw [grayCarry_ge2_v2 2 6 12 (by omega) (by omega) (by omega)]
  have h6 : v2 6 = 1 := v2_eq_of_mod_testBit 6 1 (by decide) (by decide)
  have h12 : v2 12 = 2 := v2_eq_of_mod_testBit 12 2 (by decide) (by decide)
  omega

example : v2 (iter (grayCarryStep 1 7) 8 0) = 6 := by
  rw [grayCarry1_v2 7 8 (by omega) (by omega)]
  have h7 : v2 7 = 0 := v2_eq_of_mod_testBit 7 0 (by decide) (by decide)
  have h8 : v2 8 = 3 := v2_eq_of_mod_testBit 8 3 (by decide) (by decide)
  simp [h7, h8]

example : v2 (iter (quadAndStep 1 3 5) 16 0) = 4 := by
  rw [quadAnd_v2 1 3 5 16 (by omega) (by omega) (by omega) (by omega) (by omega)]
  have h5 : v2 5 = 0 := v2_eq_of_mod_testBit 5 0 (by decide) (by decide)
  have h16 : v2 16 = 4 := v2_eq_of_mod_testBit 16 4 (by decide) (by decide)
  omega

example : v2 (iter (affineXorStep 8 3) 4 0) = 4 := by
  rw [affineXor_even_v2 8 3 4 (by omega) (by omega) (by omega) (by omega)]
  have h3 : v2 3 = 0 := v2_eq_of_mod_testBit 3 0 (by decide) (by decide)
  have h4 : v2 4 = 2 := v2_eq_of_mod_testBit 4 2 (by decide) (by decide)
  have h8 : v2 8 = 3 := v2_eq_of_mod_testBit 8 3 (by decide) (by decide)
  simp [h3, h4, h8]

end CarryHolonomyEngine
