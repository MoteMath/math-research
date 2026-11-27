import MbaHenselBlockJetLifting.Defs

namespace MBAHensel
theorem pow2_pos (w : Nat) : 0 < 2 ^ w := Nat.two_pow_pos w

theorem pow2_dvd_pow2 {w1 w2 : Nat} (h : w1 ≤ w2) : 2 ^ w1 ∣ 2 ^ w2 :=
  Nat.pow_dvd_pow 2 h

theorem mod_pow2_mod {w1 w2 : Nat} (h : w1 ≤ w2) (a : Nat) :
    (a % 2 ^ w2) % 2 ^ w1 = a % 2 ^ w1 :=
  Nat.mod_mod_of_dvd a (pow2_dvd_pow2 h)

theorem evalMod_lt (w : Nat) (e : MBAExpr) (x : Nat) : evalMod w e x < 2 ^ w := by
  cases e with
  | var => exact Nat.mod_lt _ (pow2_pos w)
  | const c => exact Nat.mod_lt _ (pow2_pos w)
  | add a b => exact Nat.mod_lt _ (pow2_pos w)
  | sub a b => exact Nat.mod_lt _ (pow2_pos w)
  | mul a b => exact Nat.mod_lt _ (pow2_pos w)
  | bxor a b => exact Nat.mod_lt _ (pow2_pos w)
  | band a b => exact Nat.mod_lt _ (pow2_pos w)
  | bor a b => exact Nat.mod_lt _ (pow2_pos w)
  | bnot a =>
    have hpos := pow2_pos w
    simp only [evalMod]
    omega
  | shl a k => exact Nat.mod_lt _ (pow2_pos w)

/-- Bitwise mod-2^w congruence helper via `Nat.eq_of_testBit_eq`. -/
theorem mod_pow2_eq_of_testBit {w a b : Nat}
    (h : ∀ i < w, a.testBit i = b.testBit i) : a % 2 ^ w = b % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < w
  · simp [hi, h i hi]
  · simp [hi]

theorem nat_and_comm (a b : Nat) : (a &&& b) = (b &&& a) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_and, Bool.and_comm]

theorem nat_or_comm (a b : Nat) : (a ||| b) = (b ||| a) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_or, Bool.or_comm]

theorem nat_xor_comm (a b : Nat) : (a ^^^ b) = (b ^^^ a) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem xor_mod_pow2 (w a b : Nat) :
    (a ^^^ b) % 2 ^ w = ((a % 2 ^ w) ^^^ (b % 2 ^ w)) % 2 ^ w := by
  apply mod_pow2_eq_of_testBit
  intro i hi
  simp [Nat.testBit_xor, Nat.testBit_mod_two_pow, hi]

theorem land_mod_pow2 (w a b : Nat) :
    (a &&& b) % 2 ^ w = ((a % 2 ^ w) &&& (b % 2 ^ w)) % 2 ^ w := by
  apply mod_pow2_eq_of_testBit
  intro i hi
  simp [Nat.testBit_and, Nat.testBit_mod_two_pow, hi]

theorem lor_mod_pow2 (w a b : Nat) :
    (a ||| b) % 2 ^ w = ((a % 2 ^ w) ||| (b % 2 ^ w)) % 2 ^ w := by
  apply mod_pow2_eq_of_testBit
  intro i hi
  simp [Nat.testBit_or, Nat.testBit_mod_two_pow, hi]

theorem mod_add_cancel_right {m u v b : Nat} (hu : u < m) (hv : v < m) (hb : b < m)
    (h : (u + b) % m = (v + b) % m) : u = v := by
  by_cases h1 : u + b < m <;> by_cases h2 : v + b < m
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_of_lt h1] at h
    have hv2 : (v + b) % m = v + b - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hv2] at h; omega
  · rw [Nat.mod_eq_of_lt h2] at h
    have hu2 : (u + b) % m = u + b - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hu2] at h; omega
  · have hu2 : (u + b) % m = u + b - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hv2 : (v + b) % m = v + b - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hu2, hv2] at h; omega

theorem sub_mod_pow2_coherent {w1 w2 a b a' b' : Nat} (hw : w1 ≤ w2)
    (hb : b < 2 ^ w2) (hb' : b' < 2 ^ w1)
    (ha_eq : a % 2 ^ w1 = a') (hb_eq : b % 2 ^ w1 = b') :
    ((a + (2 ^ w2 - b)) % 2 ^ w2) % 2 ^ w1 = (a' + (2 ^ w1 - b')) % 2 ^ w1 := by
  rw [mod_pow2_mod hw]
  obtain ⟨k, hk⟩ := pow2_dvd_pow2 hw
  have h1 : (a + (2 ^ w2 - b) + b) % 2 ^ w1 = (a + 2 ^ w2) % 2 ^ w1 := by
    congr 1; omega
  have h2 : (a + 2 ^ w2) % 2 ^ w1 = a % 2 ^ w1 := by
    rw [hk, Nat.add_mul_mod_self_left]
  have hLHS : ((a + (2 ^ w2 - b)) % 2 ^ w1 + b') % 2 ^ w1 = a' % 2 ^ w1 := by
    rw [← hb_eq, ← Nat.add_mod, h1, h2, ha_eq]
    have ha' : a' < 2 ^ w1 := by rw [← ha_eq]; exact Nat.mod_lt _ (pow2_pos w1)
    exact (Nat.mod_eq_of_lt ha').symm
  have hRHS : ((a' + (2 ^ w1 - b')) % 2 ^ w1 + b') % 2 ^ w1 = a' % 2 ^ w1 := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have : a' + (2 ^ w1 - b') + b' = a' + 2 ^ w1 := by omega
    rw [this, Nat.add_mod_right]
  exact mod_add_cancel_right (Nat.mod_lt _ (pow2_pos w1)) (Nat.mod_lt _ (pow2_pos w1)) hb'
    (hLHS.trans hRHS.symm)

theorem bnot_mod_pow2_coherent {w1 w2 a a' : Nat} (hw : w1 ≤ w2)
    (ha : a < 2 ^ w2) (ha' : a' < 2 ^ w1) (ha_eq : a % 2 ^ w1 = a') :
    (2 ^ w2 - 1 - a) % 2 ^ w1 = 2 ^ w1 - 1 - a' := by
  have hpos1 := pow2_pos w1
  have hpos2 := pow2_pos w2
  obtain ⟨k, hk⟩ := pow2_dvd_pow2 hw
  have hsum : (2 ^ w2 - 1 - a + a + 1) % 2 ^ w1 = 0 := by
    have : 2 ^ w2 - 1 - a + a + 1 = 2 ^ w2 := by omega
    rw [this, hk, Nat.mul_mod_right]
  have hLHS : ((2 ^ w2 - 1 - a) % 2 ^ w1 + a') % 2 ^ w1 = (2 ^ w1 - 1) % 2 ^ w1 := by
    have hstep : ((2 ^ w2 - 1 - a) % 2 ^ w1 + a % 2 ^ w1 + 1) % 2 ^ w1 =
                 (2 ^ w2 - 1 - a + a + 1) % 2 ^ w1 := by
      have h12 : ((2 ^ w2 - 1 - a) % 2 ^ w1 + a % 2 ^ w1) % 2 ^ w1 =
                 (2 ^ w2 - 1 - a + a) % 2 ^ w1 := (Nat.add_mod _ _ _).symm
      rw [Nat.add_mod (_ + _), h12, ← Nat.add_mod]
    have h1 : ((2 ^ w2 - 1 - a) % 2 ^ w1 + a' + 1) % 2 ^ w1 = 0 := by
      rw [← ha_eq, hstep, hsum]
    have h2 : (((2 ^ w2 - 1 - a) % 2 ^ w1 + a') % 2 ^ w1 + 1) % 2 ^ w1 = 0 := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; exact h1
    have hlt : ((2 ^ w2 - 1 - a) % 2 ^ w1 + a') % 2 ^ w1 < 2 ^ w1 := Nat.mod_lt _ hpos1
    have hval : ((2 ^ w2 - 1 - a) % 2 ^ w1 + a') % 2 ^ w1 = 2 ^ w1 - 1 := by
      by_cases hlt1 : ((2 ^ w2 - 1 - a) % 2 ^ w1 + a') % 2 ^ w1 + 1 < 2 ^ w1
      · rw [Nat.mod_eq_of_lt hlt1] at h2; omega
      · omega
    rw [hval, Nat.mod_eq_of_lt (by omega)]
  have hRHS : ((2 ^ w1 - 1 - a') + a') % 2 ^ w1 = (2 ^ w1 - 1) % 2 ^ w1 := by
    congr 1; omega
  exact mod_add_cancel_right (Nat.mod_lt _ hpos1) (by omega) ha' (hLHS.trans hRHS.symm)

theorem evalMod_coherent (e : MBAExpr) : IsWidthCoherent (fun w x => evalMod w e x) := by
  refine ⟨fun w x => evalMod_lt w e x, ?_⟩
  intro w1 w2 x y hw hxy
  induction e with
  | var =>
    simp only [evalMod]
    rw [mod_pow2_mod hw, hxy]
  | const c =>
    simp only [evalMod]
    rw [mod_pow2_mod hw]
  | add a b iha ihb =>
    simp only [evalMod] at iha ihb ⊢
    rw [mod_pow2_mod hw, Nat.add_mod, iha, ihb]
  | sub a b iha ihb =>
    simp only [evalMod] at iha ihb ⊢
    exact sub_mod_pow2_coherent hw (evalMod_lt w2 b x) (evalMod_lt w1 b y) iha ihb
  | mul a b iha ihb =>
    simp only [evalMod] at iha ihb ⊢
    rw [mod_pow2_mod hw, Nat.mul_mod, iha, ihb]
  | bxor a b iha ihb =>
    simp only [evalMod] at iha ihb ⊢
    rw [mod_pow2_mod hw, xor_mod_pow2, iha, ihb]
  | band a b iha ihb =>
    simp only [evalMod] at iha ihb ⊢
    rw [mod_pow2_mod hw, land_mod_pow2, iha, ihb]
  | bor a b iha ihb =>
    simp only [evalMod] at iha ihb ⊢
    rw [mod_pow2_mod hw, lor_mod_pow2, iha, ihb]
  | bnot a iha =>
    simp only [evalMod] at iha ⊢
    exact bnot_mod_pow2_coherent hw (evalMod_lt w2 a x) (evalMod_lt w1 a y) iha
  | shl a k iha =>
    simp only [evalMod] at iha ⊢
    rw [mod_pow2_mod hw, Nat.mul_mod, iha]
    symm
    rw [Nat.mul_mod, Nat.mod_eq_of_lt (evalMod_lt w1 a y)]

/-! ## Section 2: General Order-v Silicon Hensel Lifting Engine -/

theorem countBelow_add (P : Nat → Bool) (a b : Nat) :
    countBelow P (a + b) = countBelow P a + countBelow (fun i => P (a + i)) b := by
  induction b with
  | zero => simp [countBelow]
  | succ b ih =>
    rw [Nat.add_succ, countBelow, ih, countBelow, Nat.add_assoc]

theorem countBelow_congr {P Q : Nat → Bool} {n : Nat} (h : ∀ i < n, P i = Q i) :
    countBelow P n = countBelow Q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countBelow]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem countBelow_eq_zero {P : Nat → Bool} {n : Nat} (h : ∀ i < n, P i = false) :
    countBelow P n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countBelow, h n (by omega), ih (fun i hi => h i (by omega))]
    rfl

theorem countBelow_periodic_mul (P : Nat → Bool) (m k : Nat)
    (h : ∀ j < k, ∀ y < m, P (j * m + y) = P y) :
    countBelow P (k * m) = k * countBelow P m := by
  induction k with
  | zero => simp [countBelow]
  | succ k ih =>
    have hmul : (k + 1) * m = k * m + m := Nat.succ_mul k m
    rw [hmul, countBelow_add, ih (fun j hj y hy => h j (by omega) y hy)]
    have h2 : countBelow (fun i => P (k * m + i)) m = countBelow P m :=
      countBelow_congr (fun y hy => h k (by omega) y hy)
    rw [h2, Nat.succ_mul]

/-- Exact 1-to-1 lifting conservation lemma for `countBelow`. -/
theorem countBelow_unique_lift {P Q R : Nat → Bool} {n : Nat}
    (hdead : ∀ y < n, P y = false → Q y = false ∧ R y = false)
    (hlive : ∀ y < n, P y = true → (Q y = true ∧ R y = false) ∨ (Q y = false ∧ R y = true)) :
    countBelow Q n + countBelow R n = countBelow P n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countBelow]
    have hprev := ih (fun y hy => hdead y (by omega)) (fun y hy => hlive y (by omega))
    cases hPn : P n with
    | false =>
      have ⟨hQ, hR⟩ := hdead n (by omega) hPn
      rw [hQ, hR]; simp; omega
    | true =>
      rcases hlive n (by omega) hPn with ⟨hQ, hR⟩ | ⟨hQ, hR⟩
      · rw [hQ, hR]; simp; omega
      · rw [hQ, hR]; simp; omega

theorem sumBelow_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) :
    sumBelow f n = sumBelow g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumBelow]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumBelow_add (f g : Nat → Nat) (n : Nat) :
    sumBelow (fun i => f i + g i) n = sumBelow f n + sumBelow g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumBelow]
    omega

theorem sumBelow_indicator (M idx : Nat) (hidx : idx < M) (v : Nat) :
    sumBelow (fun c => if idx = c then v else 0) M = v := by
  induction M with
  | zero => omega
  | succ M ih =>
    simp only [sumBelow]
    by_cases h : idx = M
    · subst h
      have h0 : sumBelow (fun c => if idx = c then v else 0) idx = 0 := by
        clear ih
        have hzero : ∀ k, (∀ c < k, idx ≠ c) →
            sumBelow (fun c => if idx = c then v else 0) k = 0 := by
          intro k hk
          induction k with
          | zero => rfl
          | succ k ihk =>
            simp only [sumBelow]
            rw [ihk (fun c hc => hk c (by omega)), ite_eq_right_iff.mpr (fun heq => absurd heq (hk k (by omega)))]
        exact hzero idx (fun c hc => by omega)
      simp [h0]
    · have hlt : idx < M := by omega
      simp [ih hlt, h]

/-- Residue-class partition identity: summing `countBelow` over all residue classes `c < M`
recovers the total `countBelow`. -/
theorem sumBelow_countBelow_mod (P : Nat → Bool) (M n : Nat) (hM : 0 < M) :
    sumBelow (fun c => countBelow (fun x => decide (x % M = c) && P x) n) M = countBelow P n := by
  induction n with
  | zero =>
    have h0 : ∀ k, sumBelow (fun _ => 0) k = 0 := by
      intro k; induction k with | zero => rfl | succ k ih => simp [sumBelow, ih]
    simpa [countBelow] using h0 M
  | succ n ih =>
    simp only [countBelow]
    rw [sumBelow_add, ih]
    congr 1
    have hstep : sumBelow (fun c => if (decide (n % M = c) && P n) = true then 1 else 0) M =
                 sumBelow (fun c => if n % M = c then (if P n = true then 1 else 0) else 0) M := by
      apply sumBelow_congr
      intro c _
      by_cases h1 : n % M = c <;> cases h2 : P n <;> simp [h1]
    rw [hstep]
    exact sumBelow_indicator M (n % M) (Nat.mod_lt n hM) (if P n = true then 1 else 0)

theorem rootCount_eq_sum_classes (F : Nat → Nat → Nat) (s w : Nat) :
    rootCount F w = sumBelow (fun c => classRootCount F s c w) (2 ^ s) :=
  (sumBelow_countBelow_mod (fun x => decide (F w x = 0)) (2 ^ s) (2 ^ w) (pow2_pos s)).symm

/-- Repeated shift invariance: under `HasOrderVSensitivity`, adding `j * 2^(w - v)` preserves `F w`. -/
theorem shift_mul_invariant {F : Nat → Nat → Nat} {s c w0 v : Nat}
    (hsens : HasOrderVSensitivity F s c w0 v) {w : Nat} (hw : w0 ≤ w)
    (j y : Nat) (hy : y % 2 ^ s = c) :
    F w (y + j * 2 ^ (w - v)) = F w y := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hsw : s ≤ w - v := by have := hsens.1; omega
    have hmod : (y + j * 2 ^ (w - v)) % 2 ^ s = c := by
      obtain ⟨q, hq⟩ := pow2_dvd_pow2 hsw
      rw [hq, ← Nat.mul_assoc, Nat.mul_comm j (2 ^ s), Nat.mul_assoc,
          Nat.add_mul_mod_self_left, hy]
    have hstep := (hsens.2 w (y + j * 2 ^ (w - v)) hw hmod).1
    have hrew : y + (j + 1) * 2 ^ (w - v) = (y + j * 2 ^ (w - v)) + 2 ^ (w - v) := by
      rw [Nat.succ_mul, Nat.add_assoc]
    rw [hrew, hstep, ih]

/-- **Engine Theorem 2.1 (Fiber Decomposition):**
Every core root `y < 2^(w - v)` expands to an exact fiber of `2^v` roots mod `2^w`. -/
theorem classRootCount_eq_pow_mul_core {F : Nat → Nat → Nat} {s c w0 v : Nat}
    (hsens : HasOrderVSensitivity F s c w0 v) {w : Nat} (hw : w0 ≤ w) :
    classRootCount F s c w = 2 ^ v * coreRootCount F s c v w := by
  unfold classRootCount coreRootCount
  have hv_le : v ≤ w := by have := hsens.1; omega
  have hpow : 2 ^ w = 2 ^ v * 2 ^ (w - v) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hv_le]
  rw [hpow]
  apply countBelow_periodic_mul
  intro j _ y _
  have hsw : s ≤ w - v := by have := hsens.1; omega
  obtain ⟨q, hq⟩ := pow2_dvd_pow2 hsw
  have hmod : (j * 2 ^ (w - v) + y) % 2 ^ s = y % 2 ^ s := by
    rw [hq, ← Nat.mul_assoc, Nat.mul_comm j (2 ^ s), Nat.mul_assoc, Nat.add_comm,
        Nat.add_mul_mod_self_left]
  by_cases hyc : y % 2 ^ s = c
  · have hF : F w (j * 2 ^ (w - v) + y) = F w y := by
      rw [Nat.add_comm]; exact shift_mul_invariant hsens hw j y hyc
    simp [hmod, hyc, hF]
  · simp [hmod, hyc]

/-- Helper: if `F` is width-coherent, `F w y = 0` means `F (w+1) y` is either `0` or `2^w`. -/
theorem eval_succ_dichotomy {F : Nat → Nat → Nat} (hcoh : IsWidthCoherent F)
    {w y : Nat} (h0 : F w y = 0) :
    F (w + 1) y = 0 ∨ F (w + 1) y = 2 ^ w := by
  have hlt : F (w + 1) y < 2 ^ (w + 1) := hcoh.1 (w + 1) y
  have hmod : F (w + 1) y % 2 ^ w = 0 := by
    rw [hcoh.2 w (w + 1) y y (Nat.le_succ w) rfl, h0]
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hpow : 2 ^ (w + 1) = 2 ^ w * 2 := Nat.pow_succ 2 w
  have hk2 : k < 2 := by
    rw [hk, hpow] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  have : k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl
  · left; simp [hk]
  · right; simp [hk]

/-- **Engine Theorem 2.2 (Core Root-Count Conservation):**
Under order-`v` sensitivity, the core root count in class `c` is strictly invariant `∀ w ≥ w0`. -/
theorem coreRootCount_step {F : Nat → Nat → Nat} {s c w0 v : Nat}
    (hcoh : IsWidthCoherent F) (hsens : HasOrderVSensitivity F s c w0 v)
    {w : Nat} (hw : w0 ≤ w) :
    coreRootCount F s c v (w + 1) = coreRootCount F s c v w := by
  unfold coreRootCount
  have hv_le : v ≤ w := by have := hsens.1; omega
  have hsw : s ≤ w - v := by have := hsens.1; omega
  have hsub : w + 1 - v = (w - v) + 1 := by omega
  rw [hsub, Nat.pow_succ, Nat.mul_two, countBelow_add]
  apply countBelow_unique_lift
  · -- Dead stays dead
    intro y _ hfalse
    have hmod : (2 ^ (w - v) + y) % 2 ^ s = y % 2 ^ s := by
      obtain ⟨q, hq⟩ := pow2_dvd_pow2 hsw
      rw [hq, Nat.add_comm, Nat.add_mul_mod_self_left]
    by_cases hyc : y % 2 ^ s = c
    · have hFy : F w y ≠ 0 := by
        intro h0; simp [hyc, h0] at hfalse
      have h1 : F (w + 1) y ≠ 0 := by
        intro h0
        have := hcoh.2 w (w + 1) y y (Nat.le_succ w) rfl
        rw [h0, Nat.zero_mod] at this
        exact hFy this.symm
      have h2 : F (w + 1) (2 ^ (w - v) + y) ≠ 0 := by
        intro h0
        have hstep := (hsens.2 w y hw hyc).1
        have := hcoh.2 w (w + 1) (2 ^ (w - v) + y) (2 ^ (w - v) + y) (Nat.le_succ w) rfl
        rw [h0, Nat.zero_mod, Nat.add_comm, hstep] at this
        exact hFy this.symm
      simp [hyc, hmod, h1, h2]
    · simp [hyc, hmod]
  · -- Live lifts to EXACTLY ONE child
    intro y _ htrue
    have hyc : y % 2 ^ s = c := by
      cases h1 : decide (y % 2 ^ s = c)
      · simp [h1] at htrue
      · exact of_decide_eq_true h1
    have hFy : F w y = 0 := by
      cases h2 : decide (F w y = 0)
      · simp [h2] at htrue
      · exact of_decide_eq_true h2
    have hmod : (y + 2 ^ (w - v)) % 2 ^ s = c := by
      obtain ⟨q, hq⟩ := pow2_dvd_pow2 hsw
      rw [hq, Nat.add_mul_mod_self_left, hyc]
    have ⟨hinv, hneq⟩ := hsens.2 w y hw hyc
    have hFy' : F w (y + 2 ^ (w - v)) = 0 := by rw [hinv, hFy]
    have hd1 := eval_succ_dichotomy hcoh hFy
    have hd2 := eval_succ_dichotomy hcoh hFy'
    have hpos := pow2_pos w
    rw [Nat.add_comm (2 ^ (w - v)) y]
    rcases hd1 with h10 | h1p <;> rcases hd2 with h20 | h2p
    · exfalso; exact hneq (h20.trans h10.symm)
    · left; simp [hyc, h10, h2p]
    · right; simp [hyc, hmod, h1p, h20]
    · exfalso; exact hneq (h2p.trans h1p.symm)

theorem coreRootCount_invariant {F : Nat → Nat → Nat} {s c w0 v : Nat}
    (hcoh : IsWidthCoherent F) (hsens : HasOrderVSensitivity F s c w0 v)
    {w : Nat} (hw : w0 ≤ w) :
    coreRootCount F s c v w = coreRootCount F s c v w0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hw
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, coreRootCount_step hcoh hsens (Nat.le_add_right w0 k),
        ih (Nat.le_add_right w0 k)]

/-- **Engine Theorem 2.3 (Exact Class Root-Count Conservation):** -/
theorem classRootCount_invariant {F : Nat → Nat → Nat} {s c w0 v : Nat}
    (hcoh : IsWidthCoherent F) (hsens : HasOrderVSensitivity F s c w0 v)
    {w : Nat} (hw : w0 ≤ w) :
    classRootCount F s c w = classRootCount F s c w0 := by
  rw [classRootCount_eq_pow_mul_core hsens hw,
      classRootCount_eq_pow_mul_core hsens (Nat.le_refl w0),
      coreRootCount_invariant hcoh hsens hw]

/-- **Engine Theorem 2.4 (Dead Class Extinction):**
If a residue class `c (mod 2^s)` has 0 roots at `w0` (with `s ≤ w0`), it has 0 roots `∀ w ≥ w0`. -/
theorem classRootCount_dead {F : Nat → Nat → Nat} {s c w0 : Nat}
    (hcoh : IsWidthCoherent F) (hsw : s ≤ w0)
    (hdead : classRootCount F s c w0 = 0) {w : Nat} (hw : w0 ≤ w) :
    classRootCount F s c w = 0 := by
  unfold classRootCount at hdead ⊢
  apply countBelow_eq_zero
  intro x _
  by_cases hxc : x % 2 ^ s = c
  · by_cases hFx : F w x = 0
    · exfalso
      -- Then x % 2^w0 < 2^w0 is a root at w0 in class c!
      have hx0_lt : x % 2 ^ w0 < 2 ^ w0 := Nat.mod_lt x (pow2_pos w0)
      have hx0_c : (x % 2 ^ w0) % 2 ^ s = c := by rw [mod_pow2_mod hsw, hxc]
      have hx0_F : F w0 (x % 2 ^ w0) = 0 := by
        have := hcoh.2 w0 w x (x % 2 ^ w0) hw (Nat.mod_mod _ _).symm
        rw [hFx, Nat.zero_mod] at this
        exact this.symm
      -- Show countBelow ≥ 1 contradicting hdead = 0
      have hge1 : ∀ (P : Nat → Bool) (n i : Nat), i < n → P i = true → 0 < countBelow P n := by
        intro P n i hi hPi
        induction n with
        | zero => omega
        | succ n ih =>
          simp only [countBelow]
          by_cases h : i = n
          · subst h; rw [hPi]; simp
          · have := ih (by omega); omega
      have hpos : 0 < countBelow (fun x => decide (x % 2 ^ s = c) && decide (F w0 x = 0)) (2 ^ w0) :=
        hge1 _ (2 ^ w0) (x % 2 ^ w0) hx0_lt (by simp [hx0_c, hx0_F])
      omega
    · simp [hxc, hFx]
  · simp [hxc]

/-- **Engine Theorem 2.5 (Non-Uniform Multi-Class Partition Theorem):**
If every residue class `c < 2^s` is EITHER dead at `w0` OR has some order-`v(c)` sensitivity
(with different `v(c)` allowed per class!), then `rootCount F w = rootCount F w0` for ALL `w ≥ w0`. -/
theorem rootCount_partition_invariant {F : Nat → Nat → Nat} {s w0 : Nat}
    (hcoh : IsWidthCoherent F) (hsw : s ≤ w0)
    (hpart : ∀ c < 2 ^ s,
      classRootCount F s c w0 = 0 ∨ ∃ v, HasOrderVSensitivity F s c w0 v)
    {w : Nat} (hw : w0 ≤ w) :
    rootCount F w = rootCount F w0 := by
  rw [rootCount_eq_sum_classes F s w, rootCount_eq_sum_classes F s w0]
  apply sumBelow_congr
  intro c hc
  rcases hpart c hc with hdead | ⟨v, hsens⟩
  · rw [classRootCount_dead hcoh hsw hdead hw, hdead]
  · exact classRootCount_invariant hcoh hsens hw

/-! ### Constructive Bit-by-Bit Silicon Lift (`liftCore`) & Fiber Exhaustion -/

/-- **Engine Theorem 2.6 (Constructive Infinite Bit-by-Bit Lift & Fiber Exhaustion):**
Given any base core root `y0 < 2^(w0 - v)` in class `c` with `F w0 y0 = 0`, `liftCore` produces
a genuine 2-adic projective root sequence valid for ALL `k : Nat`, whose `2^v`-fibers are all roots. -/
theorem liftCore_spec {F : Nat → Nat → Nat} {s c w0 v y0 : Nat}
    (hcoh : IsWidthCoherent F) (hsens : HasOrderVSensitivity F s c w0 v)
    (hy0_lt : y0 < 2 ^ (w0 - v)) (hy0_c : y0 % 2 ^ s = c) (hy0_root : F w0 y0 = 0) :
    ∀ k : Nat,
      let y := liftCore F v w0 y0 k
      y < 2 ^ (w0 + k - v) ∧
      y % 2 ^ s = c ∧
      F (w0 + k) y = 0 ∧
      liftCore F v w0 y0 (k + 1) % 2 ^ (w0 + k - v) = y ∧
      (∀ j < 2 ^ v, F (w0 + k) (y + j * 2 ^ (w0 + k - v)) = 0) := by
  have hbase : ∀ k : Nat,
      liftCore F v w0 y0 k < 2 ^ (w0 + k - v) ∧
      liftCore F v w0 y0 k % 2 ^ s = c ∧
      F (w0 + k) (liftCore F v w0 y0 k) = 0 := by
    intro k
    induction k with
    | zero => exact ⟨hy0_lt, hy0_c, hy0_root⟩
    | succ k ih =>
      obtain ⟨hlt, hc, hroot⟩ := ih
      let y := liftCore F v w0 y0 k
      let w := w0 + k
      have hw : w0 ≤ w := Nat.le_add_right w0 k
      have hsw : s ≤ w - v := by have := hsens.1; omega
      have hsub : w + 1 - v = (w - v) + 1 := by have := hsens.1; omega
      have hpow : 2 ^ (w + 1 - v) = 2 ^ (w - v) + 2 ^ (w - v) := by
        rw [hsub, Nat.pow_succ, Nat.mul_two]
      change liftStep F v w y < 2 ^ (w + 1 - v) ∧
             liftStep F v w y % 2 ^ s = c ∧
             F (w + 1) (liftStep F v w y) = 0
      unfold liftStep
      by_cases h0 : F (w + 1) y = 0
      · simp only [h0, ↓reduceIte]
        have hlt' : y < 2 ^ (w + 1 - v) := by
          rw [hpow]
          have : y < 2 ^ (w - v) := hlt
          omega
        exact ⟨hlt', hc, trivial⟩
      · simp only [h0, ↓reduceIte]
        have ⟨hinv, hneq⟩ := hsens.2 w y hw hc
        have hFy' : F w (y + 2 ^ (w - v)) = 0 := by rw [hinv, hroot]
        have hd1 := eval_succ_dichotomy hcoh hroot
        have hd2 := eval_succ_dichotomy hcoh hFy'
        have h1p : F (w + 1) y = 2 ^ w := by
          rcases hd1 with h | h
          · exact absurd h h0
          · exact h
        have h20 : F (w + 1) (y + 2 ^ (w - v)) = 0 := by
          rcases hd2 with h | h
          · exact h
          · exact absurd (h.trans h1p.symm) hneq
        have hc' : (y + 2 ^ (w - v)) % 2 ^ s = c := by
          obtain ⟨q, hq⟩ := pow2_dvd_pow2 hsw
          rw [hq, Nat.add_mul_mod_self_left, hc]
        have hlt' : y + 2 ^ (w - v) < 2 ^ (w + 1 - v) := by
          rw [hpow]
          have : y < 2 ^ (w - v) := hlt
          omega
        exact ⟨hlt', hc', h20⟩
  intro k
  obtain ⟨hlt, hc, hroot⟩ := hbase k
  refine ⟨hlt, hc, hroot, ?_, ?_⟩
  · -- Projective compatibility: y_{k+1} % 2^(w0 + k - v) = y_k
    change liftStep F v (w0 + k) (liftCore F v w0 y0 k) % 2 ^ (w0 + k - v) =
           liftCore F v w0 y0 k
    unfold liftStep
    split
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  · -- Fiber exhaustion: all 2^v lifts are roots
    intro j _
    rw [shift_mul_invariant hsens (Nat.le_add_right w0 k) j _ hc, hroot]

/-! ## Section 3: Symbolic MBA Differential Compiler (`symDeriv0`) -/

theorem hasExactDeriv0_to_order0 {e : MBAExpr} {w0 s r : Nat}
    (hsw : s ≤ w0) (hd : HasExactDeriv0 e w0 s r true) :
    HasOrderVSensitivity (fun w x => evalMod w e x) s r w0 0 := by
  refine ⟨by omega, ?_⟩
  intro w x hw hxr
  rw [Nat.sub_zero]
  refine ⟨?_, ?_⟩
  · -- Width-coherence: evalMod w e (x + 2^w) = evalMod w e x
    have hcoh := (evalMod_coherent e).2 w w (x + 2 ^ w) x (Nat.le_refl w) (Nat.add_mod_right x (2 ^ w))
    rwa [Nat.mod_eq_of_lt (evalMod_lt w e (x + 2 ^ w))] at hcoh
  · -- Sensitivity: adding 2^w mod 2^(w+1) changes the value
    dsimp only
    rw [hd w x hw hxr]
    simp only [↓reduceIte]
    have hlt := evalMod_lt (w + 1) e x
    have hpos := pow2_pos w
    have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ, Nat.mul_two]
    intro heq
    by_cases h1 : evalMod (w + 1) e x < 2 ^ w
    · rw [Nat.mod_eq_of_lt (by omega)] at heq; omega
    · have h2 : (evalMod (w + 1) e x + 2 ^ w) % 2 ^ (w + 1) =
                evalMod (w + 1) e x + 2 ^ w - 2 ^ (w + 1) := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [h2] at heq; omega

/-- Helper: adding `2^w` mod `2^(w+1)` flips bit `w` and preserves all bits `< w`. -/
theorem testBit_add_pow2_mod {w u i : Nat} (hi : i ≤ w) :
    ((u + 2 ^ w) % 2 ^ (w + 1)).testBit i =
      if i = w then !(u.testBit w) else u.testBit i := by
  rw [Nat.testBit_mod_two_pow]
  have hlt : i < w + 1 := by omega
  simp only [hlt, decide_true, Bool.true_and]
  have hsplit : u = u % 2 ^ w + 2 ^ w * (u / 2 ^ w) := (Nat.mod_add_div u (2 ^ w)).symm
  have hadd : u + 2 ^ w = u % 2 ^ w + 2 ^ w * (u / 2 ^ w + 1) := by
    rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, ← hsplit]
  by_cases heq : i = w
  · subst heq
    simp only [↓reduceIte]
    rw [Nat.testBit, Nat.testBit]
    have hdiv : (u + 2 ^ i) / 2 ^ i = u / 2 ^ i + 1 := by
      rw [Nat.add_div_right _ (pow2_pos i)]
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hdiv]
    cases h : (u / 2 ^ i) % 2 with
    | zero =>
      have : (u / 2 ^ i + 1) % 2 = 1 := by omega
      simp [h, this]
    | succ k =>
      have hk : k = 0 := by have := Nat.mod_lt (u / 2 ^ i) (by decide : 0 < 2); omega
      subst hk
      have : (u / 2 ^ i + 1) % 2 = 0 := by omega
      simp [h, this]
  · simp only [heq, ↓reduceIte]
    have hil : i < w := by omega
    have hdvd : 2 ^ (i + 1) ∣ 2 ^ w := pow2_dvd_pow2 (by omega)
    obtain ⟨m, hm⟩ := hdvd
    have hmod : (u + 2 ^ w) % 2 ^ (i + 1) = u % 2 ^ (i + 1) := by
      rw [hm, Nat.add_mul_mod_self_left]
    have htb1 : ((u + 2 ^ w) % 2 ^ (i + 1)).testBit i = (u + 2 ^ w).testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp
    have htb2 : (u % 2 ^ (i + 1)).testBit i = u.testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp
    rw [← htb1, hmod, htb2]

theorem add_bit_mod_pow2_succ (w u : Nat) (d1 d2 : Bool) :
    (((u + if d1 then 2 ^ w else 0) + if d2 then 2 ^ w else 0) % 2 ^ (w + 1)) =
      (u + if (d1 ^^ d2) then 2 ^ w else 0) % 2 ^ (w + 1) := by
  have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ, Nat.mul_two]
  cases d1 <;> cases d2 <;> simp
  rw [Nat.add_assoc, ← hpow, Nat.add_mod_right]

theorem add_deriv_rule {w a b : Nat} (da db : Bool) :
    (((a + if da then 2 ^ w else 0) % 2 ^ (w + 1) +
      (b + if db then 2 ^ w else 0) % 2 ^ (w + 1)) % 2 ^ (w + 1)) =
      ((a + b) % 2 ^ (w + 1) + if (da ^^ db) then 2 ^ w else 0) % 2 ^ (w + 1) := by
  have h1 : ((a + if da then 2 ^ w else 0) % 2 ^ (w + 1) +
             (b + if db then 2 ^ w else 0) % 2 ^ (w + 1)) % 2 ^ (w + 1) =
            ((a + b) + (if da then 2 ^ w else 0) + (if db then 2 ^ w else 0)) % 2 ^ (w + 1) := by
    rw [← Nat.add_mod]
    congr 1; omega
  rw [h1, add_bit_mod_pow2_succ]
  symm
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem sub_deriv_rule {w a b : Nat} (hb : b < 2 ^ (w + 1)) (da db : Bool) :
    (((a + if da then 2 ^ w else 0) % 2 ^ (w + 1) +
      (2 ^ (w + 1) - (b + if db then 2 ^ w else 0) % 2 ^ (w + 1))) % 2 ^ (w + 1)) =
      ((a + (2 ^ (w + 1) - b)) % 2 ^ (w + 1) + if (da ^^ db) then 2 ^ w else 0) % 2 ^ (w + 1) := by
  have hpos := pow2_pos w
  have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ, Nat.mul_two]
  have hsub_b : (2 ^ (w + 1) - (b + if db then 2 ^ w else 0) % 2 ^ (w + 1)) % 2 ^ (w + 1) =
                ((2 ^ (w + 1) - b) + if db then 2 ^ w else 0) % 2 ^ (w + 1) := by
    cases db with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [Nat.mod_eq_of_lt hb]
    | true =>
      simp only [↓reduceIte]
      by_cases hlt : b < 2 ^ w
      · have hlt2 : b + 2 ^ w < 2 ^ (w + 1) := by omega
        rw [Nat.mod_eq_of_lt hlt2]
        have h1 : 2 ^ (w + 1) - (b + 2 ^ w) = 2 ^ w - b := by omega
        have h2 : 2 ^ (w + 1) - b + 2 ^ w = (2 ^ w - b) + 2 ^ (w + 1) := by omega
        rw [h1, h2, Nat.add_mod_right]
      · have hmod : (b + 2 ^ w) % 2 ^ (w + 1) = b + 2 ^ w - 2 ^ (w + 1) := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        congr 1; omega
  rw [Nat.add_mod, hsub_b, ← Nat.add_mod]
  have hrew : ((a + if da then 2 ^ w else 0) % 2 ^ (w + 1) +
               ((2 ^ (w + 1) - b) + if db then 2 ^ w else 0) % 2 ^ (w + 1)) % 2 ^ (w + 1) =
              ((a + (2 ^ (w + 1) - b)) % 2 ^ (w + 1) + if (da ^^ db) then 2 ^ w else 0) % 2 ^ (w + 1) :=
    add_deriv_rule da db
  simpa only [Nat.add_mod, Nat.mod_mod] using hrew

theorem mul_deriv_rule {w a b : Nat} (hw : 1 ≤ w) (da db : Bool) :
    (((a + if da then 2 ^ w else 0) % 2 ^ (w + 1) *
      ((b + if db then 2 ^ w else 0) % 2 ^ (w + 1))) % 2 ^ (w + 1)) =
      ((a * b) % 2 ^ (w + 1) +
        if ((da && (b % 2 == 1)) ^^ ((a % 2 == 1) && db)) then 2 ^ w else 0) % 2 ^ (w + 1) := by
  rw [← Nat.mul_mod]
  have h2w : 2 ^ (w + 1) ∣ 2 ^ w * 2 ^ w := by
    rw [← Nat.pow_add]
    exact pow2_dvd_pow2 (by omega)
  have hterm : ∀ (t : Nat), (t * 2 ^ w) % 2 ^ (w + 1) =
      (if (t % 2 == 1) then 2 ^ w else 0) % 2 ^ (w + 1) := by
    intro t
    have hsplit : t = 2 * (t / 2) + t % 2 := (Nat.div_add_mod t 2).symm
    have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : t * 2 ^ w = (t / 2) * 2 ^ (w + 1) + (t % 2) * 2 ^ w := by
      calc t * 2 ^ w = (2 * (t / 2) + t % 2) * 2 ^ w := by rw [← hsplit]
        _ = 2 * (t / 2) * 2 ^ w + (t % 2) * 2 ^ w := Nat.add_mul _ _ _
        _ = (t / 2) * (2 * 2 ^ w) + (t % 2) * 2 ^ w := by
            rw [Nat.mul_comm 2 (t / 2), Nat.mul_assoc]
        _ = (t / 2) * 2 ^ (w + 1) + (t % 2) * 2 ^ w := by rw [← hpow]
    rw [h1, Nat.mul_comm (t / 2), Nat.mul_add_mod]
    have hmod2 : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases hmod2 with h0 | h1'
    · simp [h0]
    · simp [h1']
  have hexp : ((a + if da then 2 ^ w else 0) * (b + if db then 2 ^ w else 0)) % 2 ^ (w + 1) =
              ((a * b) +
                (if da then (b * 2 ^ w) else 0) +
                (if db then (a * 2 ^ w) else 0)) % 2 ^ (w + 1) := by
    cases da <;> cases db <;> simp
    · rw [Nat.mul_add]
    · rw [Nat.add_mul, Nat.mul_comm (2 ^ w) b]
    · obtain ⟨k, hk⟩ := h2w
      have hcalc : (a + 2 ^ w) * (b + 2 ^ w) = (a * b + b * 2 ^ w + a * 2 ^ w) + 2 ^ (w + 1) * k := by
        rw [← hk, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm (2 ^ w) b]
        omega
      rw [hcalc, Nat.add_mul_mod_self_left]
  rw [hexp]
  have hda : (if da then b * 2 ^ w else 0) % 2 ^ (w + 1) =
             (if (da && (b % 2 == 1)) then 2 ^ w else 0) % 2 ^ (w + 1) := by
    cases da <;> simp [hterm b]
  have hdb : (if db then a * 2 ^ w else 0) % 2 ^ (w + 1) =
             (if ((a % 2 == 1) && db) then 2 ^ w else 0) % 2 ^ (w + 1) := by
    cases db <;> simp [hterm a]
  rw [Nat.add_mod (a * b + _), hdb, Nat.add_mod (a * b), hda]
  have hcomb : (((a * b) % 2 ^ (w + 1) +
                  (if (da && (b % 2 == 1)) then 2 ^ w else 0) % 2 ^ (w + 1)) % 2 ^ (w + 1) +
                (if ((a % 2 == 1) && db) then 2 ^ w else 0) % 2 ^ (w + 1)) % 2 ^ (w + 1) =
               ((a * b) % 2 ^ (w + 1) +
                  (if (da && (b % 2 == 1)) then 2 ^ w else 0) +
                  (if ((a % 2 == 1) && db) then 2 ^ w else 0)) % 2 ^ (w + 1) := by
    symm
    rw [Nat.add_mod ((a * b) % _ + _), Nat.add_mod ((a * b) % _), Nat.mod_mod]
  rw [hcomb, add_bit_mod_pow2_succ]

theorem bxor_deriv_rule {w a b : Nat} (da db : Bool) :
    (((a + if da then 2 ^ w else 0) % 2 ^ (w + 1) ^^^
      (b + if db then 2 ^ w else 0) % 2 ^ (w + 1)) % 2 ^ (w + 1)) =
      ((a ^^^ b) % 2 ^ (w + 1) + if (da ^^ db) then 2 ^ w else 0) % 2 ^ (w + 1) := by
  apply mod_pow2_eq_of_testBit
  intro i hi
  have hle : i ≤ w := by omega
  rw [Nat.testBit_xor]
  have hA : ((a + if da then 2 ^ w else 0) % 2 ^ (w + 1)).testBit i =
      if i = w then (a.testBit w ^^ da) else a.testBit i := by
    cases da with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.bne_false]
      rw [Nat.testBit_mod_two_pow]; simp [hi]
      by_cases heq : i = w <;> simp [heq]
    | true =>
      simp only [↓reduceIte, Bool.bne_true]
      exact testBit_add_pow2_mod hle
  have hB : ((b + if db then 2 ^ w else 0) % 2 ^ (w + 1)).testBit i =
      if i = w then (b.testBit w ^^ db) else b.testBit i := by
    cases db with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.bne_false]
      rw [Nat.testBit_mod_two_pow]; simp [hi]
      by_cases heq : i = w <;> simp [heq]
    | true =>
      simp only [↓reduceIte, Bool.bne_true]
      exact testBit_add_pow2_mod hle
  have hR : (((a ^^^ b) % 2 ^ (w + 1) + if (da ^^ db) then 2 ^ w else 0) % 2 ^ (w + 1)).testBit i =
      if i = w then ((a.testBit w ^^ b.testBit w) ^^ (da ^^ db)) else (a.testBit i ^^ b.testBit i) := by
    cases h : (da ^^ db) with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.bne_false]
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_xor]
      simp [hi]
      by_cases heq : i = w <;> simp [heq]
    | true =>
      simp only [↓reduceIte, Bool.bne_true]
      rw [testBit_add_pow2_mod hle, Nat.testBit_mod_two_pow, Nat.testBit_xor]
      by_cases heq : i = w
      · subst heq; simp
      · simp [heq, hi]
  rw [Nat.testBit_mod_two_pow] at hR
  simp only [hi, decide_true, Bool.true_and] at hR
  rw [hA, hB]
  -- Simplify RHS testBit
  have hR' : (((a ^^^ b) % 2 ^ (w + 1) + if (da ^^ db) then 2 ^ w else 0)).testBit i =
      if i = w then ((a.testBit w ^^ b.testBit w) ^^ (da ^^ db)) else (a.testBit i ^^ b.testBit i) := hR
  rw [hR']
  by_cases heq : i = w
  · subst heq; simp; cases a.testBit i <;> cases b.testBit i <;> cases da <;> cases db <;> rfl
  · simp [heq]

theorem bnot_deriv_rule {w a : Nat} (ha : a < 2 ^ (w + 1)) (da : Bool) :
    ((2 ^ (w + 1) - 1) - (a + if da then 2 ^ w else 0) % 2 ^ (w + 1)) =
      (((2 ^ (w + 1) - 1) - a) + if da then 2 ^ w else 0) % 2 ^ (w + 1) := by
  have hpos := pow2_pos w
  have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ, Nat.mul_two]
  cases da with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)]
  | true =>
    simp only [↓reduceIte]
    by_cases hlt : a < 2 ^ w
    · rw [Nat.mod_eq_of_lt (by omega)]
      have h1 : 2 ^ (w + 1) - 1 - a + 2 ^ w = (2 ^ w - 1 - a) + 2 ^ (w + 1) := by omega
      have h2 : 2 ^ (w + 1) - 1 - (a + 2 ^ w) = 2 ^ w - 1 - a := by omega
      rw [h1, h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have hmod : (a + 2 ^ w) % 2 ^ (w + 1) = a + 2 ^ w - 2 ^ (w + 1) := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hmod, Nat.mod_eq_of_lt (by omega)]
      omega

/-- Key carry-free lemma: if `x % 2^s = r` and `r + c < 2^s`, then `x + c` agrees with `x`
at every bit `w ≥ s`. -/
theorem testBit_add_const_carry_free {s r c x w : Nat}
    (hxr : x % 2 ^ s = r) (hrc : r + c < 2 ^ s) (hsw : s ≤ w) :
    (x + c).testBit w = x.testBit w := by
  have hsplit : x = 2 ^ s * (x / 2 ^ s) + r := by rw [← hxr, Nat.div_add_mod]
  have hxc : x + c = 2 ^ s * (x / 2 ^ s) + (r + c) := by omega
  have hdiv : (x + c) / 2 ^ s = x / 2 ^ s := by
    rw [hxc, Nat.mul_add_div (pow2_pos s), Nat.div_eq_of_lt hrc, Nat.add_zero]
  rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hpow : 2 ^ w = 2 ^ s * 2 ^ (w - s) := by rw [← Nat.pow_add, Nat.add_sub_of_le hsw]
  rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]

/-- **Engine Theorem 3.1 (Soundness of Symbolic MBA Differential Compiler `symDeriv0`):** -/
theorem symDeriv0_sound {w0 s r : Nat} {e : MBAExpr} {d : Bool}
    (h : symDeriv0 w0 s r e = some d) : HasExactDeriv0 e w0 s r d := by
  induction e generalizing d with
  | var =>
    simp only [symDeriv0, Option.some.injEq] at h; subst h
    intro w x _ _
    simp only [evalMod, ↓reduceIte]
    symm
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  | const c =>
    simp only [symDeriv0, Option.some.injEq] at h; subst h
    intro w x _ _
    simp only [evalMod, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_mod]
  | add a b iha ihb =>
    simp only [symDeriv0] at h
    cases ha : symDeriv0 w0 s r a with
    | none => simp [ha] at h
    | some da =>
      cases hb : symDeriv0 w0 s r b with
      | none => simp [ha, hb] at h
      | some db =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        intro w x hw hxr
        simp only [evalMod]
        rw [iha ha w x hw hxr, ihb hb w x hw hxr]
        exact add_deriv_rule da db
  | sub a b iha ihb =>
    simp only [symDeriv0] at h
    cases ha : symDeriv0 w0 s r a with
    | none => simp [ha] at h
    | some da =>
      cases hb : symDeriv0 w0 s r b with
      | none => simp [ha, hb] at h
      | some db =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        intro w x hw hxr
        simp only [evalMod]
        rw [iha ha w x hw hxr, ihb hb w x hw hxr]
        exact sub_deriv_rule (evalMod_lt (w + 1) b x) da db
  | mul a b iha ihb =>
    simp only [symDeriv0] at h
    split at h
    · rename_i hws
      cases ha : symDeriv0 w0 s r a with
      | none => simp [ha] at h
      | some da =>
        cases hb : symDeriv0 w0 s r b with
        | none => simp [ha, hb] at h
        | some db =>
          simp only [ha, hb, Option.some.injEq] at h; subst h
          intro w x hw hxr
          simp only [evalMod]
          rw [iha ha w x hw hxr, ihb hb w x hw hxr]
          have ha0 : evalMod (w + 1) a x % 2 = evalMod 1 a r := by
            have h1 : x % 2 ^ 1 = r % 2 ^ 1 := by
              rw [← mod_pow2_mod hws.2 x, hxr]
            exact (evalMod_coherent a).2 1 (w + 1) x r (by omega) h1
          have hb0 : evalMod (w + 1) b x % 2 = evalMod 1 b r := by
            have h1 : x % 2 ^ 1 = r % 2 ^ 1 := by
              rw [← mod_pow2_mod hws.2 x, hxr]
            exact (evalMod_coherent b).2 1 (w + 1) x r (by omega) h1
          rw [mul_deriv_rule (by omega) da db, ha0, hb0]
    · simp at h
  | bxor a b iha ihb =>
    simp only [symDeriv0] at h
    cases ha : symDeriv0 w0 s r a with
    | none => simp [ha] at h
    | some da =>
      cases hb : symDeriv0 w0 s r b with
      | none => simp [ha, hb] at h
      | some db =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        intro w x hw hxr
        simp only [evalMod]
        rw [iha ha w x hw hxr, ihb hb w x hw hxr]
        exact bxor_deriv_rule da db
  | bnot a iha =>
    simp only [symDeriv0] at h
    intro w x hw hxr
    simp only [evalMod]
    rw [iha h w x hw hxr]
    exact bnot_deriv_rule (evalMod_lt (w + 1) a x) d
  | shl a k iha =>
    simp only [symDeriv0] at h
    split at h
    · rename_i hk0; subst hk0
      intro w x hw hxr
      simp only [evalMod, Nat.pow_zero, Nat.mul_one]
      rw [Nat.mod_eq_of_lt (evalMod_lt (w + 1) a (x + 2 ^ w)),
          Nat.mod_eq_of_lt (evalMod_lt (w + 1) a x)]
      exact iha h w x hw hxr
    · rename_i hkpos
      simp only [Option.some.injEq] at h; subst h
      intro w x _ _
      simp only [evalMod, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_mod]
      -- Since k ≥ 1, evalMod w a (x + 2^w) = evalMod w a x implies * 2^k agrees mod 2^(w+1)!
      have hcoh : evalMod (w + 1) a (x + 2 ^ w) % 2 ^ w = evalMod (w + 1) a x % 2 ^ w := by
        have h1 := (evalMod_coherent a).2 w (w + 1) (x + 2 ^ w) x (Nat.le_succ w) (Nat.add_mod_right x (2 ^ w))
        have h2 := (evalMod_coherent a).2 w (w + 1) x x (Nat.le_succ w) rfl
        exact h1.trans h2.symm
      have hk1 : 1 ≤ k := by omega
      have hpowk : 2 ^ k = 2 * 2 ^ (k - 1) := by
        have hk_eq : k = (k - 1) + 1 := by omega
        calc 2 ^ k = 2 ^ ((k - 1) + 1) := by rw [← hk_eq]
          _ = 2 ^ (k - 1) * 2 := Nat.pow_succ 2 (k - 1)
          _ = 2 * 2 ^ (k - 1) := Nat.mul_comm _ _
      have hdiv : ∀ u v : Nat, u % 2 ^ w = v % 2 ^ w → (u * 2 ^ k) % 2 ^ (w + 1) = (v * 2 ^ k) % 2 ^ (w + 1) := by
        intro u v huv
        have hu : u = u % 2 ^ w + 2 ^ w * (u / 2 ^ w) := (Nat.mod_add_div u (2 ^ w)).symm
        have hv : v = v % 2 ^ w + 2 ^ w * (v / 2 ^ w) := (Nat.mod_add_div v (2 ^ w)).symm
        have hmul : ∀ t q : Nat, ((t + 2 ^ w * q) * 2 ^ k) % 2 ^ (w + 1) = (t * 2 ^ k) % 2 ^ (w + 1) := by
          intro t q
          rw [Nat.add_mul, hpowk]
          have h2 : 2 ^ w * q * (2 * 2 ^ (k - 1)) = 2 ^ (w + 1) * (q * 2 ^ (k - 1)) := by
            rw [Nat.pow_succ]
            have : 2 ^ w * q * (2 * 2 ^ (k - 1)) = (2 ^ w * 2) * (q * 2 ^ (k - 1)) := by
              rw [Nat.mul_assoc, Nat.mul_left_comm q 2, ← Nat.mul_assoc]
            exact this
          rw [h2, Nat.add_mul_mod_self_left]
        rw [hu, hmul, hv, hmul, huv]
      exact hdiv _ _ hcoh
  | band a b iha ihb =>
    -- Case analysis matching symDeriv0
    have hconst_left : ∀ c (hc : c < 2 ^ w0) (e2 : MBAExpr),
        HasExactDeriv0 (.band (.const c) e2) w0 s r false := by
      intro c hc e2 w x hw _
      simp only [evalMod, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_mod]
      apply mod_pow2_eq_of_testBit
      intro i hi
      rw [Nat.testBit_and, Nat.testBit_and]
      by_cases hiw : i < w
      · have hcoh : evalMod (w + 1) e2 (x + 2 ^ w) % 2 ^ w = evalMod (w + 1) e2 x % 2 ^ w := by
          have h1 := (evalMod_coherent e2).2 w (w + 1) (x + 2 ^ w) x (Nat.le_succ w) (Nat.add_mod_right x (2 ^ w))
          have h2 := (evalMod_coherent e2).2 w (w + 1) x x (Nat.le_succ w) rfl
          exact h1.trans h2.symm
        have htb : (evalMod (w + 1) e2 (x + 2 ^ w)).testBit i = (evalMod (w + 1) e2 x).testBit i := by
          have h1 := congrArg (fun n => n.testBit i) hcoh
          rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at h1
          simpa [hiw] using h1
        rw [htb]
      · have hi_eq : i = w := by omega
        subst hi_eq
        have hlt : c < 2 ^ i := Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) hw)
        have hc0 : (c % 2 ^ (i + 1)).testBit i = false := by
          rw [Nat.testBit_mod_two_pow]
          have : c.testBit i = false := Nat.testBit_lt_two_pow hlt
          simp [this]
        simp [hc0]
    have hconst_right : ∀ c (hc : c < 2 ^ w0) (e1 : MBAExpr),
        HasExactDeriv0 (.band e1 (.const c)) w0 s r false := by
      intro c hc e1 w x hw hxr
      have hl := hconst_left c hc e1 w x hw hxr
      simpa only [evalMod, nat_and_comm] using hl
    have hcf_self : ∀ c (hsw : s ≤ w0) (hrc : r + c < 2 ^ s),
        HasExactDeriv0 (.band .var (.add .var (.const c))) w0 s r true := by
      intro c hsw hrc w x hw hxr
      simp only [evalMod, ↓reduceIte]
      apply mod_pow2_eq_of_testBit
      intro i hi
      rw [Nat.testBit_and]
      have hle : i ≤ w := by omega
      have hmod_rhs : (((x % 2 ^ (w + 1) &&& (x % 2 ^ (w + 1) + c % 2 ^ (w + 1)) % 2 ^ (w + 1)) % 2 ^ (w + 1) +
                        2 ^ w) % 2 ^ (w + 1)).testBit i =
                      if i = w then !((x % 2 ^ (w + 1) &&& (x % 2 ^ (w + 1) + c % 2 ^ (w + 1)) % 2 ^ (w + 1)).testBit w)
                      else (x % 2 ^ (w + 1) &&& (x % 2 ^ (w + 1) + c % 2 ^ (w + 1)) % 2 ^ (w + 1)).testBit i := by
        rw [testBit_add_pow2_mod hle]
        by_cases heq : i = w
        · subst heq; rw [Nat.testBit_mod_two_pow]; simp
        · rw [Nat.testBit_mod_two_pow]; simp [heq, hi]
      rw [Nat.testBit_mod_two_pow] at hmod_rhs
      simp only [hi, decide_true, Bool.true_and] at hmod_rhs
      rw [hmod_rhs]
      have hadd1 : ((x + 2 ^ w) % 2 ^ (w + 1) + c % 2 ^ (w + 1)) % 2 ^ (w + 1) = (x + c + 2 ^ w) % 2 ^ (w + 1) := by
        rw [← Nat.add_mod]; congr 1; omega
      have hadd2 : (x % 2 ^ (w + 1) + c % 2 ^ (w + 1)) % 2 ^ (w + 1) = (x + c) % 2 ^ (w + 1) := by
        rw [← Nat.add_mod]
      rw [hadd1, hadd2]
      by_cases heq : i = w
      · subst heq
        simp only [↓reduceIte, Nat.testBit_and]
        rw [testBit_add_pow2_mod (Nat.le_refl i), testBit_add_pow2_mod (Nat.le_refl i)]
        simp only [↓reduceIte, Nat.testBit_mod_two_pow, Nat.lt_succ_self, decide_true, Bool.true_and]
        have hcf := testBit_add_const_carry_free hxr hrc (by omega : s ≤ i)
        rw [hcf]
        cases x.testBit i <;> rfl
      · simp only [heq, ↓reduceIte, Nat.testBit_and]
        rw [testBit_add_pow2_mod hle, testBit_add_pow2_mod hle]
        simp only [heq, ↓reduceIte, Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]
    have hzero_abs : ∀ (ha : symDeriv0 w0 s r a = some false) (hb : symDeriv0 w0 s r b = some false),
        HasExactDeriv0 (.band a b) w0 s r false := by
      intro ha hb w x hw hxr
      simp only [evalMod, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_mod]
      have h1 := iha ha w x hw hxr
      have h2 := ihb hb w x hw hxr
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_eq_of_lt (evalMod_lt (w + 1) a x),
                 Nat.mod_eq_of_lt (evalMod_lt (w + 1) b x)] at h1 h2
      rw [h1, h2]
    simp only [symDeriv0] at h
    by_cases hbc : (isBoundedConst w0 a || isBoundedConst w0 b) = true
    · simp only [hbc, ↓reduceIte, Option.some.injEq] at h; subst h
      rw [Bool.or_eq_true] at hbc
      rcases hbc with ha_c | hb_c
      · cases a with
        | const c => exact hconst_left c (of_decide_eq_true ha_c) b
        | _ => simp [isBoundedConst] at ha_c
      · cases b with
        | const c => exact hconst_right c (of_decide_eq_true hb_c) a
        | _ => simp [isBoundedConst] at hb_c
    · simp only [hbc, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hcfp : isCarryFreeSelfPair w0 s r a b = true
      · simp only [hcfp, ↓reduceIte, Option.some.injEq] at h; subst h
        cases a with
        | var =>
          cases b with
          | add b1 b2 =>
            cases b1 with
            | var =>
              cases b2 with
              | const c =>
                have hp := of_decide_eq_true hcfp
                exact hcf_self c hp.1 hp.2
              | _ => simp [isCarryFreeSelfPair] at hcfp
            | _ => simp [isCarryFreeSelfPair] at hcfp
          | _ => simp [isCarryFreeSelfPair] at hcfp
        | add a1 a2 =>
          cases a1 with
          | var =>
            cases a2 with
            | const c =>
              cases b with
              | var =>
                have hp := of_decide_eq_true hcfp
                intro w x hw hxr
                have h1 := hcf_self c hp.1 hp.2 w x hw hxr
                simpa only [evalMod, nat_and_comm] using h1
              | _ => simp [isCarryFreeSelfPair] at hcfp
            | _ => simp [isCarryFreeSelfPair] at hcfp
          | _ => simp [isCarryFreeSelfPair] at hcfp
        | _ => simp [isCarryFreeSelfPair] at hcfp
      · simp only [hcfp, Bool.false_eq_true, ↓reduceIte] at h
        cases ha : symDeriv0 w0 s r a with
        | none => simp [ha] at h
        | some da =>
          cases hb : symDeriv0 w0 s r b with
          | none => simp [ha, hb] at h
          | some db =>
            cases da <;> cases db <;> simp [ha, hb] at h
            subst h; exact hzero_abs ha hb
  | bor a b iha ihb =>
    have hconst_left : ∀ c (hc : c < 2 ^ w0) (e2 : MBAExpr) (db : Bool),
        HasExactDeriv0 e2 w0 s r db → HasExactDeriv0 (.bor (.const c) e2) w0 s r db := by
      intro c hc e2 db hdb w x hw hxr
      have h2 := hdb w x hw hxr
      simp only [evalMod]
      rw [h2]
      apply mod_pow2_eq_of_testBit
      intro i hi
      have hle : i ≤ w := by omega
      rw [Nat.testBit_or]
      have hR : (((c % 2 ^ (w + 1) ||| evalMod (w + 1) e2 x) % 2 ^ (w + 1) +
                  if db then 2 ^ w else 0)).testBit i =
                if i = w then (((c % 2 ^ (w + 1)).testBit w || (evalMod (w + 1) e2 x).testBit w) ^^ db)
                else ((c % 2 ^ (w + 1)).testBit i || (evalMod (w + 1) e2 x).testBit i) := by
        have hstep : (((c % 2 ^ (w + 1) ||| evalMod (w + 1) e2 x) % 2 ^ (w + 1) +
                      if db then 2 ^ w else 0) % 2 ^ (w + 1)).testBit i =
                     if i = w then (((c % 2 ^ (w + 1)).testBit w || (evalMod (w + 1) e2 x).testBit w) ^^ db)
                     else ((c % 2 ^ (w + 1)).testBit i || (evalMod (w + 1) e2 x).testBit i) := by
          cases db with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.bne_false]
            rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_or]
            by_cases heq : i = w <;> simp [heq, hi]
          | true =>
            simp only [↓reduceIte, Bool.bne_true]
            rw [testBit_add_pow2_mod hle, Nat.testBit_mod_two_pow, Nat.testBit_or]
            by_cases heq : i = w
            · subst heq; simp
            · simp [heq, hi]
        rw [Nat.testBit_mod_two_pow] at hstep
        simpa [hi] using hstep
      rw [hR]
      have hL : ((evalMod (w + 1) e2 x + if db then 2 ^ w else 0) % 2 ^ (w + 1)).testBit i =
                if i = w then ((evalMod (w + 1) e2 x).testBit w ^^ db)
                else (evalMod (w + 1) e2 x).testBit i := by
        cases db with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.bne_false]
          rw [Nat.testBit_mod_two_pow]; by_cases heq : i = w <;> simp [heq, hi]
        | true =>
          simp only [↓reduceIte, Bool.bne_true]
          exact testBit_add_pow2_mod hle
      rw [hL]
      by_cases heq : i = w
      · subst heq
        have hlt : c < 2 ^ i := Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) hw)
        have hc0 : (c % 2 ^ (i + 1)).testBit i = false := by
          rw [Nat.testBit_mod_two_pow]; simp [Nat.testBit_lt_two_pow hlt]
        simp [hc0]
      · simp [heq]
    have hzero_abs : ∀ (ha : symDeriv0 w0 s r a = some false) (hb : symDeriv0 w0 s r b = some false),
        HasExactDeriv0 (.bor a b) w0 s r false := by
      intro ha hb w x hw hxr
      simp only [evalMod, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_mod]
      have h1 := iha ha w x hw hxr
      have h2 := ihb hb w x hw hxr
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mod_eq_of_lt (evalMod_lt (w + 1) a x),
                 Nat.mod_eq_of_lt (evalMod_lt (w + 1) b x)] at h1 h2
      rw [h1, h2]
    simp only [symDeriv0] at h
    by_cases ha_c : isBoundedConst w0 a = true
    · simp only [ha_c, ↓reduceIte] at h
      cases a with
      | const c => exact hconst_left c (of_decide_eq_true ha_c) b d (ihb h)
      | _ => simp [isBoundedConst] at ha_c
    · simp only [ha_c, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hb_c : isBoundedConst w0 b = true
      · simp only [hb_c, ↓reduceIte] at h
        cases b with
        | const c =>
          intro w x hw hxr
          have hl := hconst_left c (of_decide_eq_true hb_c) a d (iha h) w x hw hxr
          simpa only [evalMod, nat_or_comm] using hl
        | _ => simp [isBoundedConst] at hb_c
      · simp only [hb_c, Bool.false_eq_true, ↓reduceIte] at h
        cases ha : symDeriv0 w0 s r a with
        | none => simp [ha] at h
        | some da =>
          cases hb : symDeriv0 w0 s r b with
          | none => simp [ha, hb] at h
          | some db =>
            cases da <;> cases db <;> simp [ha, hb] at h
            subst h; exact hzero_abs ha hb

theorem rootCount_of_checkOrder0Cert {e : MBAExpr} {w0 s : Nat}
    (hcert : checkOrder0Cert e w0 s = true) {w : Nat} (hw : w0 ≤ w) :
    rootCount (fun w x => evalMod w e x) w = rootCount (fun w x => evalMod w e x) w0 := by
  unfold checkOrder0Cert at hcert
  rw [Bool.and_eq_true] at hcert
  have hsw : s ≤ w0 := of_decide_eq_true hcert.1
  have hall := List.all_eq_true.mp hcert.2
  apply rootCount_partition_invariant (evalMod_coherent e) hsw _ hw
  intro c hc
  have hmem : c ∈ List.range (2 ^ s) := List.mem_range.mpr hc
  have hc_ok := hall c hmem
  rw [Bool.or_eq_true] at hc_ok
  rcases hc_ok with hdead | hlive
  · left; exact of_decide_eq_true hdead
  · right
    refine ⟨0, hasExactDeriv0_to_order0 hsw (symDeriv0_sound ?_)⟩
    exact beq_iff_eq.mp hlive

/-! ## Section 4: Exact Affine Block-Jet Quadratic Lifting Engine (`w → 2*w`) -/

theorem modInvPow2_lt (a w : Nat) : modInvPow2 a w < 2 ^ w := by
  induction w with
  | zero => simp [modInvPow2]
  | succ w ih =>
    simp only [modInvPow2]
    have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ, Nat.mul_two]
    split <;> omega

theorem modInvPow2_spec {a : Nat} (hodd : a % 2 = 1) (w : Nat) :
    (a * modInvPow2 a w) % 2 ^ w = 1 % 2 ^ w := by
  induction w with
  | zero => simp [modInvPow2]
  | succ w ih =>
    simp only [modInvPow2]
    let inv := modInvPow2 a w
    have h1lt : 1 < 2 ^ (w + 1) := by
      have := pow2_pos w
      have : 2 ^ (w + 1) = 2 ^ w * 2 := Nat.pow_succ 2 w
      omega
    rw [Nat.mod_eq_of_lt h1lt]
    by_cases h1 : (a * inv) % 2 ^ (w + 1) = 1
    · dsimp only [inv] at h1 ⊢
      simp only [h1, ↓reduceIte]
    · dsimp only [inv] at h1 ⊢
      simp only [h1, ↓reduceIte]
      cases w with
      | zero =>
        simp only [Nat.pow_zero, Nat.pow_one, modInvPow2, Nat.zero_add, Nat.mul_one] at h1 ⊢
        exact hodd
      | succ w' =>
        have hpos : 1 < 2 ^ (w' + 1) := by
          have := pow2_pos w'
          have : 2 ^ (w' + 1) = 2 ^ w' * 2 := Nat.pow_succ 2 w'
          omega
        rw [Nat.mod_eq_of_lt hpos] at ih
        have hmod : ((a * modInvPow2 a (w' + 1)) % 2 ^ (w' + 1 + 1)) % 2 ^ (w' + 1) = 1 := by
          rw [mod_pow2_mod (Nat.le_succ _)]; exact ih
        have hlt : (a * modInvPow2 a (w' + 1)) % 2 ^ (w' + 1 + 1) < 2 ^ (w' + 1 + 1) := Nat.mod_lt _ (pow2_pos _)
        have hpow : 2 ^ (w' + 1 + 1) = 2 ^ (w' + 1) + 2 ^ (w' + 1) := by
          rw [Nat.pow_succ, Nat.mul_two]
        have hval : (a * modInvPow2 a (w' + 1)) % 2 ^ (w' + 1 + 1) = 1 + 2 ^ (w' + 1) := by
          by_cases hu : (a * modInvPow2 a (w' + 1)) % 2 ^ (w' + 1 + 1) < 2 ^ (w' + 1)
          · rw [Nat.mod_eq_of_lt hu] at hmod; exact absurd hmod h1
          · have hsub : ((a * modInvPow2 a (w' + 1)) % 2 ^ (w' + 1 + 1)) % 2 ^ (w' + 1) =
                        (a * modInvPow2 a (w' + 1)) % 2 ^ (w' + 1 + 1) - 2 ^ (w' + 1) := by
              rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
            rw [hsub] at hmod; omega
        have hmul : a * (modInvPow2 a (w' + 1) + 2 ^ (w' + 1)) =
                    a * modInvPow2 a (w' + 1) + a * 2 ^ (w' + 1) := Nat.mul_add _ _ _
        have ha2 : (a * 2 ^ (w' + 1)) % 2 ^ (w' + 1 + 1) = 2 ^ (w' + 1) := by
          have hsplit : a = 2 * (a / 2) + 1 := by omega
          have hcalc : a * 2 ^ (w' + 1) = 2 ^ (w' + 1 + 1) * (a / 2) + 2 ^ (w' + 1) := by
            calc a * 2 ^ (w' + 1) = (2 * (a / 2) + 1) * 2 ^ (w' + 1) := by rw [← hsplit]
              _ = 2 * (a / 2) * 2 ^ (w' + 1) + 2 ^ (w' + 1) := by rw [Nat.add_mul, Nat.one_mul]
              _ = (2 ^ (w' + 1) * 2) * (a / 2) + 2 ^ (w' + 1) := by
                  rw [Nat.mul_comm 2 (a / 2), Nat.mul_assoc, Nat.mul_comm (a / 2),
                      Nat.mul_comm 2 (2 ^ (w' + 1))]
              _ = 2 ^ (w' + 1 + 1) * (a / 2) + 2 ^ (w' + 1) := by rw [← Nat.pow_succ]
          rw [hcalc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        rw [hmul, Nat.add_mod, hval, ha2]
        have hsum : 1 + 2 ^ (w' + 1) + 2 ^ (w' + 1) = 1 + 2 ^ (w' + 1 + 1) := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt h1lt]

theorem pow2_two_mul (w : Nat) : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by
  rw [Nat.two_mul, Nat.pow_add]

theorem block_lt {w u v : Nat} (hu : u < 2 ^ w) (hv : v < 2 ^ w) :
    u + 2 ^ w * v < 2 ^ (2 * w) := by
  rw [pow2_two_mul]
  have h1 : 2 ^ w * (v + 1) ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left (2 ^ w) hv
  rw [Nat.mul_add, Nat.mul_one] at h1
  omega

/-- Fundamental bit-block splitting identity for `u + 2^w * v` when `u < 2^w`. -/
theorem testBit_split_block {w u v i : Nat} (hu : u < 2 ^ w) :
    (u + 2 ^ w * v).testBit i = if i < w then u.testBit i else v.testBit (i - w) := by
  by_cases hi : i < w
  · simp only [hi, ↓reduceIte]
    have hdvd : 2 ^ (i + 1) ∣ 2 ^ w := pow2_dvd_pow2 (by omega)
    obtain ⟨m, hm⟩ := hdvd
    have hmod : (u + 2 ^ w * v) % 2 ^ (i + 1) = u % 2 ^ (i + 1) := by
      rw [hm, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    have h1 : ((u + 2 ^ w * v) % 2 ^ (i + 1)).testBit i = (u + 2 ^ w * v).testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp
    have h2 : (u % 2 ^ (i + 1)).testBit i = u.testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp
    rw [← h1, hmod, h2]
  · simp only [hi, ↓reduceIte]
    have hwi : w ≤ i := by omega
    rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have hpow : 2 ^ i = 2 ^ w * 2 ^ (i - w) := by rw [← Nat.pow_add, Nat.add_sub_of_le hwi]
    have hdiv : (u + 2 ^ w * v) / 2 ^ w = v := by
      rw [Nat.add_comm, Nat.mul_add_div (pow2_pos w), Nat.div_eq_of_lt hu, Nat.add_zero]
    rw [hpow, ← Nat.div_div_eq_div_mul, hdiv]

theorem xor_split_block {w u1 v1 u2 v2 : Nat}
    (hu1 : u1 < 2 ^ w) (hu2 : u2 < 2 ^ w) :
    (u1 + 2 ^ w * v1) ^^^ (u2 + 2 ^ w * v2) = (u1 ^^^ u2) + 2 ^ w * (v1 ^^^ v2) := by
  have hu_lt : (u1 ^^^ u2) < 2 ^ w := by
    have hmod : (u1 ^^^ u2) % 2 ^ w = (u1 ^^^ u2) := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
      by_cases hi : i < w
      · simp [hi]
      · have h1 : u1.testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu1 (Nat.pow_le_pow_right (by decide) (by omega)))
        have h2 : u2.testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu2 (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [hi, h1, h2]
    rw [← hmod]; exact Nat.mod_lt _ (pow2_pos w)
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, testBit_split_block hu1, testBit_split_block hu2, testBit_split_block hu_lt]
  by_cases hi : i < w <;> simp [hi, Nat.testBit_xor]

theorem and_split_block {w u1 v1 u2 v2 : Nat}
    (hu1 : u1 < 2 ^ w) (hu2 : u2 < 2 ^ w) :
    (u1 + 2 ^ w * v1) &&& (u2 + 2 ^ w * v2) = (u1 &&& u2) + 2 ^ w * (v1 &&& v2) := by
  have hu_lt : (u1 &&& u2) < 2 ^ w := by
    have hmod : (u1 &&& u2) % 2 ^ w = (u1 &&& u2) := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_mod_two_pow, Nat.testBit_and]
      by_cases hi : i < w
      · simp [hi]
      · have h1 : u1.testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu1 (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [hi, h1]
    rw [← hmod]; exact Nat.mod_lt _ (pow2_pos w)
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, testBit_split_block hu1, testBit_split_block hu2, testBit_split_block hu_lt]
  by_cases hi : i < w <;> simp [hi, Nat.testBit_and]

theorem or_split_block {w u1 v1 u2 v2 : Nat}
    (hu1 : u1 < 2 ^ w) (hu2 : u2 < 2 ^ w) :
    (u1 + 2 ^ w * v1) ||| (u2 + 2 ^ w * v2) = (u1 ||| u2) + 2 ^ w * (v1 ||| v2) := by
  have hu_lt : (u1 ||| u2) < 2 ^ w := by
    have hmod : (u1 ||| u2) % 2 ^ w = (u1 ||| u2) := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
      by_cases hi : i < w
      · simp [hi]
      · have h1 : u1.testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu1 (Nat.pow_le_pow_right (by decide) (by omega)))
        have h2 : u2.testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu2 (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [hi, h1, h2]
    rw [← hmod]; exact Nat.mod_lt _ (pow2_pos w)
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, testBit_split_block hu1, testBit_split_block hu2, testBit_split_block hu_lt]
  by_cases hi : i < w <;> simp [hi, Nat.testBit_or]

theorem testBit_two_pow_sub_one (w j : Nat) :
    (2 ^ w - 1).testBit j = decide (j < w) := by
  induction w generalizing j with
  | zero => simp
  | succ w ih =>
    cases j with
    | zero =>
      have hpos := pow2_pos w
      have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
      have hodd : (2 ^ (w + 1) - 1) % 2 = 1 := by omega
      simp [Nat.testBit_zero, hodd]
    | succ j' =>
      have hpos := pow2_pos w
      have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
      have hdiv : (2 ^ (w + 1) - 1) / 2 = 2 ^ w - 1 := by omega
      rw [Nat.testBit_succ, hdiv, ih j']
      simp [Nat.succ_lt_succ_iff]

theorem xor_all_ones {w u : Nat} (hu : u < 2 ^ w) :
    u ^^^ (2 ^ w - 1) = 2 ^ w - 1 - u := by
  have hsum : ∀ w u, u < 2 ^ w → u ^^^ (2 ^ w - 1 - u) = 2 ^ w - 1 := by
    intro w
    induction w with
    | zero =>
      intro u hu; have : u = 0 := by omega
      subst this; rfl
    | succ w ih =>
      intro u hu
      have hpos := pow2_pos w
      have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
      have hu2 : u / 2 < 2 ^ w := by omega
      have hsub_div : (2 ^ (w + 1) - 1 - u) / 2 = 2 ^ w - 1 - u / 2 := by omega
      have hsub_mod : (2 ^ (w + 1) - 1 - u) % 2 = 1 - u % 2 := by omega
      apply Nat.eq_of_testBit_eq; intro k
      cases k with
      | zero =>
        rw [Nat.testBit_xor, testBit_two_pow_sub_one]
        simp only [Nat.succ_pos, decide_true, Nat.testBit_zero, hsub_mod]
        have : u % 2 = 0 ∨ u % 2 = 1 := by omega
        rcases this with h | h <;> simp [h]
      | succ k' =>
        rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, hsub_div, testBit_two_pow_sub_one]
        have hih := congrArg (fun n => Nat.testBit n k') (ih (u / 2) hu2)
        rw [Nat.testBit_xor, testBit_two_pow_sub_one] at hih
        rw [hih]
        simp [Nat.succ_lt_succ_iff]
  apply Nat.eq_of_testBit_eq; intro i
  have hbit := congrArg (fun n => Nat.testBit n i) (hsum w u hu)
  rw [Nat.testBit_xor] at hbit ⊢
  rw [← hbit]
  cases u.testBit i <;> cases (2 ^ w - 1 - u).testBit i <;> rfl

theorem and_all_ones {w u : Nat} (hu : u < 2 ^ w) :
    u &&& (2 ^ w - 1) = u := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, testBit_two_pow_sub_one]
  by_cases hi : i < w
  · simp [hi]
  · have h0 : u.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, h0]

theorem or_all_ones {w u : Nat} (hu : u < 2 ^ w) :
    u ||| (2 ^ w - 1) = 2 ^ w - 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, testBit_two_pow_sub_one]
  by_cases hi : i < w
  · simp [hi]
  · have h0 : u.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, h0]

theorem nat_xor_self (u : Nat) : u ^^^ u = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; simp

theorem nat_and_self (u : Nat) : u &&& u = u := by
  apply Nat.eq_of_testBit_eq; intro i; simp

theorem nat_or_self (u : Nat) : u ||| u = u := by
  apply Nat.eq_of_testBit_eq; intro i; simp

theorem bnot_affine_mod {w q a Δ : Nat} (hq : q < 2 ^ w) (ha : a < 2 ^ w) :
    2 ^ w - 1 - (q + a * Δ) % 2 ^ w = ((2 ^ w - 1 - q) + ((2 ^ w - a) % 2 ^ w) * Δ) % 2 ^ w := by
  have hpos := pow2_pos w
  have hsum : ((2 ^ w - 1 - q) + ((2 ^ w - a) % 2 ^ w) * Δ + (q + a * Δ) % 2 ^ w) % 2 ^ w =
              (2 ^ w - 1) % 2 ^ w := by
    have h1 : (((2 ^ w - 1 - q) + ((2 ^ w - a) % 2 ^ w) * Δ) + (q + a * Δ)) % 2 ^ w =
              (2 ^ w - 1) % 2 ^ w := by
      have h2 : (2 ^ w - 1 - q) + ((2 ^ w - a) % 2 ^ w) * Δ + (q + a * Δ) =
                (2 ^ w - 1) + (((2 ^ w - a) % 2 ^ w + a) * Δ) := by
        rw [Nat.add_mul]
        omega
      rw [h2]
      have hma : ((2 ^ w - a) % 2 ^ w + a) % 2 ^ w = 0 := by
        by_cases ha0 : a = 0
        · subst ha0; simp
        · rw [Nat.mod_eq_of_lt (by omega : 2 ^ w - a < 2 ^ w)]
          have : 2 ^ w - a + a = 2 ^ w := by omega
          rw [this, Nat.mod_self]
      obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hma
      rw [ht, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    exact h1
  have hRHS : ((2 ^ w - 1 - (q + a * Δ) % 2 ^ w) + (q + a * Δ) % 2 ^ w) % 2 ^ w = (2 ^ w - 1) % 2 ^ w := by
    have hlt : (q + a * Δ) % 2 ^ w < 2 ^ w := Nat.mod_lt _ hpos
    congr 1; omega
  have hLHS : ((((2 ^ w - 1 - q) + ((2 ^ w - a) % 2 ^ w) * Δ) % 2 ^ w) + (q + a * Δ) % 2 ^ w) % 2 ^ w =
              (2 ^ w - 1) % 2 ^ w := by
    rw [Nat.add_mod (_ % 2 ^ w), Nat.mod_mod, ← Nat.add_mod]; exact hsum
  exact mod_add_cancel_right (by have := Nat.mod_lt (q + a * Δ) hpos; omega) (Nat.mod_lt _ hpos)
    (Nat.mod_lt _ hpos) (hRHS.trans hLHS.symm)

/-- Helper: `(a + M * b) % (M * M) = (a % M) + M * ((a / M + b) % M)` for `M > 0`. -/
theorem xor_lt_pow2 {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) : (a ^^^ b) < 2 ^ w := by
  have hm : (a ^^^ b) % 2 ^ w = (a ^^^ b) := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
    by_cases hi : i < w
    · simp [hi]
    · have h1 : a.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
      have h2 : b.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hi, h1, h2]
  rw [← hm]; exact Nat.mod_lt _ (pow2_pos w)

theorem and_lt_pow2 {w a b : Nat} (ha : a < 2 ^ w) : (a &&& b) < 2 ^ w := by
  have hm : (a &&& b) % 2 ^ w = (a &&& b) := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_and]
    by_cases hi : i < w
    · simp [hi]
    · have h1 : a.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hi, h1]
  rw [← hm]; exact Nat.mod_lt _ (pow2_pos w)

theorem or_lt_pow2 {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) : (a ||| b) < 2 ^ w := by
  have hm : (a ||| b) % 2 ^ w = (a ||| b) := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
    by_cases hi : i < w
    · simp [hi]
    · have h1 : a.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
      have h2 : b.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hi, h1, h2]
  rw [← hm]; exact Nat.mod_lt _ (pow2_pos w)

theorem mod_add_mod_pair (M a b c : Nat) :
    (a + (b % M + c % M)) % M = (a + (b + c)) % M := by
  rw [Nat.add_mod a, ← Nat.add_mod b c M, ← Nat.add_mod]

theorem mod_sq_block (M a b : Nat) (hM : 0 < M) :
    (a + M * b) % (M * M) = a % M + M * ((a / M + b) % M) := by
  have h1 : a + M * b = a % M + M * (a / M + b) := by
    rw [Nat.mul_add, ← Nat.add_assoc, Nat.mod_add_div]
  rw [h1]
  have h2 : a / M + b = (a / M + b) % M + M * ((a / M + b) / M) := (Nat.mod_add_div _ M).symm
  have h3 : a % M + M * (a / M + b) = (a % M + M * ((a / M + b) % M)) + (M * M) * ((a / M + b) / M) := by
    calc a % M + M * (a / M + b)
        = a % M + M * ((a / M + b) % M + M * ((a / M + b) / M)) := by rw [← h2]
      _ = a % M + (M * ((a / M + b) % M) + M * (M * ((a / M + b) / M))) := by rw [Nat.mul_add]
      _ = (a % M + M * ((a / M + b) % M)) + (M * M) * ((a / M + b) / M) := by
          rw [← Nat.add_assoc, ← Nat.mul_assoc]
  rw [h3, Nat.add_mul_mod_self_left]
  have hlt : a % M + M * ((a / M + b) % M) < M * M := by
    have hlt1 : a % M < M := Nat.mod_lt a hM
    have hlt2 : (a / M + b) % M < M := Nat.mod_lt _ hM
    have hle : M * ((a / M + b) % M + 1) ≤ M * M := Nat.mul_le_mul_left M hlt2
    rw [Nat.mul_add, Nat.mul_one] at hle
    omega
  exact Nat.mod_eq_of_lt hlt

/-- **Engine Theorem 4.1 (Soundness of Symbolic Affine Block-Jet Compiler `evalBlockJet`):** -/
theorem evalBlockJet_sound (w : Nat) (e : MBAExpr) (x : Nat) (J : BlockJet)
    (h : evalBlockJet w e x = some J) :
    IsAffineBlockJet (fun w' y => evalMod w' e y) w x J := by
  have hM : 0 < 2 ^ w := pow2_pos w
  induction e generalizing J with
  | var =>
    simp only [evalBlockJet, Option.some.injEq] at h; subst h
    refine ⟨Nat.mod_lt _ hM, hM, Nat.mod_lt _ hM, ?_⟩
    intro Δ hΔ
    simp only [evalMod, Nat.zero_add]
    have hlt : x % 2 ^ w + 2 ^ w * Δ < 2 ^ (2 * w) := block_lt (Nat.mod_lt _ hM) hΔ
    rw [Nat.mod_eq_of_lt hlt]
    congr 2
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.one_mul, Nat.mod_eq_of_lt hΔ]
  | const c =>
    simp only [evalBlockJet, Option.some.injEq] at h; subst h
    refine ⟨Nat.mod_lt _ hM, Nat.mod_lt _ hM, hM, ?_⟩
    intro Δ _
    simp only [evalMod, Nat.zero_mul, Nat.add_zero, Nat.mod_mod]
    rw [pow2_two_mul]
    have := mod_sq_block (2 ^ w) c 0 hM
    simpa only [Nat.mul_zero, Nat.add_zero] using this
  | add a b iha ihb =>
    simp only [evalBlockJet] at h
    cases ha : evalBlockJet w a x with
    | none => simp [ha] at h
    | some J1 =>
      cases hb : evalBlockJet w b x with
      | none => simp [ha, hb] at h
      | some J2 =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        obtain ⟨hr1, hq1, ha1, he1⟩ := iha J1 ha
        obtain ⟨hr2, hq2, ha2, he2⟩ := ihb J2 hb
        dsimp only at he1 he2
        refine ⟨Nat.mod_lt _ hM, Nat.mod_lt _ hM, Nat.mod_lt _ hM, ?_⟩
        intro Δ hΔ
        simp only [evalMod]
        rw [he1 Δ hΔ, he2 Δ hΔ, pow2_two_mul]
        have hsum : (J1.r + 2 ^ w * ((J1.q + J1.a * Δ) % 2 ^ w)) +
                    (J2.r + 2 ^ w * ((J2.q + J2.a * Δ) % 2 ^ w)) =
                    (J1.r + J2.r) + 2 ^ w * (((J1.q + J1.a * Δ) % 2 ^ w) + ((J2.q + J2.a * Δ) % 2 ^ w)) := by
          rw [Nat.mul_add]; omega
        rw [hsum, mod_sq_block (2 ^ w) _ _ hM]
        congr 2
        have hmod : ((J1.r + J2.r) / 2 ^ w +
                      ((J1.q + J1.a * Δ) % 2 ^ w + (J2.q + J2.a * Δ) % 2 ^ w)) % 2 ^ w =
                    ((J1.q + J2.q + (J1.r + J2.r) / 2 ^ w) % 2 ^ w +
                      (J1.a + J2.a) % 2 ^ w * Δ) % 2 ^ w := by
          have hL : ((J1.r + J2.r) / 2 ^ w +
                      ((J1.q + J1.a * Δ) % 2 ^ w + (J2.q + J2.a * Δ) % 2 ^ w)) % 2 ^ w =
                    ((J1.r + J2.r) / 2 ^ w + (J1.q + J1.a * Δ + (J2.q + J2.a * Δ))) % 2 ^ w :=
            mod_add_mod_pair (2 ^ w) _ _ _
          have hR : ((J1.q + J2.q + (J1.r + J2.r) / 2 ^ w) % 2 ^ w +
                      (J1.a + J2.a) % 2 ^ w * Δ) % 2 ^ w =
                    ((J1.q + J2.q + (J1.r + J2.r) / 2 ^ w) + (J1.a + J2.a) * Δ) % 2 ^ w := by
            rw [Nat.add_mod, Nat.mod_mod, Nat.mul_mod ((J1.a + J2.a) % _), Nat.mod_mod,
                ← Nat.mul_mod, ← Nat.add_mod]
          rw [hL, hR]
          congr 1
          rw [Nat.add_mul]; omega
        exact hmod
  | sub a b iha ihb =>
    simp only [evalBlockJet] at h
    cases ha : evalBlockJet w a x with
    | none => simp [ha] at h
    | some J1 =>
      cases hb : evalBlockJet w b x with
      | none => simp [ha, hb] at h
      | some J2 =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        obtain ⟨hr1, hq1, ha1, he1⟩ := iha J1 ha
        obtain ⟨hr2, hq2, ha2, he2⟩ := ihb J2 hb
        dsimp only at he1 he2
        refine ⟨Nat.mod_lt _ hM, Nat.mod_lt _ hM, Nat.mod_lt _ hM, ?_⟩
        intro Δ hΔ
        simp only [evalMod]
        rw [he1 Δ hΔ, he2 Δ hΔ]
        let v1 := (J1.q + J1.a * Δ) % 2 ^ w
        let v2 := (J2.q + J2.a * Δ) % 2 ^ w
        have hv1 : v1 < 2 ^ w := Nat.mod_lt _ hM
        have hv2 : v2 < 2 ^ w := Nat.mod_lt _ hM
        have hlt2 : J2.r + 2 ^ w * v2 < 2 ^ (2 * w) := block_lt hr2 hv2
        let borrow := if J1.r < J2.r then 2 ^ w - 1 else 0
        -- Show both sides agree by cancelling +(J2.r + 2^w * v2) mod 2^(2*w)!
        have hRHS_lt : (J1.r + (2 ^ w - J2.r)) % 2 ^ w +
            2 ^ w * (((J1.q + (2 ^ w - J2.q) + borrow) % 2 ^ w +
              (J1.a + (2 ^ w - J2.a)) % 2 ^ w * Δ) % 2 ^ w) < 2 ^ (2 * w) :=
          block_lt (Nat.mod_lt _ hM) (Nat.mod_lt _ hM)
        apply mod_add_cancel_right (Nat.mod_lt _ (pow2_pos _)) hRHS_lt hlt2
        -- LHS + (J2.r + 2^w * v2) ≡ J1.r + 2^w * v1 (mod 2^(2*w))
        have hLHS_add : (((J1.r + 2 ^ w * v1) + (2 ^ (2 * w) - (J2.r + 2 ^ w * v2))) % 2 ^ (2 * w) +
                         (J2.r + 2 ^ w * v2)) % 2 ^ (2 * w) =
                        (J1.r + 2 ^ w * v1) % 2 ^ (2 * w) := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have : (J1.r + 2 ^ w * v1) + (2 ^ (2 * w) - (J2.r + 2 ^ w * v2)) + (J2.r + 2 ^ w * v2) =
                 (J1.r + 2 ^ w * v1) + 2 ^ (2 * w) := by omega
          rw [this, Nat.add_mod_right]
        rw [hLHS_add, Nat.mod_eq_of_lt (block_lt hr1 hv1)]
        -- Compute RHS + (J2.r + 2^w * v2) mod 2^(2*w)
        rw [pow2_two_mul]
        let vout := ((J1.q + (2 ^ w - J2.q) + borrow) % 2 ^ w +
                      (J1.a + (2 ^ w - J2.a)) % 2 ^ w * Δ) % 2 ^ w
        have hcomb : ((J1.r + (2 ^ w - J2.r)) % 2 ^ w + 2 ^ w * vout) + (J2.r + 2 ^ w * v2) =
                     ((J1.r + (2 ^ w - J2.r)) % 2 ^ w + J2.r) + 2 ^ w * (vout + v2) := by
          rw [Nat.mul_add]; omega
        rw [hcomb, mod_sq_block (2 ^ w) _ _ hM]
        -- Check low part and carry
        have hlow : ((J1.r + (2 ^ w - J2.r)) % 2 ^ w + J2.r) % 2 ^ w = J1.r := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have : J1.r + (2 ^ w - J2.r) + J2.r = J1.r + 2 ^ w := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hr1]
        have hcarry : ((J1.r + (2 ^ w - J2.r)) % 2 ^ w + J2.r) / 2 ^ w =
                      if J1.r < J2.r then 1 else 0 := by
          by_cases hlt : J1.r < J2.r
          · simp only [hlt, ↓reduceIte]
            have h1 : (J1.r + (2 ^ w - J2.r)) % 2 ^ w = J1.r + (2 ^ w - J2.r) :=
              Nat.mod_eq_of_lt (by omega)
            rw [h1]
            have h2 : J1.r + (2 ^ w - J2.r) + J2.r = J1.r + 2 ^ w := by omega
            rw [h2, Nat.add_div_right _ hM, Nat.div_eq_of_lt hr1, Nat.zero_add]
          · simp only [hlt, ↓reduceIte]
            by_cases h0 : J2.r = 0
            · rw [h0]
              have : (J1.r + (2 ^ w - 0)) % 2 ^ w = J1.r := by
                rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hr1]
              rw [this, Nat.add_zero, Nat.div_eq_of_lt hr1]
            · have h1 : (J1.r + (2 ^ w - J2.r)) % 2 ^ w = J1.r - J2.r := by
                have hge : 2 ^ w ≤ J1.r + (2 ^ w - J2.r) := by omega
                rw [Nat.mod_eq_sub_mod hge]
                have : J1.r + (2 ^ w - J2.r) - 2 ^ w = J1.r - J2.r := by omega
                rw [this, Nat.mod_eq_of_lt (by omega)]
              rw [h1]
              have h2 : J1.r - J2.r + J2.r = J1.r := by omega
              rw [h2, Nat.div_eq_of_lt hr1]
        rw [hlow, hcarry]
        congr 2
        -- Show ((if J1.r < J2.r then 1 else 0) + (vout + v2)) % 2^w = v1
        have hsum_hi : ((if J1.r < J2.r then 1 else 0) + (vout + v2)) % 2 ^ w = v1 := by
          -- Unfold vout and v2 mod 2^w
          have h1 : ((if J1.r < J2.r then 1 else 0) + (vout + v2)) % 2 ^ w =
                    ((if J1.r < J2.r then 1 else 0) + borrow +
                      (J1.q + (2 ^ w - J2.q) + J2.q) +
                      ((J1.a + (2 ^ w - J2.a)) + J2.a) * Δ) % 2 ^ w := by
            have hvout_m : vout = ((J1.q + (2 ^ w - J2.q) + borrow) + (J1.a + (2 ^ w - J2.a)) * Δ) % 2 ^ w := by
              dsimp only [vout]
              rw [Nat.add_mod, Nat.mod_mod, Nat.mul_mod ((J1.a + _) % _), Nat.mod_mod,
                  ← Nat.mul_mod, ← Nat.add_mod]
            rw [hvout_m]
            dsimp only [v2]
            rw [mod_add_mod_pair]
            congr 1
            rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
            omega
          rw [h1]
          have hbor : ((if J1.r < J2.r then 1 else 0) + borrow) % 2 ^ w = 0 := by
            dsimp only [borrow]
            by_cases hlt : J1.r < J2.r
            · simp only [hlt, ↓reduceIte]
              have : 1 + (2 ^ w - 1) = 2 ^ w := by omega
              rw [this, Nat.mod_self]
            · simp [hlt]
          have hq_c : J1.q + (2 ^ w - J2.q) + J2.q = J1.q + 2 ^ w := by omega
          have ha_c : J1.a + (2 ^ w - J2.a) + J2.a = J1.a + 2 ^ w := by omega
          rw [hq_c, ha_c, Nat.add_mul]
          obtain ⟨kb, hkb⟩ := Nat.dvd_of_mod_eq_zero hbor
          have htot : (if J1.r < J2.r then 1 else 0) + borrow + (J1.q + 2 ^ w) + (J1.a * Δ + 2 ^ w * Δ) =
                      (J1.q + J1.a * Δ) + 2 ^ w * (kb + 1 + Δ) := by
            rw [hkb, Nat.mul_add, Nat.mul_add, Nat.mul_one]
            omega
          rw [htot, Nat.add_mul_mod_self_left]
        exact hsum_hi.symm
  | mul a b iha ihb =>
    simp only [evalBlockJet] at h
    cases ha : evalBlockJet w a x with
    | none => simp [ha] at h
    | some J1 =>
      cases hb : evalBlockJet w b x with
      | none => simp [ha, hb] at h
      | some J2 =>
        simp only [ha, hb, Option.some.injEq] at h; subst h
        obtain ⟨hr1, hq1, ha1, he1⟩ := iha J1 ha
        obtain ⟨hr2, hq2, ha2, he2⟩ := ihb J2 hb
        dsimp only at he1 he2
        refine ⟨Nat.mod_lt _ hM, Nat.mod_lt _ hM, Nat.mod_lt _ hM, ?_⟩
        intro Δ hΔ
        simp only [evalMod]
        rw [he1 Δ hΔ, he2 Δ hΔ, pow2_two_mul]
        let v1 := (J1.q + J1.a * Δ) % 2 ^ w
        let v2 := (J2.q + J2.a * Δ) % 2 ^ w
        have hmul_exp : (J1.r + 2 ^ w * v1) * (J2.r + 2 ^ w * v2) =
                        (J1.r * J2.r + 2 ^ w * (J1.r * v2 + J2.r * v1)) + (2 ^ w * 2 ^ w) * (v1 * v2) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add]
          have h1 : 2 ^ w * v1 * J2.r = 2 ^ w * (J2.r * v1) := by
            rw [Nat.mul_assoc, Nat.mul_comm v1 J2.r]
          have h2 : J1.r * (2 ^ w * v2) = 2 ^ w * (J1.r * v2) := by
            rw [Nat.mul_left_comm]
          have h3 : 2 ^ w * v1 * (2 ^ w * v2) = 2 ^ w * 2 ^ w * (v1 * v2) := by
            rw [Nat.mul_assoc, Nat.mul_left_comm v1 (2 ^ w), ← Nat.mul_assoc]
          rw [h1, h2, h3]; omega
        rw [hmul_exp, Nat.add_mul_mod_self_left, mod_sq_block (2 ^ w) _ _ hM]
        congr 2
        have hhi : (J1.r * J2.r / 2 ^ w + (J1.r * v2 + J2.r * v1)) % 2 ^ w =
                   ((J1.r * J2.r / 2 ^ w + J1.r * J2.q + J2.r * J1.q) % 2 ^ w +
                     (J1.r * J2.a + J2.r * J1.a) % 2 ^ w * Δ) % 2 ^ w := by
          have hL : (J1.r * J2.r / 2 ^ w + (J1.r * v2 + J2.r * v1)) % 2 ^ w =
                    (J1.r * J2.r / 2 ^ w + (J1.r * (J2.q + J2.a * Δ) + J2.r * (J1.q + J1.a * Δ))) % 2 ^ w := by
            dsimp only [v1, v2]
            have hm1 : (J1.r * ((J2.q + J2.a * Δ) % 2 ^ w)) % 2 ^ w = (J1.r * (J2.q + J2.a * Δ)) % 2 ^ w := by
              rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
            have hm2 : (J2.r * ((J1.q + J1.a * Δ) % 2 ^ w)) % 2 ^ w = (J2.r * (J1.q + J1.a * Δ)) % 2 ^ w := by
              rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
            rw [← mod_add_mod_pair, hm1, hm2, mod_add_mod_pair]
          have hR : ((J1.r * J2.r / 2 ^ w + J1.r * J2.q + J2.r * J1.q) % 2 ^ w +
                      (J1.r * J2.a + J2.r * J1.a) % 2 ^ w * Δ) % 2 ^ w =
                    ((J1.r * J2.r / 2 ^ w + J1.r * J2.q + J2.r * J1.q) +
                      (J1.r * J2.a + J2.r * J1.a) * Δ) % 2 ^ w := by
            rw [Nat.add_mod, Nat.mod_mod, Nat.mul_mod ((_ + _) % _), Nat.mod_mod,
                ← Nat.mul_mod, ← Nat.add_mod]
          rw [hL, hR]
          congr 1
          rw [Nat.mul_add, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
          omega
        exact hhi
  | shl a k iha =>
    simp only [evalBlockJet] at h
    cases ha : evalBlockJet w a x with
    | none => simp [ha] at h
    | some J1 =>
      simp only [ha, Option.some.injEq] at h; subst h
      obtain ⟨hr1, hq1, ha1, he1⟩ := iha J1 ha
      dsimp only at he1
      refine ⟨Nat.mod_lt _ hM, Nat.mod_lt _ hM, Nat.mod_lt _ hM, ?_⟩
      intro Δ hΔ
      simp only [evalMod]
      rw [he1 Δ hΔ, pow2_two_mul]
      have hmul : (J1.r + 2 ^ w * ((J1.q + J1.a * Δ) % 2 ^ w)) * 2 ^ k =
                  J1.r * 2 ^ k + 2 ^ w * (((J1.q + J1.a * Δ) % 2 ^ w) * 2 ^ k) := by
        rw [Nat.add_mul, Nat.mul_assoc]
      rw [hmul, mod_sq_block (2 ^ w) _ _ hM]
      congr 2
      have hL : (J1.r * 2 ^ k / 2 ^ w + (J1.q + J1.a * Δ) % 2 ^ w * 2 ^ k) % 2 ^ w =
                (J1.r * 2 ^ k / 2 ^ w + (J1.q + J1.a * Δ) * 2 ^ k) % 2 ^ w := by
        rw [Nat.add_mod, Nat.mul_mod ((_ + _) % _), Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      have hR : ((J1.r * 2 ^ k / 2 ^ w + J1.q * 2 ^ k) % 2 ^ w + J1.a * 2 ^ k % 2 ^ w * Δ) % 2 ^ w =
                ((J1.r * 2 ^ k / 2 ^ w + J1.q * 2 ^ k) + (J1.a * 2 ^ k) * Δ) % 2 ^ w := by
        rw [Nat.add_mod, Nat.mod_mod, Nat.mul_mod ((J1.a * 2 ^ k) % _), Nat.mod_mod,
            ← Nat.mul_mod, ← Nat.add_mod]
      rw [hL, hR]
      congr 1
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm Δ (2 ^ k), ← Nat.mul_assoc]
      omega
  | bnot a iha =>
    simp only [evalBlockJet] at h
    cases ha : evalBlockJet w a x with
    | none => simp [ha] at h
    | some J1 =>
      simp only [ha, Option.some.injEq] at h; subst h
      obtain ⟨hr1, hq1, ha1, he1⟩ := iha J1 ha
      dsimp only at he1
      refine ⟨by dsimp; omega, by dsimp; omega, Nat.mod_lt _ hM, ?_⟩
      intro Δ hΔ
      simp only [evalMod]
      rw [he1 Δ hΔ, pow2_two_mul]
      have hsplit : 2 ^ w * 2 ^ w - 1 - (J1.r + 2 ^ w * ((J1.q + J1.a * Δ) % 2 ^ w)) =
                    (2 ^ w - 1 - J1.r) + 2 ^ w * (2 ^ w - 1 - (J1.q + J1.a * Δ) % 2 ^ w) := by
        have hv : (J1.q + J1.a * Δ) % 2 ^ w < 2 ^ w := Nat.mod_lt _ hM
        have h1 : 2 ^ w * (2 ^ w - 1 - (J1.q + J1.a * Δ) % 2 ^ w) + 2 ^ w * ((J1.q + J1.a * Δ) % 2 ^ w) + 2 ^ w =
                  2 ^ w * 2 ^ w := by
          rw [← Nat.mul_add]
          have : 2 ^ w - 1 - (J1.q + J1.a * Δ) % 2 ^ w + (J1.q + J1.a * Δ) % 2 ^ w = 2 ^ w - 1 := by omega
          rw [this]
          have : 2 ^ w * (2 ^ w - 1) + 2 ^ w = 2 ^ w * ((2 ^ w - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
          rw [this, Nat.sub_add_cancel hM]
        omega
      rw [hsplit, bnot_affine_mod hq1 ha1]
  | bxor a b iha ihb =>
    simp only [evalBlockJet] at h
    cases ha : evalBlockJet w a x with
    | none => simp [ha] at h
    | some J1 =>
      cases hb : evalBlockJet w b x with
      | none => simp [ha, hb] at h
      | some J2 =>
        simp only [ha, hb] at h
        obtain ⟨hr1, hq1, ha1, he1⟩ := iha J1 ha
        obtain ⟨hr2, hq2, ha2, he2⟩ := ihb J2 hb
        dsimp only at he1 he2
        have hblk : ∀ Δ < 2 ^ w,
            evalMod (2 * w) (.bxor a b) (x % 2 ^ w + 2 ^ w * Δ) =
            (J1.r ^^^ J2.r) % 2 ^ w +
              2 ^ w * (((J1.q + J1.a * Δ) % 2 ^ w) ^^^ ((J2.q + J2.a * Δ) % 2 ^ w)) := by
          intro Δ hΔ
          simp only [evalMod]
          rw [he1 Δ hΔ, he2 Δ hΔ, xor_split_block hr1 hr2]
          have hxr_lt := xor_lt_pow2 hr1 hr2
          have hxv_lt := xor_lt_pow2 (Nat.mod_lt (J1.q + J1.a * Δ) hM) (Nat.mod_lt (J2.q + J2.a * Δ) hM)
          rw [Nat.mod_eq_of_lt (block_lt hxr_lt hxv_lt), Nat.mod_eq_of_lt hxr_lt]
        split at h
        · rename_i hc; simp only [Option.some.injEq] at h; subst h
          have ⟨h2q, h2a⟩ : J2.q = 0 ∧ J2.a = 0 := by simpa using hc
          refine ⟨Nat.mod_lt _ hM, hq1, ha1, fun Δ hΔ => ?_⟩
          dsimp only; rw [hblk Δ hΔ, h2q, h2a]; simp
        · split at h
          · rename_i _ hc; simp only [Option.some.injEq] at h; subst h
            have ⟨h1q, h1a⟩ : J1.q = 0 ∧ J1.a = 0 := by simpa using hc
            refine ⟨Nat.mod_lt _ hM, hq2, ha2, fun Δ hΔ => ?_⟩
            dsimp only; rw [hblk Δ hΔ, h1q, h1a]; simp
          · split at h
            · rename_i _ _ hc; simp only [Option.some.injEq] at h; subst h
              have ⟨h2q, h2a⟩ : J2.q = 2 ^ w - 1 ∧ J2.a = 0 := by simpa using hc
              refine ⟨Nat.mod_lt _ hM, by dsimp; omega, Nat.mod_lt _ hM, fun Δ hΔ => ?_⟩
              dsimp only; rw [hblk Δ hΔ, h2q, h2a, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ w)]
              rw [xor_all_ones (Nat.mod_lt _ hM), bnot_affine_mod hq1 ha1]
            · split at h
              · rename_i _ _ _ hc; simp only [Option.some.injEq] at h; subst h
                have ⟨h1q, h1a⟩ : J1.q = 2 ^ w - 1 ∧ J1.a = 0 := by simpa using hc
                refine ⟨Nat.mod_lt _ hM, by dsimp; omega, Nat.mod_lt _ hM, fun Δ hΔ => ?_⟩
                dsimp only; rw [hblk Δ hΔ, h1q, h1a, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ w)]
                rw [nat_xor_comm (2 ^ w - 1), xor_all_ones (Nat.mod_lt _ hM), bnot_affine_mod hq2 ha2]
              · split at h
                · rename_i _ _ _ _ hc; simp only [Option.some.injEq] at h; subst h
                  have ⟨hqeq, haeq⟩ : J1.q = J2.q ∧ J1.a = J2.a := by simpa using hc
                  refine ⟨Nat.mod_lt _ hM, hM, hM, fun Δ hΔ => ?_⟩
                  dsimp only; rw [hblk Δ hΔ, hqeq, haeq, nat_xor_self]; simp
                · simp at h
  | band a b iha ihb =>
    simp only [evalBlockJet] at h
    cases ha : evalBlockJet w a x with
    | none => simp [ha] at h
    | some J1 =>
      cases hb : evalBlockJet w b x with
      | none => simp [ha, hb] at h
      | some J2 =>
        simp only [ha, hb] at h
        obtain ⟨hr1, hq1, ha1, he1⟩ := iha J1 ha
        obtain ⟨hr2, hq2, ha2, he2⟩ := ihb J2 hb
        dsimp only at he1 he2
        have hblk : ∀ Δ < 2 ^ w,
            evalMod (2 * w) (.band a b) (x % 2 ^ w + 2 ^ w * Δ) =
            (J1.r &&& J2.r) % 2 ^ w +
              2 ^ w * (((J1.q + J1.a * Δ) % 2 ^ w) &&& ((J2.q + J2.a * Δ) % 2 ^ w)) := by
          intro Δ hΔ
          simp only [evalMod]
          rw [he1 Δ hΔ, he2 Δ hΔ, and_split_block hr1 hr2]
          have hxr_lt := and_lt_pow2 (b := J2.r) hr1
          have hxv_lt := and_lt_pow2 (b := (J2.q + J2.a * Δ) % 2 ^ w) (Nat.mod_lt (J1.q + J1.a * Δ) hM)
          rw [Nat.mod_eq_of_lt (block_lt hxr_lt hxv_lt), Nat.mod_eq_of_lt hxr_lt]
        split at h
        · rename_i hc; simp only [Option.some.injEq] at h; subst h
          have ⟨h2q, h2a⟩ : J2.q = 0 ∧ J2.a = 0 := by simpa using hc
          refine ⟨Nat.mod_lt _ hM, hM, hM, fun Δ hΔ => ?_⟩
          dsimp only; rw [hblk Δ hΔ, h2q, h2a]; simp
        · split at h
          · rename_i _ hc; simp only [Option.some.injEq] at h; subst h
            have ⟨h1q, h1a⟩ : J1.q = 0 ∧ J1.a = 0 := by simpa using hc
            refine ⟨Nat.mod_lt _ hM, hM, hM, fun Δ hΔ => ?_⟩
            dsimp only; rw [hblk Δ hΔ, h1q, h1a]; simp
          · split at h
            · rename_i _ _ hc; simp only [Option.some.injEq] at h; subst h
              have ⟨h2q, h2a⟩ : J2.q = 2 ^ w - 1 ∧ J2.a = 0 := by simpa using hc
              refine ⟨Nat.mod_lt _ hM, hq1, ha1, fun Δ hΔ => ?_⟩
              dsimp only; rw [hblk Δ hΔ, h2q, h2a, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ w)]
              rw [and_all_ones (Nat.mod_lt _ hM)]
            · split at h
              · rename_i _ _ _ hc; simp only [Option.some.injEq] at h; subst h
                have ⟨h1q, h1a⟩ : J1.q = 2 ^ w - 1 ∧ J1.a = 0 := by simpa using hc
                refine ⟨Nat.mod_lt _ hM, hq2, ha2, fun Δ hΔ => ?_⟩
                dsimp only; rw [hblk Δ hΔ, h1q, h1a, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ w)]
                rw [nat_and_comm (2 ^ w - 1), and_all_ones (Nat.mod_lt _ hM)]
              · split at h
                · rename_i _ _ _ _ hc; simp only [Option.some.injEq] at h; subst h
                  have ⟨hqeq, haeq⟩ : J1.q = J2.q ∧ J1.a = J2.a := by simpa using hc
                  refine ⟨Nat.mod_lt _ hM, hq1, ha1, fun Δ hΔ => ?_⟩
                  dsimp only; rw [hblk Δ hΔ, hqeq, haeq, nat_and_self]
                · simp at h
  | bor a b iha ihb =>
    simp only [evalBlockJet] at h
    cases ha : evalBlockJet w a x with
    | none => simp [ha] at h
    | some J1 =>
      cases hb : evalBlockJet w b x with
      | none => simp [ha, hb] at h
      | some J2 =>
        simp only [ha, hb] at h
        obtain ⟨hr1, hq1, ha1, he1⟩ := iha J1 ha
        obtain ⟨hr2, hq2, ha2, he2⟩ := ihb J2 hb
        dsimp only at he1 he2
        have hblk : ∀ Δ < 2 ^ w,
            evalMod (2 * w) (.bor a b) (x % 2 ^ w + 2 ^ w * Δ) =
            (J1.r ||| J2.r) % 2 ^ w +
              2 ^ w * (((J1.q + J1.a * Δ) % 2 ^ w) ||| ((J2.q + J2.a * Δ) % 2 ^ w)) := by
          intro Δ hΔ
          simp only [evalMod]
          rw [he1 Δ hΔ, he2 Δ hΔ, or_split_block hr1 hr2]
          have hxr_lt := or_lt_pow2 hr1 hr2
          have hxv_lt := or_lt_pow2 (Nat.mod_lt (J1.q + J1.a * Δ) hM) (Nat.mod_lt (J2.q + J2.a * Δ) hM)
          rw [Nat.mod_eq_of_lt (block_lt hxr_lt hxv_lt), Nat.mod_eq_of_lt hxr_lt]
        split at h
        · rename_i hc; simp only [Option.some.injEq] at h; subst h
          have ⟨h2q, h2a⟩ : J2.q = 0 ∧ J2.a = 0 := by simpa using hc
          refine ⟨Nat.mod_lt _ hM, hq1, ha1, fun Δ hΔ => ?_⟩
          dsimp only; rw [hblk Δ hΔ, h2q, h2a]; simp
        · split at h
          · rename_i _ hc; simp only [Option.some.injEq] at h; subst h
            have ⟨h1q, h1a⟩ : J1.q = 0 ∧ J1.a = 0 := by simpa using hc
            refine ⟨Nat.mod_lt _ hM, hq2, ha2, fun Δ hΔ => ?_⟩
            dsimp only; rw [hblk Δ hΔ, h1q, h1a]; simp
          · split at h
            · rename_i _ _ hc; simp only [Option.some.injEq] at h; subst h
              have ⟨h2q, h2a⟩ : J2.q = 2 ^ w - 1 ∧ J2.a = 0 := by simpa using hc
              refine ⟨Nat.mod_lt _ hM, by dsimp; omega, hM, fun Δ hΔ => ?_⟩
              dsimp only; rw [hblk Δ hΔ, h2q, h2a, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ w)]
              rw [or_all_ones (Nat.mod_lt _ hM)]
            · split at h
              · rename_i _ _ _ hc; simp only [Option.some.injEq] at h; subst h
                have ⟨h1q, h1a⟩ : J1.q = 2 ^ w - 1 ∧ J1.a = 0 := by simpa using hc
                refine ⟨Nat.mod_lt _ hM, by dsimp; omega, hM, fun Δ hΔ => ?_⟩
                dsimp only; rw [hblk Δ hΔ, h1q, h1a, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ w)]
                rw [nat_or_comm (2 ^ w - 1), or_all_ones (Nat.mod_lt _ hM)]
              · split at h
                · rename_i _ _ _ _ hc; simp only [Option.some.injEq] at h; subst h
                  have ⟨hqeq, haeq⟩ : J1.q = J2.q ∧ J1.a = J2.a := by simpa using hc
                  refine ⟨Nat.mod_lt _ hM, hq1, ha1, fun Δ hΔ => ?_⟩
                  dsimp only; rw [hblk Δ hΔ, hqeq, haeq, nat_or_self]
                · simp at h

/-- **Engine Theorem 4.2 (Single-Step Exact Quadratic Lifting & Uniqueness `w → 2*w`):** -/
theorem quadLiftFromJet_sound {F : Nat → Nat → Nat} {w x : Nat} {J : BlockJet}
    (hw : 1 ≤ w) (hjet : IsAffineBlockJet F w x J) (hr0 : J.r = 0) (hodd : J.a % 2 = 1) :
    let x' := quadLiftFromJet w x J
    x' < 2 ^ (2 * w) ∧
    x' % 2 ^ w = x % 2 ^ w ∧
    F (2 * w) x' = 0 ∧
    (∀ y < 2 ^ (2 * w), y % 2 ^ w = x % 2 ^ w → F (2 * w) y = 0 → y = x') := by
  have hM : 0 < 2 ^ w := pow2_pos w
  have hM1 : 1 < 2 ^ w := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw
    omega
  obtain ⟨hr, hq, ha, hspec⟩ := hjet
  let inv := modInvPow2 J.a w
  let Δ := ((2 ^ w - J.q) * inv) % 2 ^ w
  have hΔ : Δ < 2 ^ w := Nat.mod_lt _ hM
  have hinv : (J.a * inv) % 2 ^ w = 1 := by
    rw [modInvPow2_spec hodd w, Nat.mod_eq_of_lt hM1]
  have hzero : (J.q + J.a * Δ) % 2 ^ w = 0 := by
    have h1 : (J.q + J.a * Δ) % 2 ^ w = (J.q + (J.a * inv) * (2 ^ w - J.q)) % 2 ^ w := by
      dsimp only [Δ]
      rw [Nat.add_mod, Nat.mul_mod J.a, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      congr 2
      rw [Nat.mul_left_comm, Nat.mul_comm]
    rw [h1, Nat.add_mod, Nat.mul_mod (J.a * inv), hinv, Nat.one_mul, Nat.mod_mod, ← Nat.add_mod]
    have : J.q + (2 ^ w - J.q) = 2 ^ w := by omega
    rw [this, Nat.mod_self]
  refine ⟨block_lt (Nat.mod_lt _ hM) hΔ, ?_, ?_, ?_⟩
  · -- Congruence mod 2^w
    simp only [quadLiftFromJet]
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  · -- Exact root mod 2^(2*w)
    change F (2 * w) (x % 2 ^ w + 2 ^ w * Δ) = 0
    rw [hspec Δ hΔ, hr0, hzero]; simp
  · -- Uniqueness among all lifts y < 2^(2*w)
    intro y hy hmod hFy
    have hy_split : y = x % 2 ^ w + 2 ^ w * (y / 2 ^ w) := by
      rw [← hmod, Nat.mod_add_div]
    have hdiv_lt : y / 2 ^ w < 2 ^ w := by
      rw [pow2_two_mul] at hy
      exact Nat.div_lt_of_lt_mul hy
    have hEq := hspec (y / 2 ^ w) hdiv_lt
    rw [← hy_split, hFy, hr0, Nat.zero_add] at hEq
    have hq_zero : (J.q + J.a * (y / 2 ^ w)) % 2 ^ w = 0 := by
      by_cases hz : (J.q + J.a * (y / 2 ^ w)) % 2 ^ w = 0
      · exact hz
      · have hpos : 0 < 2 ^ w * ((J.q + J.a * (y / 2 ^ w)) % 2 ^ w) :=
          Nat.mul_pos hM (Nat.pos_of_ne_zero hz)
        omega
    -- Multiply (J.q + J.a * (y / 2^w)) ≡ 0 by inv to recover y / 2^w = Δ!
    have hdiv_eq : y / 2 ^ w = Δ := by
      have hmul0 : ((J.q + J.a * (y / 2 ^ w)) * inv) % 2 ^ w = 0 := by
        rw [Nat.mul_mod, hq_zero, Nat.zero_mul, Nat.zero_mod]
      have hadd0 : ((J.q * inv) % 2 ^ w + y / 2 ^ w) % 2 ^ w = 0 := by
        have hstep : ((J.q + J.a * (y / 2 ^ w)) * inv) % 2 ^ w =
                     ((J.q * inv) % 2 ^ w + y / 2 ^ w) % 2 ^ w := by
          rw [Nat.add_mul, Nat.add_mod (J.q * inv), Nat.mul_assoc, Nat.mul_comm (y / 2 ^ w) inv,
              ← Nat.mul_assoc, Nat.mul_mod (J.a * inv), hinv, Nat.one_mul, Nat.mod_mod,
              Nat.mod_eq_of_lt hdiv_lt]
        rw [← hstep, hmul0]
      have hΔ_add : ((J.q * inv) % 2 ^ w + Δ) % 2 ^ w = 0 := by
        have hstep : ((J.q + (2 ^ w - J.q)) * inv) % 2 ^ w =
                     ((J.q * inv) % 2 ^ w + Δ) % 2 ^ w := by
          dsimp only [Δ]
          rw [Nat.add_mul, Nat.add_mod]
        have : J.q + (2 ^ w - J.q) = 2 ^ w := by omega
        rw [← hstep, this, Nat.mul_mod_right]
      have hcomm1 : (y / 2 ^ w + (J.q * inv) % 2 ^ w) % 2 ^ w = (Δ + (J.q * inv) % 2 ^ w) % 2 ^ w := by
        rw [Nat.add_comm (y / 2 ^ w), Nat.add_comm Δ, hadd0, hΔ_add]
      exact mod_add_cancel_right hdiv_lt hΔ (Nat.mod_lt _ hM) hcomm1
    rw [hy_split, hdiv_eq]; rfl

/-- **Engine Theorem 4.3 (Infinite Quadratic Doubling Tower `w0 → 2^k * w0`, `∀ k : Nat`):**
Whenever an invariant `Inv w x` (e.g. `x % 2^s = r`) is preserved mod `2^w` and guarantees
`evalBlockJet w e x` succeeds with odd slope for all `w ≥ w0`, `mbaQuadLift` constructs exact
double-precision roots `evalMod (w0 * 2^k) e (mbaQuadLift e w0 x0 k) = 0` for ALL `k : Nat`! -/
theorem mbaQuadLift_sound {e : MBAExpr} {w0 x0 : Nat} {Inv : Nat → Nat → Prop}
    (hw0 : 1 ≤ w0)
    (hInv0 : Inv w0 (x0 % 2 ^ w0))
    (hRoot0 : evalMod w0 e (x0 % 2 ^ w0) = 0)
    (hInvStep : ∀ w x y, w0 ≤ w → Inv w x → y % 2 ^ w = x % 2 ^ w → Inv (2 * w) y)
    (hJetOk : ∀ w x, w0 ≤ w → Inv w x → ∃ J, evalBlockJet w e x = some J ∧ J.a % 2 = 1) :
    ∀ k : Nat,
      let wk := w0 * 2 ^ k
      let xk := mbaQuadLift e w0 x0 k
      xk < 2 ^ wk ∧ Inv wk xk ∧ evalMod wk e xk = 0 ∧
      mbaQuadLift e w0 x0 (k + 1) % 2 ^ wk = xk := by
  have hbase : ∀ k : Nat,
      let wk := w0 * 2 ^ k
      let xk := mbaQuadLift e w0 x0 k
      xk < 2 ^ wk ∧ Inv wk xk ∧ evalMod wk e xk = 0 := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.pow_zero, Nat.mul_one, mbaQuadLift]
      exact ⟨Nat.mod_lt _ (pow2_pos w0), hInv0, hRoot0⟩
    | succ k ih =>
      obtain ⟨hlt, hinv, hroot⟩ := ih
      let wk := w0 * 2 ^ k
      let xk := mbaQuadLift e w0 x0 k
      have hwk_ge : w0 ≤ wk := Nat.le_mul_of_pos_right w0 (pow2_pos k)
      have hwk1 : 1 ≤ wk := Nat.le_trans hw0 hwk_ge
      obtain ⟨J, hJeq, hJodd⟩ := hJetOk wk xk hwk_ge hinv
      have hJsound := evalBlockJet_sound wk e xk J hJeq
      have hJr0 : J.r = 0 := by
        have h0 := hJsound.2.2.2 0 (pow2_pos wk)
        simp only [Nat.mul_zero, Nat.add_zero] at h0
        have hcoh := (evalMod_coherent e).2 wk (2 * wk) (xk % 2 ^ wk) xk
          (by omega) (Nat.mod_mod _ _)
        dsimp only at hcoh
        rw [hroot, h0, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hJsound.1] at hcoh
        exact hcoh
      have hstep := quadLiftFromJet_sound hwk1 hJsound hJr0 hJodd
      have hpow_eq : w0 * 2 ^ (k + 1) = 2 * wk := by
        dsimp only [wk]
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (w0 * 2 ^ k) 2]
      have hx_next : mbaQuadLift e w0 x0 (k + 1) = quadLiftFromJet wk xk J := by
        change mbaQuadStep e wk xk = quadLiftFromJet wk xk J
        simp only [mbaQuadStep, hJeq]
      rw [hpow_eq, hx_next]
      exact ⟨hstep.1, hInvStep wk xk _ hwk_ge hinv hstep.2.1, hstep.2.2.1⟩
  intro k
  obtain ⟨hlt, hinv, hroot⟩ := hbase k
  let wk := w0 * 2 ^ k
  let xk := mbaQuadLift e w0 x0 k
  have hwk_ge : w0 ≤ wk := Nat.le_mul_of_pos_right w0 (pow2_pos k)
  obtain ⟨J, hJeq, hJodd⟩ := hJetOk wk xk hwk_ge hinv
  have hJsound := evalBlockJet_sound wk e xk J hJeq
  have hJr0 : J.r = 0 := by
    have h0 := hJsound.2.2.2 0 (pow2_pos wk)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    have hcoh := (evalMod_coherent e).2 wk (2 * wk) (xk % 2 ^ wk) xk
      (by omega) (Nat.mod_mod _ _)
    dsimp only at hcoh
    rw [hroot, h0, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hJsound.1] at hcoh
    exact hcoh
  have hstep := quadLiftFromJet_sound (Nat.le_trans hw0 hwk_ge) hJsound hJr0 hJodd
  have hx_next : mbaQuadLift e w0 x0 (k + 1) = quadLiftFromJet wk xk J := by
    change mbaQuadStep e wk xk = quadLiftFromJet wk xk J
    simp only [mbaQuadStep, hJeq]
  refine ⟨hlt, hinv, hroot, ?_⟩
  rw [hx_next, hstep.2.1, Nat.mod_eq_of_lt hlt]

/-! ## Section 5: Four Sharp Infinite Theorems, Non-Vacuity Witnesses & Sharpness Counterexamples -/

/-! ### Theorem 1: 4-Parameter Odd-Mask XOR-Product & Bitwise-AND 0-or-2 Dichotomy -/

theorem fam1_symDeriv0 (a b c d r : Nat) (hr : r < 2) :
    symDeriv0 1 1 r (fam1 a b c d) = some true := by
  have hodd : (2 * a + 1) % 2 = 1 := by omega
  have hr_cases : r = 0 ∨ r = 1 := by omega
  rcases hr_cases with rfl | rfl <;> simp [fam1, symDeriv0, evalMod, hodd]

/-- **Main Theorem 1 (4-Parameter Odd-Mask XOR-Product & Bitwise-AND Dichotomy):**
For ALL `a b c d : Nat` and ALL `w ≥ 1`, `fam1 a b c d (x) ≡ 0 (mod 2^w)` has
EXACTLY `2` roots if `d` is even, and `0` roots if `d` is odd! -/
theorem thm1_odd_xor_product_rootCount (a b c d : Nat) {w : Nat} (hw : 1 ≤ w) :
    rootCount (fun w' x => evalMod w' (fam1 a b c d) x) w = if d % 2 = 0 then 2 else 0 := by
  have hinv : rootCount (fun w' x => evalMod w' (fam1 a b c d) x) w =
              rootCount (fun w' x => evalMod w' (fam1 a b c d) x) 1 := by
    apply rootCount_partition_invariant (evalMod_coherent (fam1 a b c d)) (Nat.le_refl 1) _ hw
    intro r hr
    right
    exact ⟨0, hasExactDeriv0_to_order0 (Nat.le_refl 1) (symDeriv0_sound (fam1_symDeriv0 a b c d r hr))⟩
  rw [hinv]
  have hodd : (2 * a + 1) % 2 = 1 := by omega
  have hd : d % 2 = 0 ∨ d % 2 = 1 := by omega
  rcases hd with h0 | h1
  · simp [rootCount, countBelow, fam1, evalMod, hodd, h0]
  · simp [rootCount, countBelow, fam1, evalMod, hodd, h1]

/-- **Main Theorem 1b (Constructive Infinite Bit-by-Bit Lifts of Both 2-Adic Roots):** -/
theorem thm1_constructive_lifts (a b c d : Nat) (hd : d % 2 = 0) :
    ∀ k : Nat,
      let F := fun w' x => evalMod w' (fam1 a b c d) x
      let y0 := liftCore F 0 1 0 k
      let y1 := liftCore F 0 1 1 k
      y0 < 2 ^ (1 + k) ∧ y1 < 2 ^ (1 + k) ∧
      F (1 + k) y0 = 0 ∧ F (1 + k) y1 = 0 ∧ y0 ≠ y1 := by
  have hodd : (2 * a + 1) % 2 = 1 := by omega
  have hsens0 : HasOrderVSensitivity (fun w' x => evalMod w' (fam1 a b c d) x) 1 0 1 0 :=
    hasExactDeriv0_to_order0 (Nat.le_refl 1) (symDeriv0_sound (fam1_symDeriv0 a b c d 0 (by decide)))
  have hsens1 : HasOrderVSensitivity (fun w' x => evalMod w' (fam1 a b c d) x) 1 1 1 0 :=
    hasExactDeriv0_to_order0 (Nat.le_refl 1) (symDeriv0_sound (fam1_symDeriv0 a b c d 1 (by decide)))
  have hr0 : evalMod 1 (fam1 a b c d) 0 = 0 := by simp [fam1, evalMod, hodd, hd]
  have hr1 : evalMod 1 (fam1 a b c d) 1 = 0 := by simp [fam1, evalMod, hodd, hd]
  have hL0 := liftCore_spec (evalMod_coherent (fam1 a b c d)) hsens0 (by decide) (by decide) hr0
  have hL1 := liftCore_spec (evalMod_coherent (fam1 a b c d)) hsens1 (by decide) (by decide) hr1
  intro k
  obtain ⟨hlt0, hc0, hrt0, _, _⟩ := hL0 k
  obtain ⟨hlt1, hc1, hrt1, _, _⟩ := hL1 k
  refine ⟨by simpa using hlt0, by simpa using hlt1, hrt0, hrt1, ?_⟩
  intro heq
  rw [heq] at hc0
  omega

-- Non-vacuity witnesses for Theorem 1 (both branches inhabited)
example : rootCount (fun w x => evalMod w (fam1 2 3 5 6) x) 4 = 2 := by
  exact thm1_odd_xor_product_rootCount 2 3 5 6 (by decide)

example : rootCount (fun w x => evalMod w (fam1 2 3 5 7) x) 4 = 0 := by
  exact thm1_odd_xor_product_rootCount 2 3 5 7 (by decide)

-- Sharpness Counterexample 1a: Even XOR mask `2*a = 0` (`x * (x ^ 0) - 4`) breaks rootCount=2 → hits 8 at w=5!
theorem sharpness1_even_mask :
    rootCount (fun w x => evalMod w fam1SharpEvenMask x) 5 = 8 := by decide

-- Sharpness Counterexample 1b: Removing the factor-2 shield on variable-variable `&`
-- (`x * (x ^ 1) + (x & (x + 1)) - 2`) breaks rootCount=2 → drops to 1 at w=2!
theorem sharpness1_unshielded_and :
    rootCount (fun w x => evalMod w fam1SharpUnshieldedAnd x) 1 = 2 ∧
    rootCount (fun w x => evalMod w fam1SharpUnshieldedAnd x) 2 = 1 := by decide


/-! ### Theorem 2: Universal 1-or-5 Non-Uniform Ramification Dichotomy (`∀ H : MBAExpr, ∀ w ≥ 3`) -/

theorem fam2_even_sens (H : MBAExpr) :
    HasOrderVSensitivity (fun w x => evalMod w (fam2 H) x) 1 0 3 0 := by
  apply hasExactDeriv0_to_order0 (by decide)
  apply symDeriv0_sound
  simp [fam2, symDeriv0, evalMod]

theorem evalMod_cubic_eq_nat {w x : Nat} (hw : 1 ≤ w) (hx : 1 ≤ x) :
    evalMod w (.mul .var (.sub (.mul .var .var) (.const 1))) x = (x * (x * x - 1)) % 2 ^ w := by
  have hM1 : 1 < 2 ^ w := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw; omega
  have h1mod : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt hM1
  simp only [evalMod, h1mod]
  have hxx : 1 ≤ x * x := Nat.mul_pos hx hx
  have hsub_mod : ((x % 2 ^ w * (x % 2 ^ w)) % 2 ^ w + (2 ^ w - 1)) % 2 ^ w = (x * x - 1) % 2 ^ w := by
    rw [← Nat.mul_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hcalc : x * x + (2 ^ w - 1) = (x * x - 1) + 2 ^ w := by omega
    rw [hcalc, Nat.add_mod_right]
  rw [hsub_mod, ← Nat.mul_mod]

theorem evalMod_shl2_shift_v1 (H : MBAExpr) {w x : Nat} (hw : 3 ≤ w) :
    evalMod (w + 1) (.shl H 2) (x + 2 ^ (w - 1)) = evalMod (w + 1) (.shl H 2) x := by
  simp only [evalMod]
  have hcoh : evalMod (w + 1) H (x + 2 ^ (w - 1)) % 2 ^ (w - 1) =
              evalMod (w + 1) H x % 2 ^ (w - 1) := by
    have h1 := (evalMod_coherent H).2 (w - 1) (w + 1) (x + 2 ^ (w - 1)) x (by omega)
      (Nat.add_mod_right x (2 ^ (w - 1)))
    have h2 := (evalMod_coherent H).2 (w - 1) (w + 1) x x (by omega) rfl
    exact h1.trans h2.symm
  have hpow : 2 ^ (w + 1) = 2 ^ (w - 1) * 2 ^ 2 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hlift : ∀ u v : Nat, u % 2 ^ (w - 1) = v % 2 ^ (w - 1) →
      (u * 2 ^ 2) % 2 ^ (w + 1) = (v * 2 ^ 2) % 2 ^ (w + 1) := by
    intro u v huv
    have hu : u = u % 2 ^ (w - 1) + 2 ^ (w - 1) * (u / 2 ^ (w - 1)) := (Nat.mod_add_div u _).symm
    have hv : v = v % 2 ^ (w - 1) + 2 ^ (w - 1) * (v / 2 ^ (w - 1)) := (Nat.mod_add_div v _).symm
    have hmul : ∀ t q : Nat, ((t + 2 ^ (w - 1) * q) * 2 ^ 2) % 2 ^ (w + 1) = (t * 2 ^ 2) % 2 ^ (w + 1) := by
      intro t q
      rw [Nat.add_mul, hpow]
      have hcomm : 2 ^ (w - 1) * q * 2 ^ 2 = (2 ^ (w - 1) * 2 ^ 2) * q := by
        rw [Nat.mul_assoc, Nat.mul_comm q (2 ^ 2), ← Nat.mul_assoc]
      rw [hcomm, Nat.add_mul_mod_self_left]
    rw [hu, hmul, hv, hmul, huv]
  exact hlift _ _ hcoh

theorem cubic_odd_shift_v1 {w x : Nat} (hw : 3 ≤ w) (hodd : x % 2 = 1) :
    evalMod (w + 1) (.mul .var (.sub (.mul .var .var) (.const 1))) (x + 2 ^ (w - 1)) =
      (evalMod (w + 1) (.mul .var (.sub (.mul .var .var) (.const 1))) x + 2 ^ w) % 2 ^ (w + 1) := by
  have hx1 : 1 ≤ x := by omega
  have hxm1 : 1 ≤ x + 2 ^ (w - 1) := Nat.le_trans hx1 (Nat.le_add_right _ _)
  rw [evalMod_cubic_eq_nat (by omega) hxm1, evalMod_cubic_eq_nat (by omega) hx1]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  -- Algebraic identity: (x + m)*((x + m)^2 - 1) = x*(x^2 - 1) + m*(3*x^2 - 1) + 3*x*m^2 + m^3
  let m := 2 ^ (w - 1)
  have ht_even : ∃ k, (x / 2) * (x / 2 + 1) = 2 * k := by
    by_cases hpar : (x / 2) % 2 = 0
    · refine ⟨(x / 2) / 2 * (x / 2 + 1), ?_⟩
      have hdiv : x / 2 = 2 * ((x / 2) / 2) := by omega
      calc (x / 2) * (x / 2 + 1) = (2 * ((x / 2) / 2)) * (x / 2 + 1) := by rw [← hdiv]
        _ = 2 * (((x / 2) / 2) * (x / 2 + 1)) := Nat.mul_assoc _ _ _
    · refine ⟨(x / 2) * ((x / 2 + 1) / 2), ?_⟩
      have hdiv : x / 2 + 1 = 2 * ((x / 2 + 1) / 2) := by omega
      calc (x / 2) * (x / 2 + 1) = (x / 2) * (2 * ((x / 2 + 1) / 2)) := by rw [← hdiv]
        _ = 2 * ((x / 2) * ((x / 2 + 1) / 2)) := by rw [Nat.mul_left_comm]
  obtain ⟨k, hk⟩ := ht_even
  have hx_eq : x = 2 * (x / 2) + 1 := by omega
  have h3x2 : 3 * (x * x) - 1 = 2 + 24 * k := by
    have hsq : x * x = 4 * ((x / 2) * (x / 2 + 1)) + 1 := by
      calc x * x = (2 * (x / 2) + 1) * (2 * (x / 2) + 1) := by rw [← hx_eq]
        _ = 4 * ((x / 2) * (x / 2)) + 4 * (x / 2) + 1 := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]
            have : 2 * (x / 2) * (2 * (x / 2)) = 4 * ((x / 2) * (x / 2)) := by
              rw [Nat.mul_assoc 2, Nat.mul_left_comm (x / 2) 2, ← Nat.mul_assoc, ← Nat.mul_assoc]
            rw [this]; omega
        _ = 4 * ((x / 2) * (x / 2) + x / 2) + 1 := by rw [Nat.mul_add]
        _ = 4 * ((x / 2) * (x / 2 + 1)) + 1 := by rw [Nat.mul_add (x / 2), Nat.mul_one]
    rw [hsq, hk]
    omega
  have hm2 : 2 * m = 2 ^ w := by
    dsimp only [m]
    have : w = (w - 1) + 1 := by omega
    calc 2 * 2 ^ (w - 1) = 2 ^ (w - 1) * 2 := Nat.mul_comm _ _
      _ = 2 ^ ((w - 1) + 1) := (Nat.pow_succ 2 (w - 1)).symm
      _ = 2 ^ w := by rw [← this]
  have h4m : 4 * m = 2 ^ (w + 1) := by
    rw [Nat.pow_succ, ← hm2]
    omega
  have hmsq_dvd : 2 ^ (w + 1) ∣ m * m := by
    dsimp only [m]
    rw [← Nat.pow_add]
    exact pow2_dvd_pow2 (by omega)
  obtain ⟨q, hq⟩ := hmsq_dvd
  have hexp : (x + m) * ((x + m) * (x + m) - 1) =
              (x * (x * x - 1) + 2 ^ w) + 2 ^ (w + 1) * (6 * k + q * (3 * x + m)) := by
    have hxx1 : 1 ≤ x * x := Nat.mul_pos hx1 hx1
    have hxm2 : (x + m) * (x + m) - 1 = (x * x - 1) + 2 * x * m + m * m := by
      have h1 : (x + m) * (x + m) = x * x + 2 * x * m + m * m := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm m x]
        have : x * m + x * m = 2 * x * m := by rw [Nat.two_mul, Nat.add_mul]
        omega
      omega
    have hmul : (x + m) * ((x + m) * (x + m) - 1) =
                x * (x * x - 1) + m * (3 * (x * x) - 1) + (m * m) * (3 * x + m) := by
      rw [hxm2, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
      have ha1 : x * (2 * x * m) = m * (2 * (x * x)) := by
        rw [Nat.mul_comm (2 * x) m, Nat.mul_left_comm, Nat.mul_left_comm x 2]
      have ha2 : m * (x * x - 1) + m * (2 * (x * x)) = m * (3 * (x * x) - 1) := by
        rw [← Nat.mul_add]
        congr 1; omega
      have ha3 : x * (m * m) + m * (2 * x * m) = (m * m) * (3 * x) := by
        have h1 : m * (2 * x * m) = (m * m) * (2 * x) := by
          rw [Nat.mul_comm (2 * x) m, ← Nat.mul_assoc, Nat.mul_comm (m * m)]
        rw [h1, Nat.mul_comm x (m * m), ← Nat.mul_add]
        congr 1; omega
      have ha4 : (m * m) * (3 * x) + m * (m * m) = (m * m) * (3 * x + m) := by
        rw [Nat.mul_comm m (m * m), ← Nat.mul_add]
      rw [ha1]
      omega
    rw [hmul, h3x2, hq]
    have hm_term : m * (2 + 24 * k) = 2 ^ w + 2 ^ (w + 1) * (6 * k) := by
      rw [Nat.mul_add, Nat.mul_comm m 2, hm2, ← h4m]
      have : m * (24 * k) = 4 * m * (6 * k) := by
        have h24 : 24 * k = 4 * (6 * k) := by omega
        rw [h24, Nat.mul_left_comm, ← Nat.mul_assoc]
      rw [this]
    rw [hm_term, Nat.mul_add (2 ^ (w + 1)), Nat.mul_assoc (2 ^ (w + 1)) q]
    omega
  rw [hexp, Nat.add_mul_mod_self_left]

theorem fam2_odd_sens (H : MBAExpr) :
    HasOrderVSensitivity (fun w x => evalMod w (fam2 H) x) 1 1 3 1 := by
  refine ⟨by decide, ?_⟩
  intro w x hw hodd
  have hodd2 : x % 2 = 1 := by simpa using hodd
  have hshift_mod : evalMod (w + 1) (fam2 H) (x + 2 ^ (w - 1)) =
                    (evalMod (w + 1) (fam2 H) x + 2 ^ w) % 2 ^ (w + 1) := by
    change (evalMod (w + 1) (.mul .var (.sub (.mul .var .var) (.const 1))) (x + 2 ^ (w - 1)) +
            evalMod (w + 1) (.shl H 2) (x + 2 ^ (w - 1))) % 2 ^ (w + 1) =
           ((evalMod (w + 1) (.mul .var (.sub (.mul .var .var) (.const 1))) x +
             evalMod (w + 1) (.shl H 2) x) % 2 ^ (w + 1) + 2 ^ w) % 2 ^ (w + 1)
    rw [cubic_odd_shift_v1 hw hodd2, evalMod_shl2_shift_v1 H hw]
    have := add_deriv_rule (w := w)
      (a := evalMod (w + 1) (.mul .var (.sub (.mul .var .var) (.const 1))) x)
      (b := evalMod (w + 1) (.shl H 2) x) true false
    simpa only [↓reduceIte, Bool.false_eq_true, Nat.add_zero, Bool.bne_false,
      Nat.mod_eq_of_lt (evalMod_lt (w + 1) (.shl H 2) x)] using this
  refine ⟨?_, ?_⟩
  · -- Mod 2^w invariance
    dsimp only
    have h1 := (evalMod_coherent (fam2 H)).2 w (w + 1) (x + 2 ^ (w - 1)) (x + 2 ^ (w - 1)) (Nat.le_succ w) rfl
    have h2 := (evalMod_coherent (fam2 H)).2 w (w + 1) x x (Nat.le_succ w) rfl
    dsimp only at h1 h2
    rw [← h1, hshift_mod, mod_pow2_mod (Nat.le_succ w), Nat.add_mod_right, h2]
  · -- Mod 2^(w+1) flip
    dsimp only
    rw [hshift_mod]
    have hlt := evalMod_lt (w + 1) (fam2 H) x
    have hpos := pow2_pos w
    have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ, Nat.mul_two]
    intro heq
    by_cases h1 : evalMod (w + 1) (fam2 H) x < 2 ^ w
    · rw [Nat.mod_eq_of_lt (by omega)] at heq; omega
    · have h2 : (evalMod (w + 1) (fam2 H) x + 2 ^ w) % 2 ^ (w + 1) =
                evalMod (w + 1) (fam2 H) x + 2 ^ w - 2 ^ (w + 1) := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [h2] at heq; omega

/-- **Main Theorem 2 (Universal 1-or-5 Non-Uniform Ramification Dichotomy):**
For EVERY mixed bitwise-arithmetic expression `H : MBAExpr` (mixing `+`, `-`, `*`, `^`, `&`, `|`, `~`, `<<`
arbitrarily!) and EVERY `w ≥ 3`:
`x * (x^2 - 1) + 4 * H(x) ≡ 0 (mod 2^w)` has:
- **EXACTLY `5` roots** (1 unramified even root `v=0` + 2 ramified odd core roots `v=1` with fibers of size 2)
  if `H(1)` is even (`evalMod 1 H 1 = 0`),
- **EXACTLY `1` root** (the unique even root `v=0`) if `H(1)` is odd (`evalMod 1 H 1 = 1`)! -/
theorem thm2_universal_cubic_mba_dichotomy (H : MBAExpr) {w : Nat} (hw : 3 ≤ w) :
    rootCount (fun w' x => evalMod w' (fam2 H) x) w =
      if evalMod 1 H 1 = 0 then 5 else 1 := by
  have hinv : rootCount (fun w' x => evalMod w' (fam2 H) x) w =
              rootCount (fun w' x => evalMod w' (fam2 H) x) 3 := by
    apply rootCount_partition_invariant (s := 1) (evalMod_coherent (fam2 H)) (by decide) _ hw
    intro c hc
    have hc_cases : c = 0 ∨ c = 1 := by omega
    rcases hc_cases with rfl | rfl
    · right; exact ⟨0, fam2_even_sens H⟩
    · right; exact ⟨1, fam2_odd_sens H⟩
  rw [hinv]
  -- Evaluate rootCount at w0 = 3 purely via H(0) % 2 and H(1) % 2 (by width-coherence of H!)
  have hH : ∀ x, (evalMod 3 H x * 4) % 8 = 4 * evalMod 1 H (x % 2) := by
    intro x
    have h1 := (evalMod_coherent H).2 1 3 x (x % 2) (by decide) (by simp)
    dsimp only at h1
    have hlt1 : evalMod 1 H (x % 2) < 2 := evalMod_lt 1 H (x % 2)
    have hsplit : evalMod 3 H x = 2 * (evalMod 3 H x / 2) + evalMod 1 H (x % 2) := by
      rw [← h1, Nat.div_add_mod]
    have hmul : evalMod 3 H x * 4 = 8 * (evalMod 3 H x / 2) + 4 * evalMod 1 H (x % 2) := by
      omega
    rw [hmul, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have h0_lt : evalMod 1 H 0 < 2 := evalMod_lt 1 H 0
  have h1_lt : evalMod 1 H 1 < 2 := evalMod_lt 1 H 1
  have h0_c : evalMod 1 H 0 = 0 ∨ evalMod 1 H 0 = 1 := by omega
  have h1_c : evalMod 1 H 1 = 0 ∨ evalMod 1 H 1 = 1 := by omega
  have heval3 : ∀ x, evalMod 3 (fam2 H) x =
      (evalMod 3 (.mul .var (.sub (.mul .var .var) (.const 1))) x + 4 * evalMod 1 H (x % 2)) % 8 := by
    intro x
    simp only [fam2, evalMod]
    rw [Nat.add_mod, hH x, ← Nat.add_mod]
  unfold rootCount
  change countBelow (fun x => decide (evalMod 3 (fam2 H) x = 0)) 8 = _
  simp only [countBelow, heval3]
  rcases h0_c with h0 | h0 <;> rcases h1_c with h1 | h1 <;>
    simp [evalMod, h0, h1]

-- Non-vacuity witnesses for Theorem 2 (both 5-root and 1-root branches with full `+ * ^ &`)
theorem witness2_five_roots {w : Nat} (hw : 3 ≤ w) :
    rootCount (fun w' x => evalMod w' (fam2 H_five) x) w = 5 := by
  simpa [H_five, evalMod] using thm2_universal_cubic_mba_dichotomy H_five hw

theorem witness2_one_root {w : Nat} (hw : 3 ≤ w) :
    rootCount (fun w' x => evalMod w' (fam2 H_one) x) w = 1 := by
  simpa [H_one, evalMod] using thm2_universal_cubic_mba_dichotomy H_one hw

-- Sharpness Counterexample 2: Replacing `4 * H` by `2 * H` with `H = x & (x + 1)` shatters `{1, 5}`
-- hitting 7 roots at w = 4 and 11 roots at w = 5!
theorem sharpness2_coeff_two :
    rootCount (fun w x => evalMod w fam2SharpCoeff2 x) 4 = 7 ∧
    rootCount (fun w x => evalMod w fam2SharpCoeff2 x) 5 = 11 := by decide


/-! ### Theorem 3: 3-Parameter Quadratic Lifting Tower via Bitwise-AND Idempotence Linearization -/

/-- **Main Theorem 3a (Exact Unique Root Count `∀ w ≥ 1`):**
For ALL odd `a` and ALL `b c : Nat`, `fam3 a b c (x) ≡ 0 (mod 2^w)` has EXACTLY `1` root
for ALL `w ≥ 1`, and that unique root is always even. -/
theorem thm3_unique_rootCount {a : Nat} (ha : a % 2 = 1) (b c : Nat) {w : Nat} (hw : 1 ≤ w) :
    rootCount (fun w' x => evalMod w' (fam3 a b c) x) w = 1 := by
  have hinv : rootCount (fun w' x => evalMod w' (fam3 a b c) x) w =
              rootCount (fun w' x => evalMod w' (fam3 a b c) x) 1 := by
    apply rootCount_partition_invariant (evalMod_coherent (fam3 a b c)) (Nat.le_refl 1) _ hw
    intro r hr
    have hr_c : r = 0 ∨ r = 1 := by omega
    rcases hr_c with rfl | rfl
    · right
      refine ⟨0, hasExactDeriv0_to_order0 (Nat.le_refl 1) (symDeriv0_sound ?_)⟩
      simp [fam3, symDeriv0, isBoundedConst, isCarryFreeSelfPair, evalMod]
    · left
      simp [classRootCount, countBelow, fam3, evalMod, ha]
  rw [hinv]
  simp [rootCount, countBelow, fam3, evalMod, ha]

theorem fam3_blockJet_ok {a b c w0 w x : Nat}
    (hw0 : 1 ≤ w0) (hw : w0 ≤ w) (hc : c < 2 ^ w0) (heven : x % 2 = 0) :
    ∃ J, evalBlockJet w (fam3 a b c) x = some J ∧ J.a % 2 = 1 := by
  have hw1 : 1 ≤ w := Nat.le_trans hw0 hw
  have hM2 : 2 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw1; omega
  have hM_even : 2 ∣ 2 ^ w := by
    have h1 : 2 ^ 1 ∣ 2 ^ w := pow2_dvd_pow2 hw1; simpa using h1
  have hc_lt : c < 2 ^ w := Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) hw)
  have h1_mod : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by omega)
  have h1_div : 1 / 2 ^ w = 0 := Nat.div_eq_of_lt (by omega)
  have hc_div : c / 2 ^ w = 0 := Nat.div_eq_of_lt hc_lt
  have hx_even : (x % 2 ^ w) % 2 = 0 := by
    rw [mod_pow2_mod hw1]; exact heven
  have hM_sub_odd : (2 ^ w - 1) % 2 = 1 := by
    obtain ⟨m, hm⟩ := hM_even; omega
  have hx_lt_pred : x % 2 ^ w + 1 < 2 ^ w := by
    have hlt := Nat.mod_lt x (pow2_pos w)
    have hne : x % 2 ^ w ≠ 2 ^ w - 1 := by omega
    omega
  have hx1_div : (x % 2 ^ w + 1) / 2 ^ w = 0 := Nat.div_eq_of_lt hx_lt_pred
  -- Evaluate evalBlockJet w (fam3 a b c) x step by step!
  have hjet_and : evalBlockJet w (.band .var (.add .var (.const 1))) x =
      some ⟨((x % 2 ^ w) &&& ((x % 2 ^ w + 1) % 2 ^ w)) % 2 ^ w, 0, 1⟩ := by
    simp only [evalBlockJet, h1_mod, h1_div, hx1_div, Nat.add_zero, Nat.zero_mod]
    have h10 : (1 : Nat) ≠ 0 := by decide
    simp [h10]
  have hjet_xor : evalBlockJet w (.bxor .var (.const c)) x =
      some ⟨((x % 2 ^ w) ^^^ (c % 2 ^ w)) % 2 ^ w, 0, 1⟩ := by
    simp only [evalBlockJet, h1_mod, hc_div, Nat.zero_mod]
    simp
  have hjet_sq : evalBlockJet w (.mul (.const a) (.mul .var .var)) x =
      some ⟨(a % 2 ^ w * (x % 2 ^ w * (x % 2 ^ w) % 2 ^ w)) % 2 ^ w,
            (a % 2 ^ w * (x % 2 ^ w * (x % 2 ^ w) % 2 ^ w) / 2 ^ w +
              a % 2 ^ w * (x % 2 ^ w * (x % 2 ^ w) / 2 ^ w % 2 ^ w) +
              x % 2 ^ w * (x % 2 ^ w) % 2 ^ w * (a / 2 ^ w % 2 ^ w)) % 2 ^ w,
            (a % 2 ^ w * ((x % 2 ^ w + x % 2 ^ w) % 2 ^ w)) % 2 ^ w⟩ := by
    simp [evalBlockJet, h1_mod]
  have hjet_add1 : ∃ J1,
      evalBlockJet w (.add (.mul (.const a) (.mul .var .var)) (.band .var (.add .var (.const 1)))) x = some J1 ∧
      J1.a = ((a % 2 ^ w * ((x % 2 ^ w + x % 2 ^ w) % 2 ^ w)) % 2 ^ w + 1) % 2 ^ w := by
    rw [evalBlockJet, hjet_sq, hjet_and]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨J1, hJ1, hJ1a⟩ := hjet_add1
  have hjet_shl : ∃ J2,
      evalBlockJet w (.shl (.bxor .var (.const c)) 1) x = some J2 ∧
      J2.a = (1 * 2 ^ 1) % 2 ^ w := by
    rw [evalBlockJet, hjet_xor]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨J2, hJ2, hJ2a⟩ := hjet_shl
  have hjet_add2 : ∃ J3,
      evalBlockJet w (.add (.add (.mul (.const a) (.mul .var .var)) (.band .var (.add .var (.const 1))))
                           (.shl (.bxor .var (.const c)) 1)) x = some J3 ∧
      J3.a = (J1.a + J2.a) % 2 ^ w := by
    rw [evalBlockJet, hJ1, hJ2]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨J3, hJ3, hJ3a⟩ := hjet_add2
  have hjet_const : evalBlockJet w (.const (2 * b)) x =
      some ⟨(2 * b) % 2 ^ w, (2 * b / 2 ^ w) % 2 ^ w, 0⟩ := by rfl
  have hjet_all : ∃ J, evalBlockJet w (fam3 a b c) x = some J ∧
      J.a = (J3.a + (2 ^ w - 0)) % 2 ^ w := by
    unfold fam3
    rw [evalBlockJet, hJ3, hjet_const]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨J, hJ, hJa⟩ := hjet_all
  refine ⟨J, hJ, ?_⟩
  · -- Slope is odd!
    obtain ⟨m, hm⟩ := hM_even
    have hmod_even : ∀ u, (u % 2 ^ w) % 2 = u % 2 := fun u => mod_pow2_mod hw1 u
    have h2x_even : ((a % 2 ^ w) * ((x % 2 ^ w + x % 2 ^ w) % 2 ^ w)) % 2 = 0 := by
      rw [Nat.mul_mod, hmod_even (x % 2 ^ w + x % 2 ^ w)]
      have : (x % 2 ^ w + x % 2 ^ w) % 2 = 0 := by omega
      rw [this, Nat.mul_zero, Nat.zero_mod]
    have hJ1_odd : J1.a % 2 = 1 := by
      rw [hJ1a, hmod_even, Nat.add_mod, hmod_even, h2x_even]
    have hJ2_even : J2.a % 2 = 0 := by
      rw [hJ2a, hmod_even]
    have hJ3_odd : J3.a % 2 = 1 := by
      rw [hJ3a, hmod_even, Nat.add_mod, hJ1_odd, hJ2_even]
    rw [hJa, hmod_even, Nat.add_mod, hJ3_odd]
    have hM0 : (2 ^ w - 0) % 2 = 0 := by omega
    rw [hM0]

/-- **Main Theorem 3b (Infinite Quadratic Doubling Tower via Bitwise-AND Idempotence Linearization):**
For ALL odd `a`, ALL `b c : Nat`, ANY `w0 ≥ 1` with `c < 2^w0`, and the unique base root `x0` at `w0`:
`mbaQuadLift (fam3 a b c) w0 x0 k` constructs the EXACT root modulo `2^(w0 * 2^k)` in `k`
quadratic doubling steps for ALL `k : Nat`! -/
theorem thm3_quad_idempotence_tower {a : Nat} (ha : a % 2 = 1) (b c w0 x0 : Nat)
    (hw0 : 1 ≤ w0) (hc : c < 2 ^ w0) (hroot0 : evalMod w0 (fam3 a b c) (x0 % 2 ^ w0) = 0) :
    ∀ k : Nat,
      let wk := w0 * 2 ^ k
      let xk := mbaQuadLift (fam3 a b c) w0 x0 k
      xk < 2 ^ wk ∧ xk % 2 = 0 ∧ evalMod wk (fam3 a b c) xk = 0 ∧
      mbaQuadLift (fam3 a b c) w0 x0 (k + 1) % 2 ^ wk = xk := by
  have heven0 : (x0 % 2 ^ w0) % 2 = 0 := by
    have h1 := (evalMod_coherent (fam3 a b c)).2 1 w0 (x0 % 2 ^ w0) (x0 % 2 ^ w0) hw0 rfl
    dsimp only at h1
    rw [hroot0, Nat.zero_mod] at h1
    have hpar : (x0 % 2 ^ w0) % 2 = 0 ∨ (x0 % 2 ^ w0) % 2 = 1 := by omega
    rcases hpar with h0 | h1p
    · exact h0
    · exfalso
      have hev1 : evalMod 1 (fam3 a b c) (x0 % 2 ^ w0) = 1 := by
        simp [fam3, evalMod, h1p, ha]
      rw [hev1] at h1
      omega
  exact mbaQuadLift_sound (Inv := fun _ x => x % 2 = 0) hw0 heven0 hroot0
    (fun w x y hw hx hy => by
      have hw1 : 1 ≤ w := Nat.le_trans hw0 hw
      rw [← mod_pow2_mod hw1 y, hy, mod_pow2_mod hw1 x, hx])
    (fun w x hw hx => fam3_blockJet_ok hw0 hw hc hx)

-- Concrete Non-Vacuity Witness for Theorem 3 (genuinely non-trivial root: 8 → 24 → 49944 mod 2^16!)
theorem witness3_quad_lift_concrete :
    evalMod 4 (fam3 3 11 7) 8 = 0 ∧
    mbaQuadLift (fam3 3 11 7) 4 8 1 = 24 ∧
    evalMod 8 (fam3 3 11 7) 24 = 0 ∧
    mbaQuadLift (fam3 3 11 7) 4 8 2 = 49944 ∧
    evalMod 16 (fam3 3 11 7) 49944 = 0 := by decide

-- Sharpness Counterexample 3: Below threshold `c < 2^w0` (`c = 7 ≥ 2^2 = 4`), `evalBlockJet` fails!
theorem sharpness3_below_mask_threshold :
    evalBlockJet 2 (fam3 3 11 7) 0 = none := by decide


/-! ### Theorem 4: Infinite Separation Theorem (Bit-by-Bit Liftable ⇏ Affine Block-Jet Liftable) -/

/-- **Main Theorem 4a (`sepExpr` IS Universally Bit-by-Bit Hensel Liftable `∀ w ≥ 1`):**
Proved in one line via finite-certificate reflection `rootCount_of_checkOrder0Cert` at `w0 = 1`! -/
theorem thm4a_sepExpr_bit_liftable {w : Nat} (hw : 1 ≤ w) :
    rootCount (fun w' x => evalMod w' sepExpr x) w = 2 := by
  have hcert : checkOrder0Cert sepExpr 1 1 = true := by decide
  have hinv := rootCount_of_checkOrder0Cert hcert hw
  have hbase : rootCount (fun w' x => evalMod w' sepExpr x) 1 = 2 := by decide
  exact hinv.trans hbase

/-- **Main Theorem 4b (`sepExpr` Has NO Affine `w → 2*w` Block-Jet for ANY `w ≥ 3` and ANY `x`):**
Proves a strict infinite separation between 1-Lipschitz bit-by-bit MBA Hensel lifting and
quadratic affine block-jet lifting! -/
theorem thm4b_sepExpr_no_affine_blockJet {w : Nat} (hw : 3 ≤ w) (x : Nat) :
    ¬ ∃ J : BlockJet, IsAffineBlockJet (fun w' y => evalMod w' sepExpr y) w x J := by
  rintro ⟨J, hr, hq, ha, hspec⟩
  dsimp only at hspec
  have hM : 0 < 2 ^ w := pow2_pos w
  have hM8 : 8 ≤ 2 ^ w := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw; exact this
  have h8dvd : 8 ∣ 2 ^ w := by
    have : 2 ^ 3 ∣ 2 ^ w := pow2_dvd_pow2 hw; exact this
  let r := x % 2 ^ w
  have hr_lt : r < 2 ^ w := Nat.mod_lt x hM
  let r2 := (2 * r + 1) % 2 ^ w
  let c0 := (2 * r + 1) / 2 ^ w
  have hr2_lt : r2 < 2 ^ w := Nat.mod_lt _ hM
  have hc0_lt : c0 < 2 := by
    have : 2 * r + 1 < 2 ^ w * 2 := by omega
    exact Nat.div_lt_of_lt_mul this
  -- For any Δ < 4, compute (evalMod (2*w) sepExpr (r + 2^w * Δ) + 1) % 2^(2*w) in two ways!
  have hEq_mod8 : ∀ Δ < 4,
      ((r * r + (r ^^^ r2)) / 2 ^ w + 2 * r * Δ + (Δ ^^^ (2 * Δ + c0))) % 8 =
      ((J.r + 1) / 2 ^ w + J.q + J.a * Δ) % 8 := by
    intro Δ hΔ
    have hΔw : Δ < 2 ^ w := by omega
    have h2Δc : 2 * Δ + c0 < 2 ^ w := by omega
    have hspecΔ := hspec Δ hΔw
    -- Step 1: Add 1 to evalMod (2*w) sepExpr y mod 2^(2*w)
    have h1lt : 1 < 2 ^ (2 * w) := by
      rw [pow2_two_mul]
      have : 8 * 8 ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul hM8 hM8
      omega
    have hplus1_lhs : (evalMod (2 * w) sepExpr (r + 2 ^ w * Δ) + 1) % 2 ^ (2 * w) =
                      ((r + 2 ^ w * Δ) * (r + 2 ^ w * Δ) +
                        ((r + 2 ^ w * Δ) ^^^ (2 * (r + 2 ^ w * Δ) + 1))) % 2 ^ (2 * w) := by
      simp only [sepExpr, evalMod, Nat.pow_one]
      rw [Nat.mod_eq_of_lt h1lt]
      rw [Nat.add_mod (_ % _), Nat.mod_mod, ← Nat.add_mod]
      have hsub1 : ∀ u, (u + (2 ^ (2 * w) - 1) + 1) % 2 ^ (2 * w) = u % 2 ^ (2 * w) := by
        intro u
        have : u + (2 ^ (2 * w) - 1) + 1 = u + 2 ^ (2 * w) := by omega
        rw [this, Nat.add_mod_right]
      rw [hsub1]
      have hlt_y : r + 2 ^ w * Δ < 2 ^ (2 * w) := block_lt hr_lt hΔw
      have hlt_2y1 : 2 * (r + 2 ^ w * Δ) + 1 < 2 ^ (2 * w) := by
        rw [pow2_two_mul]
        have hle : 2 ^ w * (2 * Δ + 2) ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left (2 ^ w) (by omega)
        have hrew : 2 * (r + 2 ^ w * Δ) + 1 = (2 * r + 1) + 2 ^ w * (2 * Δ) := by
          rw [Nat.mul_add, Nat.mul_left_comm]; omega
        rw [Nat.mul_add] at hle; omega
      rw [Nat.mod_eq_of_lt hlt_y]
      have hmul2 : ((r + 2 ^ w * Δ) * 2 % 2 ^ (2 * w) + 1) % 2 ^ (2 * w) = 2 * (r + 2 ^ w * Δ) + 1 := by
        rw [Nat.mul_comm _ 2, Nat.mod_eq_of_lt (by omega : 2 * (r + 2 ^ w * Δ) < 2 ^ (2 * w)),
            Nat.mod_eq_of_lt hlt_2y1]
      rw [hmul2]
      have hxor_lt : ((r + 2 ^ w * Δ) ^^^ (2 * (r + 2 ^ w * Δ) + 1)) < 2 ^ (2 * w) :=
        xor_lt_pow2 hlt_y hlt_2y1
      have hmod_add_l : ∀ u v m, (u % m + v) % m = (u + v) % m := fun u v m => by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [Nat.mod_eq_of_lt hxor_lt, hmod_add_l, Nat.mod_mod]
    -- Step 2: Compute RHS via hspecΔ
    have hplus1_rhs : (evalMod (2 * w) sepExpr (r + 2 ^ w * Δ) + 1) % 2 ^ (2 * w) =
                      (J.r + 1) % 2 ^ w + 2 ^ w * (((J.r + 1) / 2 ^ w + (J.q + J.a * Δ)) % 2 ^ w) := by
      rw [hspecΔ, pow2_two_mul]
      have hre : J.r + 2 ^ w * ((J.q + J.a * Δ) % 2 ^ w) + 1 =
                 (J.r + 1) + 2 ^ w * ((J.q + J.a * Δ) % 2 ^ w) := by omega
      rw [hre, mod_sq_block (2 ^ w) _ _ hM]
      congr 2
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    -- Step 3: Compute LHS in block form via xor_split_block
    have h2y1_split : 2 * (r + 2 ^ w * Δ) + 1 = r2 + 2 ^ w * (2 * Δ + c0) := by
      have hsplit : 2 * r + 1 = r2 + 2 ^ w * c0 := (Nat.mod_add_div (2 * r + 1) (2 ^ w)).symm
      rw [Nat.mul_add, Nat.add_assoc, Nat.add_comm (2 * (2 ^ w * Δ)) 1, ← Nat.add_assoc, hsplit]
      rw [Nat.mul_add]
      have : 2 * (2 ^ w * Δ) = 2 ^ w * (2 * Δ) := by rw [Nat.mul_left_comm]
      omega
    have hxor_split : (r + 2 ^ w * Δ) ^^^ (2 * (r + 2 ^ w * Δ) + 1) =
                      (r ^^^ r2) + 2 ^ w * (Δ ^^^ (2 * Δ + c0)) := by
      rw [h2y1_split]
      exact xor_split_block hr_lt hr2_lt
    have hsq_split : (r + 2 ^ w * Δ) * (r + 2 ^ w * Δ) =
                     (r * r + 2 ^ w * (2 * r * Δ)) + (2 ^ w * 2 ^ w) * (Δ * Δ) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have h1 : r * (2 ^ w * Δ) + 2 ^ w * Δ * r = 2 ^ w * (2 * r * Δ) := by
        have ha : r * (2 ^ w * Δ) = 2 ^ w * (r * Δ) := by rw [Nat.mul_left_comm]
        have hb : 2 ^ w * Δ * r = 2 ^ w * (r * Δ) := by rw [Nat.mul_assoc, Nat.mul_comm Δ r]
        rw [ha, hb, ← Nat.mul_add, ← Nat.two_mul, Nat.mul_assoc]
      have h2 : 2 ^ w * Δ * (2 ^ w * Δ) = 2 ^ w * 2 ^ w * (Δ * Δ) := by
        rw [Nat.mul_assoc, Nat.mul_left_comm Δ (2 ^ w), ← Nat.mul_assoc]
      rw [h2]; omega
    have hplus1_lhs2 : (evalMod (2 * w) sepExpr (r + 2 ^ w * Δ) + 1) % 2 ^ (2 * w) =
                       (r * r + (r ^^^ r2)) % 2 ^ w +
                       2 ^ w * (((r * r + (r ^^^ r2)) / 2 ^ w + 2 * r * Δ + (Δ ^^^ (2 * Δ + c0))) % 2 ^ w) := by
      rw [hplus1_lhs, hxor_split, hsq_split, pow2_two_mul]
      have hre : (r * r + 2 ^ w * (2 * r * Δ) + 2 ^ w * 2 ^ w * (Δ * Δ)) +
                 ((r ^^^ r2) + 2 ^ w * (Δ ^^^ (2 * Δ + c0))) =
                 ((r * r + (r ^^^ r2)) + 2 ^ w * (2 * r * Δ + (Δ ^^^ (2 * Δ + c0)))) +
                 (2 ^ w * 2 ^ w) * (Δ * Δ) := by
        rw [Nat.mul_add]; omega
      rw [hre, Nat.add_mul_mod_self_left, mod_sq_block (2 ^ w) _ _ hM]
      congr 2
      rw [Nat.add_assoc]
    -- Equate high words (divide both sides by 2^w)
    have hhi_eq : ((r * r + (r ^^^ r2)) / 2 ^ w + 2 * r * Δ + (Δ ^^^ (2 * Δ + c0))) % 2 ^ w =
                  ((J.r + 1) / 2 ^ w + J.q + J.a * Δ) % 2 ^ w := by
      have hboth := hplus1_lhs2.symm.trans hplus1_rhs
      have hdiv := congrArg (fun n => n / 2 ^ w) hboth
      rw [Nat.add_comm ((r * r + (r ^^^ r2)) % 2 ^ w), Nat.mul_add_div hM,
          Nat.div_eq_of_lt (Nat.mod_lt _ hM), Nat.add_zero] at hdiv
      rw [Nat.add_comm ((J.r + 1) % 2 ^ w), Nat.mul_add_div hM,
          Nat.div_eq_of_lt (Nat.mod_lt _ hM), Nat.add_zero] at hdiv
      simpa only [Nat.add_assoc] using hdiv
    -- Reduce modulo 8 using 8 ∣ 2^w
    have hmod8 := congrArg (fun n => n % 8) hhi_eq
    rwa [Nat.mod_mod_of_dvd _ h8dvd, Nat.mod_mod_of_dvd _ h8dvd] at hmod8
  -- Specialize hEq_mod8 to Δ = 0, 1, 2, 3 and close via second-difference contradiction mod 8!
  have h0 := hEq_mod8 0 (by decide)
  have h1 := hEq_mod8 1 (by decide)
  have h2 := hEq_mod8 2 (by decide)
  have h3 := hEq_mod8 3 (by decide)
  have hlin : ∀ (A B C D : Nat),
      ∀ u0 u1 u2 : Nat,
      (A + 0 * B + u0) % 8 = (C + 0 * D) % 8 →
      (A + 1 * B + u1) % 8 = (C + 1 * D) % 8 →
      (A + 2 * B + u2) % 8 = (C + 2 * D) % 8 →
      (u0 + u2) % 8 = (2 * u1) % 8 := by
    intro A B C D u0 u1 u2 e0 e1 e2
    omega
  have hlin1 : ∀ (A B C D : Nat),
      ∀ u1 u2 u3 : Nat,
      (A + 1 * B + u1) % 8 = (C + 1 * D) % 8 →
      (A + 2 * B + u2) % 8 = (C + 2 * D) % 8 →
      (A + 3 * B + u3) % 8 = (C + 3 * D) % 8 →
      (u1 + u3) % 8 = (2 * u2) % 8 := by
    intro A B C D u1 u2 u3 e1 e2 e3
    omega
  have hc0_cases : c0 = 0 ∨ c0 = 1 := by
    have haux : ∀ n : Nat, n < 2 → n = 0 ∨ n = 1 := fun n hn => by omega
    exact haux c0 hc0_lt
  rcases hc0_cases with hc0 | hc0
  · rw [hc0] at h1 h2 h3
    have g1 : (1 ^^^ (2 * 1 + 0)) = 3 := by decide
    have g2 : (2 ^^^ (2 * 2 + 0)) = 6 := by decide
    have g3 : (3 ^^^ (2 * 3 + 0)) = 5 := by decide
    rw [g1] at h1; rw [g2] at h2; rw [g3] at h3
    have hbad := hlin1 ((r * r + (r ^^^ r2)) / 2 ^ w) (2 * r) ((J.r + 1) / 2 ^ w + J.q) J.a 3 6 5
      (by simpa [Nat.mul_comm] using h1)
      (by simpa [Nat.mul_comm] using h2)
      (by simpa [Nat.mul_comm] using h3)
    omega
  · rw [hc0] at h0 h1 h2
    have g0 : (0 ^^^ (2 * 0 + 1)) = 1 := by decide
    have g1 : (1 ^^^ (2 * 1 + 1)) = 2 := by decide
    have g2 : (2 ^^^ (2 * 2 + 1)) = 7 := by decide
    rw [g0] at h0; rw [g1] at h1; rw [g2] at h2
    have hbad := hlin ((r * r + (r ^^^ r2)) / 2 ^ w) (2 * r) ((J.r + 1) / 2 ^ w + J.q) J.a 1 2 7
      (by simpa [Nat.mul_comm] using h0)
      (by simpa [Nat.mul_comm] using h1)
      (by simpa [Nat.mul_comm] using h2)
    omega

end MBAHensel
